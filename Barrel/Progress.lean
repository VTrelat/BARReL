import Lean.Widget.UserWidget
import Lean.Widget.Commands
import Lean.Server.Rpc.RequestHandling
import Lean.Server.Requests
import Barrel.Meta

/-!
# Live import progress for the infoview

`import` commands can take minutes on industrial POGs, and nothing inside a single
command can update the infoview or send LSP notifications while it runs (messages are
only published when the command finishes, and fd 1 is the LSP transport). What *can*
happen concurrently is RPC: the file worker serves RPC requests against already-elaborated
snapshots on separate threads.

So the live view is a pull model: the discharger publishes its state into a global
`IO.Ref`, and a panel widget polls that state over RPC a few times per second, stacking one
self-updating card per import (with its summary table once finished).

The panel is registered **globally** (`show_panel_widgets [monitorWidget]`), so it is active
from a file's first line — *before* any `import` runs. That is the crux of liveness: the
render anchor is already committed when a (long) `import` starts, and the widget polls the
`IO.Ref` on its own timer, so cards fill in live as each `import` reports into it. (Anchoring
the widget *inside* the import — an info leaf, or a macro-split — does not work: a command's
info tree is only reported once it finishes, so the card would appear post-hoc.) Because the
infoview only shows a position's widgets once that position is elaborated, park the cursor on
an already-elaborated line (the file header works) to watch imports below fill in.

The widget renders nothing until an import reports, so an idle panel is invisible. Set
`barrel.progress` to `false` to suppress the reporting (and thus the panel).
-/

open Lean Server Widget

namespace Barrel.Progress

/--
  One record per imported machine (keyed by machine name, so re-elaborations update their
  card in place instead of piling up), polled by the monitor infoview widget.
-/
initialize state : IO.Ref (Array Json) ← IO.mkRef #[]

private def findMachine? (arr : Array Json) (machine : String) : Option Nat :=
  arr.findIdx? (λ j ↦ (j.getObjValAs? String "machine").toOption == some machine)

/--
  Publish an import's card. `total` is the subgoal count, `proven`/`sorried` the green/yellow
  parts of the proof bar (auto-discharge results during the import phase). While `importing`
  the card shows a blue bar filling by `po`/`nbPOs`; once `importing = false` the bar switches
  to the `proven` / `sorried` / missing breakdown, which `reportProof` keeps updating.
  WD counters distinguish allocated goals, conditions proved by earlier imports, and local
  cache hits. Reused conditions are not added to the obligation map or its proof counts.
-/
def report (machine : String) (total po nbPOs proven sorried : Nat)
    (importing : Bool) (elapsedMs : Nat) (summary : Json := .null)
    (obligations : Array Json := #[]) (wdUnique wdReused wdAvoided : Nat := 0)
    (wdReuses : Array Json := #[]) : BaseIO Unit := do
  let entry := Json.mkObj [
    ("machine", .str machine),
    ("total", toJson total),
    ("po", toJson po),
    ("nbPOs", toJson nbPOs),
    ("proven", toJson proven),
    -- Green baseline captured at import: `proven` is auto-only during the import phase, so
    -- `auto = proven` here; the replay bumps `proven` past `auto` and the gap is the
    -- by-hand (teal) part. Lets the card split auto-solved from user-proved.
    ("auto", toJson proven),
    ("sorried", toJson sorried),
    ("importing", toJson importing),
    ("errored", toJson false),
    -- `true` while an obligation command is elaborating for this card, so the widget can
    -- auto-expand the card under active work and re-collapse it when done.
    ("active", toJson false),
    ("elapsedMs", toJson elapsedMs),
    ("summary", summary),
    ("wdUnique", toJson wdUnique),
    ("wdReused", toJson wdReused),
    ("wdAvoided", toJson wdAvoided),
    -- One entry per reused condition: `{condition, theorem}`. The condition names
    -- its local adapter theorem; theorem is the earlier published fact it applies.
    ("wdReuses", Json.arr wdReuses),
    -- One entry per subgoal `{d, n, op, st, line, char}`: declName, short label, operation
    -- group, status (auto|sorry|hand|pending), and the source position of its proof command (once
    -- known) for click-to-jump. Populated in the final import report.
    ("obligations", Json.arr obligations)
  ]
  state.modify fun arr =>
    match findMachine? arr machine with
    | some idx => arr.set! idx entry
    | none => (if arr.size ≥ 32 then arr.extract 1 arr.size else arr).push entry

/--
  Update just the proof-progress counters of an existing card — used by
  individual obligation commands to fill the bar as each leftover goal is proven (green) or
  sorried (yellow). Also clears the `errored` flag: while proofs are still being replayed the
  goal state may yet change. No-op if the machine has no card yet.
-/
def reportProof (machine : String) (proven sorried : Nat) : BaseIO Unit :=
  state.modify fun arr =>
    match findMachine? arr machine with
    | some idx =>
      let c := (arr[idx]!).setObjVal! "proven" (toJson proven) |>.setObjVal! "sorried" (toJson sorried)
        |>.setObjVal! "errored" (toJson false) |>.setObjVal! "active" (toJson true)
      arr.set! idx c
    | none => arr

/--
  Mark a machine's card as errored after a failing obligation command or `qed`. This turns
  the badge red; until it fires the badge stays gray, since the goal state may still change.
-/
def reportError (machine : String) : BaseIO Unit :=
  state.modify fun arr =>
    match findMachine? arr machine with
    | some idx => arr.set! idx (((arr[idx]!).setObjVal! "errored" (toJson true)).setObjVal! "active" (toJson false))
    | none => arr

/--
  Flip a single obligation cell in a machine's per-obligation map — used by
  an obligation command to turn a `pending` leftover into `hand` (proved) or `sorry` as its
  proof is elaborated, and to record the source position (`line`/`char`, 0-indexed LSP coords)
  of that command for click-to-jump. Also marks the card `active`. No-op if the card, or an
  obligation with this `decl`, is absent.
-/
def reportObligation (machine decl st : String) (line char : Nat)
    (index? : Option Nat := none) : BaseIO Unit :=
  state.modify fun arr =>
    match findMachine? arr machine with
    | some idx =>
      let c := arr[idx]!
      let obs : Array Json := (c.getObjValAs? (Array Json) "obligations").toOption.getD #[]
      let update := fun (o : Json) =>
        o.setObjVal! "st" (.str st) |>.setObjVal! "line" (toJson line) |>.setObjVal! "char" (toJson char)
      -- Import records the cell's original position; the context itself is ordered WD-first.
      let index? := index?.filter fun i =>
        (obs[i]?.bind fun o => (o.getObjValAs? String "d").toOption) == some decl
      let index? := index?.orElse fun _ =>
        obs.findIdx? fun o => (o.getObjValAs? String "d").toOption == some decl
      let obs := match index? with
        | some i => obs.modify i update
        | none => obs
      arr.set! idx ((c.setObjVal! "obligations" (Json.arr obs)).setObjVal! "active" (toJson true))
    | none => arr

/-- Set a card's `active` flag (whether an obligation command is currently elaborating). -/
def reportActive (machine : String) (active : Bool) : BaseIO Unit :=
  state.modify fun arr =>
    match findMachine? arr machine with
    | some idx => arr.set! idx ((arr[idx]!).setObjVal! "active" (toJson active))
    | none => arr

/--
  Drop any card still marked `importing` — a stale in-progress import left over from a previous
  elaboration (e.g. the user changed the imported file mid-import). Safe to call at each
  import's start: within one pass imports run sequentially, so every *current* earlier import
  has already finished (`importing = false`) and only stale ones are still `importing = true`.
-/
def dropImporting : BaseIO Unit :=
  state.modify (·.filter fun j ↦ (j.getObjValAs? Bool "importing").toOption != some true)

/-- Find the context using its rendered name, including namespace and identifier escaping. -/
private def findContext? (env : Environment) (machine : String) : Option ImportContext :=
  ((obligationContexts.getState env).contexts.toList.find? fun (name, _) =>
    name.toString == machine).map Prod.snd

/--
  Reconcile a settled card with the import context in the latest command snapshot. Proofs
  remain private until `qed`, so checking global declarations would incorrectly mark every
  local proof as pending. The stored proof and position also restore the right status when
  an obligation command is removed or changed while earlier commands remain cached.
  Active/importing cards retain their live reports until the command finishes.
-/
def reconcileCard (env : Environment) (c : Json) : Json := Id.run do
  let importing := (c.getObjValAs? Bool "importing").toOption.getD false
  let active := (c.getObjValAs? Bool "active").toOption.getD false
  if importing || active then return c
  let machine := (c.getObjValAs? String "machine").toOption.getD ""
  let some ctx := findContext? env machine | return c
  let obs : Array Json := (c.getObjValAs? (Array Json) "obligations").toOption.getD #[]
  let obs := obs.map fun (o : Json) => Id.run do
    let d := (o.getObjValAs? String "d").toOption.getD ""
    let some i := ctx.bookkeeping.byDisplayName[d]? | return o
    let some ob := ctx.obligations[i]? | return o
    let status := match ob.proof? with
      | none => "pending"
      | some proof => if proof.hasSorry then "sorry" else if ob.auto then "auto" else "hand"
    let (line, char) := match ob.position? with
      | some (line, char) => (toJson line, toJson char)
      | none => (Json.null, Json.null)
    return o.setObjVal! "st" (.str status)
      |>.setObjVal! "line" line |>.setObjVal! "char" char
  return c.setObjVal! "obligations" (Json.arr obs)
    |>.setObjVal! "auto" (toJson ctx.bookkeeping.autoProven)
    |>.setObjVal! "proven" (toJson ctx.bookkeeping.proven)
    |>.setObjVal! "sorried" (toJson ctx.bookkeeping.sorried)
    |>.setObjVal! "finalized" (toJson ctx.finalized)

@[server_rpc_method]
def get (_ : Json) : RequestM (RequestTask Json) := do
  let doc ← RequestM.readDoc
  RequestM.asTask do
    -- Read the current import contexts from the latest finished command snapshot, dropping
    -- cards for imports that have since been removed or renamed.
    let (snaps, _, _) ← doc.cmdSnaps.getFinishedPrefix
    let lastSnap := snaps.getLast?
    let current : List String :=
      match lastSnap with
      | some snap => (obligationContexts.getState snap.env).contexts.toList.map
          (fun (name, _) => name.toString)
      | none      => []
    let cards ← state.get
    -- Keep in-progress cards (not in `obligationContexts` yet) and done cards whose import still
    -- exists; drop done cards for imports that are gone.
    let visible := cards.filter fun c =>
      (c.getObjValAs? Bool "importing").toOption == some true ||
      (match (c.getObjValAs? String "machine").toOption with
       | some m => current.contains m
       | none   => true)
    -- Self-heal settled cards whose leftovers had their proofs removed (see `reconcileCard`).
    let visible := match lastSnap with
      | some snap => visible.map (reconcileCard snap.env)
      | none      => visible
    return Json.arr visible

/--
  A proof scaffold containing only pending obligations, each selected by its import-relative name so
  inserting it after existing proofs cannot shift their goal selection. Finish with `qed`;
  an already finalized context has no scaffold. `sorry` is an editable placeholder.
-/
def skeletonText (ctx : ImportContext) : String := Id.run do
  if ctx.finalized then return ""
  let mut lines := #[]
  for ob in ctx.obligations do
    if ob.proof?.isNone then
      let reason := ob.reason.replace "\n" " "
      lines := lines.push s!"-- {reason}"
      let name := ob.name.replacePrefix ctx.name .anonymous
      lines := lines.push s!"obligation {name} of {ctx.name} by"
      lines := lines.push "  sorry"
      lines := lines.push ""
  lines := lines.push s!"qed {ctx.name}"
  return "\n".intercalate lines.toList

/-- Return a proof scaffold and a deterministic end-of-file insertion point. -/
@[server_rpc_method]
def skeleton (params : Json) : RequestM (RequestTask Json) := do
  let doc ← RequestM.readDoc
  RequestM.asTask do
    let machine := (params.getObjValAs? String "machine").toOption.getD ""
    let (snaps, _, _) ← doc.cmdSnaps.getFinishedPrefix
    let text : String :=
      match snaps.getLast? with
      | none => ""
      | some snap => (findContext? snap.env machine).map skeletonText |>.getD ""
    -- Deterministic insertion point: end of file (0-indexed LSP coords).
    let fm := doc.meta.text
    let eof := fm.toPosition ⟨fm.source.utf8ByteSize⟩
    return Json.mkObj [
      ("text", .str text),
      ("line", toJson (eof.line - 1)),
      ("char", toJson eof.column)]

-- `include_str` reads `widget/barrelMonitor.js` at *this file's* elaboration time. Lake's
-- incremental build traces content hashes, not mtimes, so `touch`ing this file is *not*
-- enough to force a rebuild after editing the JS — the hash of this file's own text is
-- unchanged, so Lake (correctly, by its own accounting) skips recompilation. Make a real
-- edit here (e.g. bump the version note below) after touching the JS, or `lake clean`.
-- widget version: 33
@[widget_module]
def monitorWidget : Widget.Module where
  javascript := include_str ".." / "widget" / "barrelMonitor.js"

/-
  Register the monitor as a *global* panel widget: it becomes active as soon as a file does
  `import Barrel`, i.e. before any B `import` runs, which is what lets even the first import
  be watched live (the render anchor is already committed). The widget renders nothing unless
  the cursor is on a line with a reported card, so it is invisible in files that aren't
  running B imports (aside from a brief one-time module load).
-/
show_panel_widgets [monitorWidget]

end Barrel.Progress
