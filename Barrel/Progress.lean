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
-/
def report (machine : String) (total po nbPOs proven sorried : Nat)
    (importing : Bool) (elapsedMs : Nat) (summary : Json := .null)
    (obligations : Array Json := #[]) : BaseIO Unit := do
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
    -- `true` while `prove_obligations_of` is replaying this card, so the widget can
    -- auto-expand the card under active work and re-collapse it when done.
    ("active", toJson false),
    ("elapsedMs", toJson elapsedMs),
    ("summary", summary),
    -- One entry per subgoal `{d, n, op, st, line, char}`: declName, short label, operation
    -- group, status (auto|sorry|hand|pending), and the source position of its `next` (once
    -- known) for click-to-jump. Populated in the final import report.
    ("obligations", Json.arr obligations)
  ]
  state.modify fun arr =>
    match findMachine? arr machine with
    | some idx => arr.set! idx entry
    | none => (if arr.size ≥ 32 then arr.extract 1 arr.size else arr).push entry

/--
  Update just the proof-progress counters of an existing card — used by
  `prove_obligations_of` to fill the bar in live as each leftover goal is proven (green) or
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
  Mark a machine's card as errored — its `prove_obligations_of` threw (a failing proof, or too
  few / too many `next`s). This is what turns the badge red; until it fires the badge stays
  gray, since the goal state may still change.
-/
def reportError (machine : String) : BaseIO Unit :=
  state.modify fun arr =>
    match findMachine? arr machine with
    | some idx => arr.set! idx (((arr[idx]!).setObjVal! "errored" (toJson true)).setObjVal! "active" (toJson false))
    | none => arr

/--
  Flip a single obligation cell in a machine's per-obligation map — used by
  `prove_obligations_of` to turn a `pending` leftover into `hand` (proved) or `sorry` as each
  `next` is replayed, and to record the source position (`line`/`char`, 0-indexed LSP coords)
  of that `next` for click-to-jump. Also marks the card `active`. No-op if the card, or an
  obligation with this `decl`, is absent.
-/
def reportObligation (machine decl st : String) (line char : Nat) : BaseIO Unit :=
  state.modify fun arr =>
    match findMachine? arr machine with
    | some idx =>
      let c := arr[idx]!
      let obs : Array Json := (c.getObjValAs? (Array Json) "obligations").toOption.getD #[]
      let obs := obs.map fun (o : Json) =>
        if (o.getObjValAs? String "d").toOption == some decl then
          o.setObjVal! "st" (.str st) |>.setObjVal! "line" (toJson line) |>.setObjVal! "char" (toJson char)
        else o
      arr.set! idx ((c.setObjVal! "obligations" (Json.arr obs)).setObjVal! "active" (toJson true))
    | none => arr

/-- Set a card's `active` flag (whether `prove_obligations_of` is currently replaying it). -/
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

@[server_rpc_method]
def get (_ : Json) : RequestM (RequestTask Json) := do
  let doc ← RequestM.readDoc
  RequestM.asTask do
    -- The machines still imported in the current document: the discharger records each in the
    -- `nameFromPath` env extension when its import finishes. Reading it from the latest
    -- finished snapshot lets us drop cards for imports the user has since removed or changed.
    let (snaps, _, _) ← doc.cmdSnaps.getFinishedPrefix
    let current : List String :=
      match snaps.getLast? with
      | some snap => (nameFromPath.getState snap.env).toList.map Prod.fst
      | none      => []
    let cards ← state.get
    -- Keep in-progress cards (not in `nameFromPath` yet) and done cards whose import still
    -- exists; drop done cards for imports that are gone.
    let visible := cards.filter fun c =>
      (c.getObjValAs? Bool "importing").toOption == some true ||
      (match (c.getObjValAs? String "machine").toOption with
       | some m => current.contains m
       | none   => true)
    return Json.arr visible

-- `include_str` reads `widget/barrelMonitor.js` at *this file's* elaboration time. Lake's
-- incremental build traces content hashes, not mtimes, so `touch`ing this file is *not*
-- enough to force a rebuild after editing the JS — the hash of this file's own text is
-- unchanged, so Lake (correctly, by its own accounting) skips recompilation. Make a real
-- edit here (e.g. bump the version note below) after touching the JS, or `lake clean`.
-- widget version: 29
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
