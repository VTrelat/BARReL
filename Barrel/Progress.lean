import Lean.Widget.UserWidget
import Lean.Widget.Commands
import Lean.Server.Rpc.RequestHandling

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
    (importing : Bool) (elapsedMs : Nat) (summary : Json := .null) : BaseIO Unit := do
  let entry := Json.mkObj [
    ("machine", .str machine),
    ("total", toJson total),
    ("po", toJson po),
    ("nbPOs", toJson nbPOs),
    ("proven", toJson proven),
    ("sorried", toJson sorried),
    ("importing", toJson importing),
    ("errored", toJson false),
    ("elapsedMs", toJson elapsedMs),
    ("summary", summary)
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
        |>.setObjVal! "errored" (toJson false)
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
    | some idx => arr.set! idx ((arr[idx]!).setObjVal! "errored" (toJson true))
    | none => arr

@[server_rpc_method]
def get (_ : Json) : RequestM (RequestTask Json) :=
  RequestM.asTask do
    return Json.arr (← state.get)

-- `include_str` reads `widget/barrelMonitor.js` at *this file's* elaboration time. Lake's
-- incremental build traces content hashes, not mtimes, so `touch`ing this file is *not*
-- enough to force a rebuild after editing the JS — the hash of this file's own text is
-- unchanged, so Lake (correctly, by its own accounting) skips recompilation. Make a real
-- edit here (e.g. bump the version note below) after touching the JS, or `lake clean`.
-- widget version: 16
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
