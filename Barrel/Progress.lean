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

def report (machine : String) (po nbPOs subgoals solved leftover skipped : Nat)
    (current : String) (elapsedMs etaMs : Nat) (finished : Bool)
    (summary : Json := .null) : BaseIO Unit := do
  let entry := Json.mkObj [
    ("machine", .str machine),
    ("po", toJson po),
    ("nbPOs", toJson nbPOs),
    ("subgoals", toJson subgoals),
    ("solved", toJson solved),
    ("leftover", toJson leftover),
    ("skipped", toJson skipped),
    ("current", .str current),
    ("elapsedMs", toJson elapsedMs),
    ("etaMs", toJson etaMs),
    ("finished", toJson finished),
    ("summary", summary)
  ]
  state.modify fun arr =>
    match arr.findIdx? (λ j ↦ (j.getObjValAs? String "machine").toOption == some machine) with
    | some idx => arr.set! idx entry
    | none => (if arr.size ≥ 32 then arr.extract 1 arr.size else arr).push entry

@[server_rpc_method]
def get (_ : Json) : RequestM (RequestTask Json) :=
  RequestM.asTask do
    return Json.arr (← state.get)

-- `include_str` reads `widget/barrelMonitor.js` at *this file's* elaboration time. Lake's
-- incremental build traces content hashes, not mtimes, so `touch`ing this file is *not*
-- enough to force a rebuild after editing the JS — the hash of this file's own text is
-- unchanged, so Lake (correctly, by its own accounting) skips recompilation. Make a real
-- edit here (e.g. bump the version note below) after touching the JS, or `lake clean`.
-- widget version: 11
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
