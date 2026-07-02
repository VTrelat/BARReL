import Lean.Util.Trace
import POGReader.Extractor

open Lean

initialize registerTraceClass `barrel
initialize registerTraceClass `barrel.pog
initialize registerTraceClass `barrel.cache
initialize registerTraceClass `barrel.wd
initialize registerTraceClass `barrel.solve

initialize
  nameFromPath : EnvExtension (Lean.PersistentHashMap String System.FilePath)
    ← registerEnvExtension (pure .empty)
initialize
  cache : EnvExtension (Lean.PersistentHashMap System.FilePath (Array (Name × String × Expr)))
    ← registerEnvExtension (pure .empty)

register_option barrel.atelierb : String := {
  defValue := ""
  descr := "Path to the Atelier-B distribution"
}

register_option barrel.show_goal_names : Bool := {
  defValue := true
  descr := "Show the goal name on `next`"
}

register_option barrel.show_auto_solved : Bool := {
  defValue := false
  descr := "Show the number of goals that are automatically solved by `barrel_solve`"
}

register_option barrel.cache_dir : String := {
  defValue := ""
  descr := "Path to the cache directory for storing parsed POGs"
}

register_option barrel.progress : Bool := {
  defValue := true
  descr := "Show a live, self-updating progress card in the infoview for each `import` \
    (auto-solved / remaining counts, a progress bar, and the summary table once finished). \
    Set to false to suppress the panel and its reporting."
}

register_option barrel.summary : Bool := {
  defValue := false
  descr := "Log a summary table (solved/remaining counts, WD deduplication) as an info \
    message after an `import` finishes. The same table is always shown in the live progress \
    card; this option is for batch builds and logs."
}

-----------
