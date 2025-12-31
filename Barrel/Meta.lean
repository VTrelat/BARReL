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

-----------
