import Lean.Util.Trace
import POGReader.Extractor

open Lean

initialize registerTraceClass `barrel
initialize registerTraceClass `barrel.pog
initialize registerTraceClass `barrel.cache
initialize registerTraceClass `barrel.wf
initialize mchStore : IO.Ref (Lean.PersistentHashMap System.FilePath (UInt64 × System.FilePath)) ← IO.mkRef .empty
initialize pogStore : IO.Ref (Lean.PersistentHashMap System.FilePath UInt64) ← IO.mkRef .empty
initialize poStore : IO.Ref (Lean.PersistentHashMap UInt64 (Array B.POG.Goal)) ← IO.mkRef .empty

register_option barrel.atelierb : String := {
  defValue := ""
  descr := "Path to the Atelier-B distribution"
}

register_option barrel.show_goal_names : Bool := {
  defValue := true
  descr := "Show the goal name on `next`"
}

-----------

def getMchHash (path : System.FilePath) : IO (Option UInt64) := do
  return Prod.fst <$> (← mchStore.get).find? (← IO.FS.realPath path)

def getPogPath (path : System.FilePath) : IO (Option System.FilePath) := do
  return Prod.snd <$> (← mchStore.get).find? (← IO.FS.realPath path)

def getPogHash (path : System.FilePath) : IO (Option UInt64) := do
  return (← pogStore.get).find? (← IO.FS.realPath path)

def getGoals (pogHash : UInt64) : IO (Option (Array B.POG.Goal)) := do
  return (← poStore.get).find? pogHash

-----------

def registerFile (mchPath pogPath : System.FilePath) (mchHash pogHash : UInt64) (goals : Array B.POG.Goal) : IO PUnit := do
  mchStore.set <| (← mchStore.get).insert mchPath (mchHash, pogPath)
  pogStore.set <| (← pogStore.get).insert pogPath pogHash
  poStore.set <| (← poStore.get).insert pogHash goals
