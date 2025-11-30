import Lean.Util.Trace
import POGReader.Extractor

open Lean

initialize registerTraceClass `barrel.pog
initialize registerTraceClass `barrel.checkpoints
initialize mchStore : IO.Ref (Std.HashMap System.FilePath (UInt64 × System.FilePath)) ← IO.mkRef ∅
initialize pogStore : IO.Ref (Std.HashMap System.FilePath UInt64) ← IO.mkRef ∅
initialize poStore : IO.Ref (Std.HashMap UInt64 (Array (String × Lean.Expr))) ← IO.mkRef ∅

register_option barrel.atelierb : String := {
  defValue := ""
  descr := "Path to the Atelier-B distribution"
}

-----------

def getMchHash (path : System.FilePath) : IO (Option UInt64) := do
  return Prod.fst <$> (← mchStore.get).get? (← IO.FS.realPath path)

def getPogPath (path : System.FilePath) : IO (Option System.FilePath) := do
  return Prod.snd <$> (← mchStore.get).get? (← IO.FS.realPath path)

def getPogHash (path : System.FilePath) : IO (Option UInt64) := do
  return (← pogStore.get).get? (← IO.FS.realPath path)

def getGoals (pogHash : UInt64) : IO (Option (Array (String × Lean.Expr))) := do
  return (← poStore.get).get? pogHash

-----------

def registerFile (mchPath pogPath : System.FilePath) (mchHash pogHash : UInt64) (goals : Array (String × Lean.Expr)) : IO PUnit := do
  mchStore.set <| (← mchStore.get).insert mchPath (mchHash, pogPath)
  pogStore.set <| (← pogStore.get).insert pogPath pogHash
  poStore.set <| (← poStore.get).insert pogHash goals
