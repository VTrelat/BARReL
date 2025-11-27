import Lean.Util.Trace

open Lean

initialize
  registerTraceClass `b4lean.pog

register_option b4lean.atelierb : String := {
  defValue := ""
  descr := "Path to the Atelier-B distribution"
}
