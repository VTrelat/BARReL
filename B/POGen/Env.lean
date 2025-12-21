import Lean.Environment
import Lean.Message

namespace B
  structure Obligation where
    name : Lean.Name
    description : String
    type : Lean.Expr

  instance : Lean.ToMessageData Obligation where
    toMessageData o := "{"
      ++ Lean.MessageData.nest 2
          (Lean.indentD m!"name := {o.name}"
        ++ Lean.indentD m!"description := {o.description}"
        ++ Lean.indentD m!"type := {Lean.indentExpr o.type}")
      ++ "\n}"

  initialize
    obligations : Lean.PersistentEnvExtension Obligation (Array Obligation) (Array Obligation) ←
      Lean.registerPersistentEnvExtension {
        mkInitial := pure #[]
        addImportedFn obligationss := return Array.flatten obligationss
        addEntryFn := Array.append
        exportEntriesFnEx _ obligations _ := obligations
      }
end B
