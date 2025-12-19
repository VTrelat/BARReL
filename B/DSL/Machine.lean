import B.DSL.Basic

namespace B
  open Lean.Parser

  syntax (name := setsKw) "sets" : keyword
  syntax (name := concreteConstantsKw) patternIgnore(&"concrete_constants" <|> &"constants") : keyword
  syntax (name := propertiesKw) "properties" : keyword
  syntax (name := abstractVariablesKw) patternIgnore(&"abstract_variables" <|> &"variables") : keyword
  syntax (name := invariantsKw) "invariants" : keyword
  syntax (name := assertionsKw) "assertions" : keyword
  syntax (name := beginKw) "begin" : keyword
  syntax (name := endKw) "end" : keyword
  syntax (name := skipKw) "skip" : keyword
  syntax (name := preKw) "pre" : keyword
  syntax (name := thenKw) "then" : keyword
  syntax (name := assertKw) "assert" : keyword
  syntax (name := anyKw) "any" : keyword
  syntax (name := whereKw) "where" : keyword
  syntax (name := initialisationKw) "initialisation" : keyword
  syntax (name := operationsKw) "operations" : keyword



  syntax set_decl := ident (atomic(" := ") "{" ident,+ "}")?
  syntax sets :=
    withPosition(setsKw colGt withPosition(ppIndent(ppLine colEq set_decl)+))

  syntax constant_decl := ident (" ∈ " <|> " := ") term
  syntax concrete_constants :=
    withPosition(concreteConstantsKw colGt withPosition(ppIndent(ppLine colEq constant_decl)+))

  syntax properties :=
    withPosition(propertiesKw colGt withPosition(ppIndent((ppLine colEq prop_decl)+)))

  syntax var_decl := ident " ∈ " term
  syntax abstract_variables :=
    withPosition(abstractVariablesKw colGt withPosition(ppIndent(ppLine colEq var_decl)+))

  syntax invariants :=
    withPosition(invariantsKw colGt withPosition(ppIndent(ppLine colEq prop_decl)+))

  syntax assertions :=
    withPosition(assertionsKw colGt withPosition(ppIndent(ppLine colEq prop_decl)+))

  declare_syntax_cat substitution (behavior := symbol)
  declare_syntax_cat substitution_op (behavior := symbol)

  syntax (name := substitution_op_block) beginKw ppIndent(ppLine substitution) ppLine endKw : substitution_op
  syntax (name := substitution_op_id) skipKw : substitution_op
  syntax (name := substitution_op_set_eq1) ident,+ " := " term,+ : substitution_op
  syntax (name := substitution_op_precond) preKw ppLine withPosition(ppIndent(ppLine colEq prop_decl)+) ppLine thenKw ppIndent(ppLine substitution) ppLine endKw : substitution_op
  syntax (name := substitution_op_assert) assertKw ppLine withPosition(ppIndent(ppLine colEq prop_decl)+) ppLine thenKw ppIndent(ppLine substitution) ppLine endKw : substitution_op
  -- choice
  -- conditional
  -- select
  -- case
  syntax (name := substitution_op_any) anyKw ppLine withPosition(ppIndent(ppLine colEq var_decl)+) (ppLine whereKw ppLine withPosition(ppIndent(ppLine colEq prop_decl)+))? ppLine thenKw ppIndent(ppLine substitution) ppLine endKw : substitution_op
  -- any
  -- let
  syntax (name := substitution_op_becomes_elt_of) ident,+ " :∈ " term : substitution_op
  syntax (name := substitution_op_becomes_such_that) ident,+ " :(" term ")" : substitution_op
  -- var
  -- operation call

  syntax substitution_op : substitution
  syntax:20 (name := substitution_seq) substitution:21 " ;" ppLine substitution:20 : substitution
  syntax:20 (name := substitution_par) substitution:21 patternIgnore(" ‖" <|> " ||") ppLine substitution:20 : substitution
  -- while

  syntax initialisation := withPosition(initialisationKw ppIndent(ppLine colGt substitution))

  syntax op_header := ident (("," ident)* " ← " ident)?
  syntax operation := op_header ("(" var_decl,+ ")")? " := " ppIndent(ppLine substitution_op)
  syntax operations :=
    withPosition(operationsKw colGt withPosition((ppIndent(ppLine colEq operation))+))

  syntax clause :=
    /- constraints <|> sees <|> includes <|> uses -- <|> promotes <|> extends
    <|> -/ sets <|> /- abstract_constants <|> -/ concrete_constants <|> properties
    <|> abstract_variables /- <|> concrete_variables -/ <|> invariants
    <|> assertions <|> initialisation <|> operations

  syntax machine_name := ident ("(" ident,+ ")")?

  syntax (name := machine) "machine " machine_name (ppLine clause)* ppLine &"end" : command
end B
