namespace B
  declare_syntax_cat discharger_command
  syntax (name := next_discharge) withPosition("next " colGt withPosition(ppIndent(ppLine tacticSeq))) : discharger_command

  syntax "prove_obligations_of " ident ppLine withPosition(ppIndent(ppLine colEq discharger_command)*) : command
end B
