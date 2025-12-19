namespace B
  /--
    The category of keywords that are not to be reserved in Lean.
  -/
  declare_syntax_cat keyword (behavior := symbol)

  syntax prop_decl := ident " : " term
end B
