import POGReader.Schema
import Lean.Data.Xml.Parser

private abbrev throwError {α} : String → IO α := throw ∘ IO.Error.userError

private partial def removeEmptyDeep : Lean.Xml.Element → Lean.Xml.Element
  | ⟨n, a, c⟩ => ⟨n, a, c.filterMap λ
    | .Element e => .some <| .Element <| removeEmptyDeep e
    | .Character str => if str.trim.isEmpty then .none else .some <| .Character str
    | .Comment _ => .none
  ⟩

private def Lean.Xml.Content.kind : Content → String
  | .Element ⟨n, _, _⟩ => s!"element (tag := {n})"
  | .Comment _ => "comment"
  | .Character _ => "raw text"

----------------------

namespace B.POG
  variable
    (vars : IO.Ref (Std.HashMap String Syntax.Typ))

  private partial def parseType : Lean.Xml.Element → IO Syntax.Typ
    | ⟨"Id", attrs, _⟩ => do
      unless attrs.contains "value" do throwError s!"Missing `value` attribute in type description"
      match attrs.get! "value" ++ attrs.getD "suffix" "" with
      | "BOOL" => return .bool
      | "INTEGER" => return .int
      | "REAL" => return .real
      | _ =>
        -- NOTE: maybe there is a much better way of handling unknown identifiers?
        return .int
    | ⟨"Struct", _, _⟩ => throwError "Unsupported structure types"
    | ⟨"Unary_Exp", attrs, nodes⟩ => do
      unless attrs.contains "op" do throwError "Missing `op` attribute in unary type constructor description"
      unless nodes.size = 1 do throwError s!"Expected a single node in unary type constructor, got {nodes.size}"
      let .Element e := nodes[0]! | throwError s!"Unexpected node kind {nodes[0]!.kind}"
      match attrs.get! "op" with
      | "POW" => .pow <$> parseType e
      | op => throwError s!"Unrecognized unary operator {op}"
    | ⟨"Binary_Exp", attrs, nodes⟩ => do
      unless attrs.contains "op" do throwError "Missing `op` attribute in binary type constructor description"
      unless nodes.size = 2 do throwError s!"Expected two nodes in binary type constructor, got {nodes.size}"
      let .Element e₀ := nodes[0]!  | throwError s!"Unexpected node kind {nodes[0]!.kind}"
      let .Element e₁ := nodes[1]!  | throwError s!"Unexpected node kind {nodes[0]!.kind}"
      match attrs.get! "op" with
      | "*" => .prod <$> parseType e₀ <*> parseType e₁
      | op => throwError s!"Unrecognized binary operator {op}"
    | ⟨n, _, _⟩ => throwError s!"Unknown type node {n}"

  private def tryParseTypeInfos (nodes : Array Lean.Xml.Content) : IO (Array (Nat × Syntax.Typ)) := do
      let mut types := #[]
      for node in nodes do
        let .Element ⟨"Type", attrs, nodes⟩ := node | throwError s!"Unexpected node kind {node.kind}"
        unless nodes.size = 1 do throwError s!"Expected a single node in <Type>, got {nodes.size}"
        unless attrs.contains "id" do throwError s!"<Type> node missing `id` attribute"
        let .Element e := nodes[0]! | throwError s!"Unexpected node kind {nodes[0]!.kind}"
        types := types.push ⟨String.toNat! <| attrs.get! "id", ← parseType e⟩
      return types

  private def makeUnaryTermFromOp : String → IO (Syntax.Term → Syntax.Term)
    | "not" => return .not
    | "max" | "imax" | "rmax" => return .max
    | "min" | "imin" | "rmin" => return .min
    | "card" => return .card
    | "dom" => return .dom
    | "ran" => return .ran
    | "POW" => return .pow
    | "POW1" => return .pow₁
    | "FIN" => return .fin
    | "FIN1" => return .fin₁
    | "union" => panic! "TODO: union"
    | "inter" => panic! "TODO: inter"
    | "seq" => panic! "TODO: seq"
    | "seq1" => panic! "TODO: seq1"
    | "iseq" => panic! "TODO: iseq"
    | "iseq1" => panic! "TODO: iseq1"
    | "-" | "-i" | "-r" => return .uminus
    | "~" => return .inv
    | "size" => panic! "TODO: size"
    | "perm" => panic! "TODO: perm"
    | "first" => panic! "TODO: first"
    | "last" => panic! "TODO: last"
    | "id" => return .id
    | "closure" => panic! "TODO: closure"
    | "closure1" => panic! "TODO: closure1"
    | "tail" => panic! "TODO: tail"
    | "front" => panic! "TODO: front"
    | "rev" => panic! "TODO: rev"
    | "conc" => panic! "TODO: conc"
    | "succ" => panic! "TODO: succ"
    | "pred" => panic! "TODO: pred"
    | "rel" => panic! "TODO: rel"
    | "fnc" => panic! "TODO: fnc"
    | "real" => panic! "TODO: real"
    | "floor" => panic! "TODO: floor"
    | "ceiling" => panic! "TODO: ceiling"
    | "tree" => panic! "TODO: tree"
    | "btree" => panic! "TODO: btree"
    | "top" => panic! "TODO: top"
    | "sons" => panic! "TODO: sons"
    | "prefix" => panic! "TODO: prefix"
    | "postfix" => panic! "TODO: postfix"
    | "infix" => panic! "TODO: infix"
    | "sizet" => panic! "TODO: sizet"
    | "mirror" => panic! "TODO: mirror"
    | "left" => panic! "TODO: left"
    | "right" => panic! "TODO: right"
    | "bin" => panic! "TODO: bin"
    | op => throwError s!"Unrecognized op {op}"

  private def makeBinaryTermFromOp : String → IO (Syntax.Term → Syntax.Term → Syntax.Term)
    -- Comparison binary operators
    | ":" => return .mem
    | "/:" => return (.not <| .mem · ·)
    | "<:" => return .subset
    | "/<:" => return (.not <| .subset · ·)
    | "<<:" => panic! "TODO"
    | "/<<:" => panic! "TODO"
    | "=" => return .eq
    | "/=" => return (.not <| .eq · ·)
    | "<i" | "<r" | "<f" => return .lt
    | ">i" | ">r" | ">f" => return flip .lt
    | "<=i" | "<=r" | "<=f" => return .le
    | ">=i" | ">=r" | ">=f" => return flip .le
    -- Expression binary operators
    | "*s" => return .cprod
    | "**" => panic! "TODO"
    | "*" => panic! "TODO"
    | "*i" | "*r" | "*f" => return .mul
    | "**i" | "**f" | "**r" => return .exp
    | "+" | "+i" | "+r" | "+f" => return .add
    | "+->" => return .fun (isPartial := true)
    | "-->" => return .fun (isPartial := false)
    | "+->>" => return .surjfun (isPartial := true)
    | "-->>" => return .surjfun (isPartial := false)
    | "-" | "-s" => return .setminus
    | "-i" | "-r" | "-f" => return .sub
    | "->" => panic! "TODO"
    | ".." => return .interval
    | "/" | "/i" | "/r" | "/f" => return .div
    | "/\\" => return .inter
    | "/|\\" => panic! "TODO"
    | ";" => panic! "TODO"
    | "<+" => panic! "TODO"
    | "<->" => return .rel
    | "<-" => panic! "TODO"
    | "<<|" => panic! "TODO"
    | "<|" => return .domRestr
    | ">+>" => return .injfun (isPartial := true)
    | ">->" => return .injfun (isPartial := false)
    | ">+>>" => panic! "TODO"
    | ">->>" => return .bijfun
    | "><" => panic! "TODO"
    | "||" => panic! "TODO"
    | "\\/" => return .union
    | "\\|/" => panic! "TODO"
    | "^" => panic! "TODO"
    | "mod" => return .mod
    | "," | "|->" => return .maplet
    | "|>" => panic! "TODO"
    | "|>>" => panic! "TODO"
    | "[" => return .image
    | "(" => return .app
    | "<'" => panic! "TODO"
    | "prj1" => panic! "TODO"
    | "prj2" => panic! "TODO"
    | "iterate" => panic! "TODO"
    | "const" => panic! "TODO"
    | "rank" => panic! "TODO"
    | "father" => panic! "TODO"
    | "subtree" => panic! "TODO"
    | "arity" => panic! "TODO"
    -- Logic binary operators
    | "=>" => return .imp
    | "<=>" => return .iff
    | op => throwError s!"Unrecognized unary operator {op}"

  private def makeBoundedQuantifier : String → IO (Array (String × Syntax.Typ) → Syntax.Term → Syntax.Term → Syntax.Term)
    | "%" => return .lambda
    | "SIGMA" | "iSIGMA" | "rSIGMA" => panic! "TODO"
    | "PI" | "iPI" | "rPI" => panic! "TODO"
    | "INTER" => panic! "TODO"
    | "UNION" => panic! "TODO"
    | op => throwError s!"Unrecognized quantifier {op}"

  private def parseAndRegisterId (types : Std.HashMap Nat Syntax.Typ) : Lean.Xml.Element → IO (String × Syntax.Typ)
    | ⟨"Id", attrs, _⟩ => do
      unless attrs.contains "value" do throwError s!"<Id> must contain an attribute `value`"
      unless attrs.contains "typref" do throwError s!"<Id> must contain an attribute `typref`"

      let typref := attrs.get! "typref" |>.toNat!
      let name := attrs.get! "value" ++ attrs.getD "suffix" ""
      let ty := types.get! typref
      vars.modifyGet λ vars ↦ (⟨name, ty⟩, vars.insert name ty)
    | _ => unreachable!

  private def Syntax.Typ.toTerm : Syntax.Typ → Syntax.Term
    | .bool => .𝔹
    | .int => .ℤ
    | .real => .ℝ
    | .pow t => .pow (toTerm t)
    | .prod α β => .cprod (toTerm α) (toTerm β)

  private partial def parseTerm (types : Std.HashMap Nat Syntax.Typ) : Lean.Xml.Element → IO Syntax.Term
    | node@⟨"Id", attrs, _⟩ => (.var ∘ Prod.fst) <$> parseAndRegisterId vars types node
    | ⟨"Integer_Literal", attrs, _⟩ => do
      unless attrs.contains "value" do throwError s!"<Integer_Literal> must contain an attribute `value`"
      return .int (attrs.get! "value").toInt!
    | ⟨"Boolean_Literal", attrs, nodes⟩ => do
      unless attrs.contains "value" do throwError s!"<Boolean_Literal> must contain an attribute `value`"
      match attrs.get! "value" with
      | "TRUE" => return .bool true
      | "FALSE" => return .bool false
      | v => throwError s!"Unknown boolean literal value {v}"
    | ⟨"STRING_Literal", attrs, nodes⟩ => panic! "TODO"
    | ⟨"Real_Literal", attrs, nodes⟩ => panic! "TODO"
    | ⟨tag@"Unary_Pred", attrs, nodes⟩
    | ⟨tag@"Unary_Exp", attrs, nodes⟩ => do
      unless nodes.size = 1 do throwError s!"<{tag}> expects a single child, got {nodes.size}"
      unless attrs.contains "op" do throwError s!"<{tag}> must contain the attribute `op`"

      let .Element e := nodes[0]! | throwError s!"Unexpected node kind {nodes[0]!.kind}"
      (← makeUnaryTermFromOp (attrs.get! "op")) <$> parseTerm types e
    | ⟨"Ternary_Exp", attrs, nodes⟩ => panic! "TODO"
    | ⟨"Nary_Exp", attrs, nodes⟩ => do
      -- possible op: '{', '['
      let .some op := attrs.get? "op" | throwError s!"<Nary_Exp> must contain the attribute `op`"
      let .some ty := attrs.get? "typref" | throwError s!"<Nary_Exp> must contain the attribute `typref`"
      let elems ← nodes.mapM fun
        | .Element e => parseTerm types e
        | _ => throwError s!"Unexpected node kind in <Nary_Exp>"
      match op with
      | "{" => return .set elems (types.get! ty.toNat!)
      | "[" => panic! "TODO: sequences"
      | _ => throwError s!"Unknown n-ary operator `{op}` in <Nary_Exp>"
    | ⟨"Nary_Pred", attrs, nodes⟩ => do
      let .some op := attrs.get? "op" | throwError s!"<Nary_Pred> must contain the attribute `op`"
      let (binop, default) : ((B.Syntax.Term → B.Syntax.Term → B.Syntax.Term) × B.Syntax.Term) :=
        match op with
        | "&" => (.and, .bool true)
        | "or" => (.or, .bool false)
        | _ => panic! s!"Unknown n-ary operator `{op}` in <Nary_Pred>"

      if nodes.size = 0 then return default
      else if nodes.size = 1 then
        let .Element e := nodes[0]! | throwError s!"Unexpected node kind {nodes[0]!.kind}"
        parseTerm types e
      else
        let conjuncts ← nodes.mapM fun
          | .Element e => parseTerm types e
          | _ => throwError s!"Unexpected node kind in <Nary_Pred>"
        let and ← conjuncts.pop.foldrM (init := conjuncts.back!) fun t acc ↦
          return binop t acc
        return and
    | ⟨"Boolean_Exp", attrs, nodes⟩ => do
      unless nodes.size = 1 do throwError s!"<Boolean_Exp> expects a single child, got {nodes.size}"
      let .Element e := nodes[0]! | throwError s!"Unexpected node kind {nodes[0]!.kind}"
      parseTerm types e
    | ⟨"EmptySet", attrs, nodes⟩ => do
      unless nodes.size = 0 do throwError "<EmptySet> expects no child nodes"
      unless attrs.contains "typref" do throwError "<EmptySet> requires a `typref` attribute"

      let ty := attrs.get! "typref" |>.toNat!
      return .set #[] (types.get! ty)
    | ⟨"EmptySeq", attrs, nodes⟩ => panic! "TODO"
    | ⟨"Quantified_Exp", attrs, nodes⟩ => do
      unless nodes.size = 3 do throwError "<Quantified_Exp> expects 3 child node, got {nodes.size}"
      unless attrs.contains "type" do throwError "<Quantified_Exp> requires a `type` attribute"
      unless attrs.contains "typref" do throwError "<Quantified_Exp> requires a `typref` attribute"

      let .Element ⟨"Variables", _, varNodes⟩ := nodes[0]! | throwError s!"First child of <Quantified_Exp> must be <Variables>"
      let .Element ⟨"Pred", _, predNodes⟩ := nodes[1]! | throwError s!"Second child of <Quantified_Exp> must be <Pred>"
      let .Element ⟨"Body", _, bodyNodes⟩ := nodes[2]! | throwError s!"Third child of <Quantified_Exp> must be <Body>"

      let mut vsWithTy : Array (String × Syntax.Typ) := #[]
      for vNode in varNodes do
        let .Element v := vNode | throwError s!"Unexpected node kind {vNode.kind} in <Variables>"
        vsWithTy := vsWithTy.push (←parseAndRegisterId vars types v)

      unless predNodes.size = 1 do throwError s!"<Pred> in <Quantified_Exp> expects a single child, got {predNodes.size}"
      let .Element pred := predNodes[0]! | throwError s!"Unexpected node kind {predNodes[0]!.kind}"
      let pred ← parseTerm types pred

      unless bodyNodes.size = 1 do throwError s!"<Body> in <Quantified_Exp> expects a single child, got {bodyNodes.size}"
      let .Element body := bodyNodes[0]! | throwError s!"Unexpected node kind {bodyNodes[0]!.kind}"
      let body ← parseTerm types body

      return (← makeBoundedQuantifier (attrs.get! "type")) vsWithTy pred body
    | ⟨"Struct", attrs, nodes⟩ => panic! "TODO"
    | ⟨"Record", attrs, nodes⟩ => panic! "TODO"
    | ⟨"Record_Update", attrs, nodes⟩ => panic! "TODO"
    | ⟨"Record_Field_Access", attrs, nodes⟩ => panic! "TODO"
    | ⟨tag@"Binary_Pred", attrs, nodes⟩
    | ⟨tag@"Binary_Exp", attrs, nodes⟩
    | ⟨tag@"Exp_Comparison", attrs, nodes⟩ => do
      unless nodes.size = 2 do throwError s!"<{tag}> expects two children, got {nodes.size}"
      unless attrs.contains "op" do throwError s!"<{tag}> must contain the attribute `op`"

      let .Element e₀ := nodes[0]! | throwError s!"Unexpected node kind {nodes[0]!.kind}"
      let .Element e₁ := nodes[1]! | throwError s!"Unexpected node kind {nodes[1]!.kind}"

      (← makeBinaryTermFromOp (attrs.get! "op"))
        <$> parseTerm types e₀
        <*> parseTerm types e₁
    | ⟨"Quantified_Pred", attrs, nodes⟩ => do
      unless attrs.contains "type" do throwError "<Quantified_Pred> must contain the attribute `type`"
      unless nodes.size = 2 do throwError s!"<Quantified_Pred> expects two children, got {nodes.size}"

      let .Element ⟨"Variables", _, varNodes⟩ := nodes[0]! | throwError s!"First child of <Quantified_Pred> must be <Variables>"
      let .Element ⟨"Body", _, bodyNodes⟩ := nodes[1]! | throwError s!"Second child of <Quantified_Pred> must be <Body>"

      let mut vsWithTy : Array (String × Syntax.Typ) := #[]
      for vNode in varNodes do
        let .Element v := vNode | throwError s!"Unexpected node kind {vNode.kind} in <Variables>"
        vsWithTy := vsWithTy.push (←parseAndRegisterId vars types v)

      unless bodyNodes.size = 1 do
        throwError s!"<Body> in <Quantified_Pred> expects a single child, got {bodyNodes.size}"
      let .Element body := bodyNodes[0]! | throwError s!"Unexpected node kind {bodyNodes[0]!.kind}"
      let body ← parseTerm types body

      match attrs.get! "type" with
      | "!" => return .all vsWithTy body
      | "#" => return .exists vsWithTy body
      | ty => throwError s!"Unknown quantifier `{ty}` in <Quantified_Pred>"
    | ⟨"Quantified_Set", _, nodes⟩ => do
      unless nodes.size = 2 do throwError s!"<Quantified_Set> expects two children, got {nodes.size}"

      let .Element ⟨"Variables", _, varNodes⟩ := nodes[0]! | throwError s!"First child of <Quantified_Set> must be <Variables>"
      let .Element ⟨"Body", _, bodyNodes⟩ := nodes[1]! | throwError s!"Second child of <Quantified_Set> must be <Body>"

      let mut vsWithTy : Array (String × Syntax.Typ) := #[]
      for vNode in varNodes do
        let .Element v := vNode | throwError s!"Unexpected node kind {vNode.kind} in <Variables>"
        vsWithTy := vsWithTy.push (←parseAndRegisterId vars types v)

      unless bodyNodes.size = 1 do
        throwError s!"<Body> in <Quantified_Set> expects a single child, got {bodyNodes.size}"
      let .Element body := bodyNodes[0]! | throwError s!"Unexpected node kind {bodyNodes[0]!.kind}"
      let body ← parseTerm types body

      return .collect vsWithTy body
    | ⟨tag, _, _⟩ => throwError s!"Unknown tag {tag} for expression"

  private def parseDefineType : String → IO (Option Schema.DefineType)
    | "B definitions" => return .none
    | "ctx" => return .some .ctx
    | "seext" => return .some .seext
    | "inv" => return .some .inv
    | "ass" => return .some .ass
    | "lprp" => return .some .lprp
    | "inprp" => return .some .inprp
    | "inext" => return .some .inext
    | "cst" => return .some .cst
    | "sets" => return .some .sets
    | "mchcst" => return .some .mchcst
    | "aprp" => return .some .aprp
    | "abs" => return .some .abs
    | "imlprp" => return .some .imlprp
    | "imprp" => return .some .imprp
    | "imext" => return .some .imext
    | ty => throwError s!"Unrecognized definition type {ty}"

  private def parseDefine (types : Std.HashMap Nat Syntax.Typ) (nodes : Array Lean.Xml.Element) : (name : Schema.DefineType) → IO (Schema.Define name)
    | .ctx => Function.uncurry .ctx <$> parseSetsAndTerms nodes
    | .seext => .seext <$> do
      let (terms, nodes) ← parseTerms nodes
      unless nodes.size = 0 do throwError s!"There must not be sets in `seext` definition"
      return terms
    | .inv => .inv <$> do
      let (terms, nodes) ← parseTerms nodes
      unless nodes.size = 0 do throwError s!"There must not be sets in `inv` definition"
      return terms
    | .ass => .ass <$> do
      let (terms, nodes) ← parseTerms nodes
      unless nodes.size = 0 do throwError s!"There must not be sets in `ass` definition"
      return terms
    | .lprp => Function.uncurry .lprp <$> parseSetsAndTerms nodes
    | .inprp => Function.uncurry .inprp <$> parseSetsAndTerms nodes
    | .inext => .inext <$> do
      let (terms, nodes) ← parseTerms nodes
      unless nodes.size = 0 do throwError s!"There must not be sets in `inext` definition"
      return terms
    | .cst => .cst <$> do
      let (terms, nodes) ← parseTerms nodes
      unless nodes.size = 0 do throwError s!"There must not be sets in `cst` definition"
      return terms
    | .sets => .sets <$> do
        let (sets, nodes) ← parseSets nodes
        unless nodes.size = 0 do throwError s!"There must not be terms in `sets` definition"
        return sets
    | .mchcst => .mchcst <$> do
      let (terms, nodes) ← parseTerms nodes
      unless nodes.size = 0 do throwError s!"There must not be sets in `mchcst` definition"
      return terms
    | .aprp => Function.uncurry .aprp <$> parseSetsAndTerms nodes
    | .abs => .abs <$> do
      let (terms, nodes) ← parseTerms nodes
      unless nodes.size = 0 do throwError s!"There must not be sets in `abs` definition"
      return terms
    | .imlprp => Function.uncurry .imlprp <$> parseSetsAndTerms nodes
    | .imprp => Function.uncurry .imprp <$> parseSetsAndTerms nodes
    | .imext => .imext <$> do
      let (terms, nodes) ← parseTerms nodes
      unless nodes.size = 0 do throwError s!"There must not be sets in `imext` definition"
      return terms
  where
    parseSet : Lean.Xml.Element → IO Schema.Set
      | ⟨"Set", _, nodes⟩ => do
        unless nodes.size >= 1 do throwError s!"<Set> must contain at least one child node"
        let .Element node@⟨"Id", attrs, _⟩ := nodes[0]! | throwError s!"First child node of <Set> must be a <Id>"

        let ⟨name, _⟩ ← parseAndRegisterId vars types node
        let values ← do
          let mut values := #[]

          if nodes.size = 2 then
            let .Element ⟨"Enumerated_Values", _, nodes⟩ := nodes[1]! | throwError "<Set> must only contain <Enumerated_Values> after <Id>"

            let mut i := 0
            while _h : i < nodes.size do
              let .Element node@⟨"Id", attrs, _⟩ := nodes[i] | throwError s!"<Enumerated_Values> may only contain <Id> nodes"
              let ⟨v, _⟩ ← parseAndRegisterId vars types node
              values := values.push v
              i := i + 1

          pure values

        return { name, values }
      | ⟨tag, _, _⟩ => throwError s!"Unrecognized tag {tag}"

    parseSets (nodes : Array Lean.Xml.Element) : IO (Array Schema.Set × Array Lean.Xml.Element) := do
      let mut sets := #[]
      let mut i := 0
      while _h : i < nodes.size do
        try
          sets := sets.push (← parseSet nodes[i])
          i := i + 1
        catch _ =>
          break
      return (sets, nodes[i:])

    parseTerms (nodes : Array Lean.Xml.Element) : IO (Array Syntax.Term × Array Lean.Xml.Element) := do
      let mut terms := #[]
      let mut i := 0
      while _h : i < nodes.size do
        try
          terms := terms.push (← parseTerm vars types nodes[i])
          i := i + 1
        catch e =>
          throw e
          break
      return (terms, nodes[i:])

    parseSetsAndTerms (nodes : Array Lean.Xml.Element) : IO (Array Schema.Set × Array Syntax.Term) := do
      let (sets, nodes) ← parseSets nodes
      let (terms, nodes) ← parseTerms nodes
      unless nodes.size = 0 do throwError s!"Some nodes, which are not sets nor terms, remain"
      return (sets, terms)

  private def parseSimpleGoal (nodes : Array Lean.Xml.Element) (types : Std.HashMap Nat Syntax.Typ) :
      IO Schema.SimpleGoal := do
    let mut name := ""
    let mut refHyps := #[]
    let mut goal := .bool true

    for ⟨tag, attrs, nodes⟩ in nodes do
      match tag with
      | "Tag" =>
        unless nodes.size = 1 do throwError s!"Expected a single node in <Tag>, got {nodes.size}"
        let .Character str := nodes[0]! | throwError s!"Node of <Tag> must be a raw string"
        name := str
      | "Ref_Hyp" =>
        unless attrs.contains "num" do throwError s!"<Ref_Hyp> must contain attribute `num`"
        refHyps := refHyps.push (attrs.get! "num").toNat!
      | "Goal" =>
        unless nodes.size = 1 do throwError s!"Expected a single node in <Goal>, got {nodes.size}"
        let .Element e := nodes[0]! | throwError s!"Unexpected node kind {nodes[0]!.kind}"
        goal ← parseTerm vars types e
      | "Proof_State" => continue
      | _ => throwError s!"Unrecognized tag {tag} in <Simple_Goal>"

    return { name, refHyps, goal }

  private def parseObligation (nodes : Array Lean.Xml.Element) (types : Std.HashMap Nat Syntax.Typ) :
      IO Schema.ProofObligation := do
    let mut obligation : Schema.ProofObligation := ∅
    for ⟨name, attrs, nodes⟩ in nodes do
      match name with
      | "Tag" =>
        unless nodes.size = 1 do throwError s!"Expected a single node in <Tag>, got {nodes.size}"
        let .Character name := nodes[0]! | throwError s!"Content of <Tag> must be a raw string"
        obligation := { obligation with name := name }
      | "Definition" =>
        unless nodes.size = 0 do throwError s!"Expected no children for <Definition> node, got {nodes.size}"
        unless attrs.contains "name" do throwError s!"<Definition> node must contain a `name` attribute"
        if let .some ty ← parseDefineType (attrs.get! "name") then
          obligation := { obligation with uses := obligation.uses.push ty }
      | "Hypothesis" =>
        unless nodes.size = 1 do throwError s!"Expected a single node in <Hypothesis>, got {nodes.size}"
        let .Element e := nodes[0]! | throwError s!"Unexpected node kind {nodes[0]!.kind}"
        obligation := { obligation with hypotheses := obligation.hypotheses.push (← parseTerm vars types e) }
      | "Local_Hyp" =>
        unless nodes.size = 1 do throwError s!"Expected a single node in <Local_Hyp>, got {nodes.size}"
        unless attrs.contains "num" do throwError s!"<Local_Hyp> node must contain a `num` attribute"
        let .Element e := nodes[0]! | throwError s!"Unexpected node kind {nodes[0]!.kind}"
        let i := attrs.get! "num" |>.toNat!
        let term ← parseTerm vars types e
        if obligation.localHyps.contains i then throwError "Local hypothesis {i} already registered"
        obligation := { obligation with localHyps := obligation.localHyps.insert i term }
      | "Simple_Goal" =>
        let nodes ← nodes.mapM λ
          | .Element e => pure e
          | node => throwError s!"Unexpected node kind {node.kind}"
        obligation := { obligation with simpleGoals := obligation.simpleGoals.push (← parseSimpleGoal vars nodes types) }
      | _ => throwError s!"Unexpected tag {name} in <Proof_Obligation>"
    return obligation

  private def parseProofObligations : Lean.Xml.Element → IO Schema.ProofObligations
    | ⟨"Proof_Obligations", _, nodes⟩ => do
      let mut defines' : Array Lean.Xml.Element := #[]
      let mut obligations' : Array Lean.Xml.Element := #[]

      -- First, try to parse all type infos
      let mut typeInfos := Std.HashMap.emptyWithCapacity
      for node in nodes do
        let .Element e@⟨name, _, children⟩ := node | throwError s!"Unexpected node kind {node.kind}"
        match name with
        | "TypeInfos" =>
          for ⟨i, ty⟩ in ← tryParseTypeInfos children do
            if i ∈ typeInfos then throwError s!"Type {i} already registered"
            typeInfos := typeInfos.insertIfNew i ty
        | "Define" => defines' := defines'.push e
        | "Proof_Obligation" => obligations' := obligations'.push e
        | _ => throwError s!"Unknown node tag {name} in <Proof_Obligations>"

      -- Then, parse definitions
      let mut defines := Std.DHashMap.emptyWithCapacity
      for node in defines' do
        let ⟨"Define", attrs, nodes⟩ := node | unreachable!
        unless attrs.contains "name" do throwError s!"<Define> requires a attribute `name`"

        if let .some name ← attrs.get! "name" |> parseDefineType then
          let nodes ← nodes.mapM λ
            | .Element e => pure e
            | node => throwError s!"Unexpected node kind {node.kind}"
          defines := defines.insert name (← parseDefine vars typeInfos nodes name)

      -- Finally, parse proof obligations
      let mut obligations := #[]
      for node in obligations' do
        let ⟨"Proof_Obligation", _, nodes⟩ := node | unreachable!
        let nodes ← nodes.mapM λ
          | .Element e => pure e
          | node => throwError s!"Unexpected node kind {node.kind}"
        obligations := obligations.push (← parseObligation vars nodes typeInfos)

      -- NOTE: remove all B builtins
      let vars := B.Syntax.reservedIdentifiers.fold (init := ← vars.get) Std.HashMap.erase

      return { defines, obligations, vars := vars.toArray /-, typeInfos -/ }
    | ⟨name, _, _⟩ => throwError s!"Unexpected root element '{name}'"

  omit vars in
  def parse' (content : String) : IO Schema.ProofObligations := do
    let vars ← IO.mkRef ∅

    IO.ofExcept (Lean.Xml.parse content)
      >>= parseProofObligations vars ∘ removeEmptyDeep

  omit vars in
  def parse (path : System.FilePath) : IO Schema.ProofObligations :=
    IO.FS.readFile path >>= parse'
end B.POG

-- #eval B.POG.parse ("specs" / "Exists.pog")
