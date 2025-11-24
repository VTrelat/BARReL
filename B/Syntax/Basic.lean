namespace B

abbrev 𝒱 := String

inductive Term where
  -- basic terms
  | var (v : 𝒱)
  | int (n : Int)
  | bool (b : Bool)
  -- pairs
  | maplet (x y : Term)
  -- arithmetic
  | add (x y : Term)
  | sub (x y : Term)
  | mul (x y : Term)
  | le (x y : Term)
  -- logic
  | and (x y : Term)
  | not (x : Term)
  | eq (x y : Term)
  -- sets
  -- basic sets
  | ℤ
  | 𝔹
  -- set operations
  | mem (x : Term) (S : Term)
  | collect (vs : List 𝒱) (D P : Term)
  | pow (S : Term)
  | cprod (S T : Term)
  | union (S T : Term)
  | inter (S T : Term)
  | card (S : Term)
  -- functions
  | app (f x : Term)
  | lambda (vs : List 𝒱) (D P : Term)
  | pfun (A B : Term)
  -- | tfun (A B : Term)
  | min (S : Term) -- could be extended to minᵢ, minᵣ, etc.
  | max (S : Term)
  -- quantifiers
  | all (vs : List 𝒱) (D P : Term)
  deriving DecidableEq, Inhabited

infixl:65 " ↦ᴮ " => Term.maplet
infixl:70 " +ᴮ " => Term.add
infixl:70 " -ᴮ " => Term.sub
infixl:75 " *ᴮ " => Term.mul
infixl:45 " ∧ᴮ " => Term.and
prefix:80 " ¬ᴮ " => Term.not
infixl:40 " =ᴮ " => Term.eq
infixl:40 " ≤ᴮ " => Term.le
infixl:65 " ∈ᴮ " => Term.mem
prefix:70 " 𝒫ᴮ " => Term.pow
infixl:75 " ⨯ᴮ " => Term.cprod
infixl:80 " ∪ᴮ " => Term.union
infixl:85 " ∩ᴮ " => Term.inter
prefix:20 "@ᴮ" => Term.app
infixl:90 " ⇸ᴮ " => Term.pfun
notation:90 "|" S "|ᴮ" => Term.card S

def fv : Term → List 𝒱
  | .var v => [v]
  | .int _ => []
  | .bool _ => []
  | .maplet x y | .add x y | .sub x y | .mul x y | .and x y | .le x y | .eq x y => fv x ++ fv y
  | .not x => fv x
  | .ℤ => []
  | .𝔹 => []
  | .mem x S => fv x ++ fv S
  | .collect vs D P | .all vs D P | .lambda vs D P => fv D ++ List.removeAll (fv P) vs
  | .pow S => fv S
  | .cprod S T => fv S ++ fv T
  | .union S T => fv S ++ fv T
  | .inter S T => fv S ++ fv T
  | .pfun A B => fv A ++ fv B
  | .app f x => fv f ++ fv x
  | .card S => fv S
  | .min S => fv S
  | .max S => fv S

abbrev MAXINT : Int := 2147483647
abbrev MININT : Int := -2147483647

end B
