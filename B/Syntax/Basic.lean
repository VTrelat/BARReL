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
  | or (x y : Term)
  | imp (x y : Term)
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
  | interval (lo hi : Term)
  -- functions
  | app (f x : Term)
  | lambda (vs : List 𝒱) (D P : Term)
  | pfun (A B : Term)
  | tfun (A B : Term)
  | min (S : Term) -- could be extended to minᵢ, minᵣ, etc.
  | max (S : Term)
  -- quantifiers
  | all (vs : List 𝒱) (D P : Term)
  | «exists» (vs : List 𝒱) (D P : Term)
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
infixr:20 " ⇒ᴮ " => Term.imp
infixl:40 " ∨ᴮ " => Term.or
infix:50 " ..ᴮ " => Term.interval

abbrev MAXINT : Int := 2147483647
abbrev MININT : Int := -2147483647

end B
