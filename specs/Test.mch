MACHINE
  Test

SETS X;Y

INVARIANT
  ∀ (F, G). (F ∈ X --> Y ∧ G ∈ X --> Y ∧ (∀ (x). (x ∈ X => F(x) = G(x))) => F = G)

END
