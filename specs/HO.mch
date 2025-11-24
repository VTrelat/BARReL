MACHINE HO

SETS X; Y
CONSTANTS x, y0, y1, F

PROPERTIES
  x ∈ X ∧
  y0 ∈ Y ∧
  y1 ∈ Y ∧
  y0 ≠ y1 ∧
  F : X --> Y

INVARIANT
  ∃(G).(G ∈ X --> Y ∧ G(x) ≠ F(x))

END
