MACHINE CounterMin
VARIABLES X
INVARIANT
  X ∈ FIN1(ℤ) ∧
  max(X) = -min(X)
INITIALISATION
  X := {0}
OPERATIONS
  inc =
  ANY z WHERE z ∈ ℕ THEN
    X := (-z)..z
  END
END