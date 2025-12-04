MACHINE
  Pixels
SETS Colors = {Red, Green, Blue}
CONSTANTS
  pixels
VARIABLES
  pixel
PROPERTIES
  pixels = (Colors → 0..255)
INVARIANT
  pixel ∈ pixels
INITIALISATION
  pixel := {Red ↦ 0, Green ↦ 0, Blue ↦ 0}
OPERATIONS
  flip (pp) =
  PRE pp ∈ pixels THEN
    pixel := λ color. (color ∈ Colors | 255 - pp(color))
  END;
  
  switchOff =
  PRE pixel ∈ pixels THEN
    pixel := λ color. (color ∈ Colors | 0)
  END;

  switchOn =
  PRE pixel ∈ pixels THEN
    pixel := λ color. (color ∈ Colors | 255)
  END
END
