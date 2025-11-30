MACHINE
    Test

SETS XX;YY
    
CONSTANTS
    FF 
   
PROPERTIES 
    FF ∈ XX --> YY
    
INVARIANT
    (∃(xx,yy). (xx ∈ XX ∧ yy ∈ YY ∧ FF(xx) = yy)) => FF[XX] = YY

END
