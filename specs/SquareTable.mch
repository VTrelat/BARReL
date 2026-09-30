MACHINE SquareTable
CONSTANTS sq
PROPERTIES
  sq : NATURAL --> NATURAL &
  sq(0) = 0 &
  !kk.(kk : NATURAL => sq(kk+1) = sq(kk) + 2*kk + 1)
ASSERTIONS
  !nn.(nn : NATURAL => sq(nn) = nn*nn)
END
