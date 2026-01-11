/*
This machine's only purpose is to demonstrate that Atelier B's interactive
prover allows the user to discharge wrong assertions, i.e. to prove false,
where BARReL does not.
*/
MACHINE
  DerivFalse

ASSERTIONS
  # x. (x : INTEGER & not(x : INTEGER))

END
