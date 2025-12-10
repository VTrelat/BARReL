MACHINE JobQueue
SETS
  JOB
CONSTANTS
  Limit, MaxDeadline
PROPERTIES
  Limit ∈ NAT1 ∧ MaxDeadline ∈ NAT1
VARIABLES
  Ready, deadline
INVARIANT
  /* abstract set + finiteness */
  Ready ∈ FIN(JOB) ∧
  deadline ∈ JOB → NAT1 ∧
  card(Ready) ≤ Limit ∧
  (Ready ≠ ∅ ⇒
     min(deadline[Ready]) ≥ 1 ∧
     max(deadline[Ready]) ≤ MaxDeadline)
INITIALISATION
  Ready := ∅ || deadline :∈ JOB → NAT1
OPERATIONS
  enqueue(j) =
    PRE j ∈ JOB ∧ j ∉ Ready ∧ card(Ready) < Limit ∧ deadline(j) ≤ MaxDeadline
    THEN
      Ready := Ready ∪ {j}
    END;
  dequeue =
    PRE Ready ≠ ∅
    THEN
      ANY j WHERE
        j ∈ Ready ∧
        deadline(j) = min(deadline[Ready])
      THEN
        Ready := Ready - {j}
      END
    END
END