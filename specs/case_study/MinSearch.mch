MACHINE MinSearch

CONSTANTS
  SS

PROPERTIES
  SS : FIN1(INTEGER)

VARIABLES
  done, mm

INVARIANT
  done : FIN1(SS) &
  mm : SS &
  mm = min(done)

INITIALISATION
  ANY xx WHERE
      xx : SS
  THEN
      done := {xx} ||
      mm := xx
  END

OPERATIONS
  mi <-- search_min =
    PRE done = SS THEN
      mi := mm
    END;

  step =
    IF done /= SS THEN
      ANY add WHERE
          add : FIN1(SS - done)
      THEN
          done := done \/ add ||
          mm := min(done \/ add)
      END
    END
END
