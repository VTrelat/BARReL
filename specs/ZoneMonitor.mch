MACHINE ZoneMonitor

SETS
  SENSORS; ZONES

CONSTANTS
  zone, quorum, value_min, value_max, lower0, upper0

PROPERTIES
  zone : SENSORS --> ZONES &
  quorum : ZONES --> NATURAL1 &
  value_min : INTEGER &
  value_max : INTEGER &
  value_min <= value_max &
  lower0 : ZONES --> value_min..value_max &
  upper0 : ZONES --> value_min..value_max &
  !zz.(zz : ZONES => lower0(zz) <= upper0(zz))

DEFINITIONS
  VALUE == value_min..value_max;
  active(zz) == dom(reading) /\ zone~[{zz}];
  values(zz) == reading[active(zz)]

VARIABLES
  reading, lower, upper, permit

INVARIANT
  reading : SENSORS +-> VALUE &
  lower : ZONES --> VALUE &
  upper : ZONES --> VALUE &
  permit <: ZONES &
  !zz.(zz : ZONES => lower(zz) <= upper(zz)) &
  !zz.(zz : permit =>
    active(zz) /= {} &
    quorum(zz) <= card(active(zz)) &
    lower(zz) <= min(values(zz)) &
    max(values(zz)) <= upper(zz))

INITIALISATION
  reading := {} ||
  lower := lower0 ||
  upper := upper0 ||
  permit := {}

OPERATIONS
  Record(ss,vv) =
    PRE ss : SENSORS & vv : VALUE
    THEN
      reading := reading <+ {ss |-> vv} ||
      permit := permit - {zone(ss)}
    END;

  RecordBatch(batch) =
    PRE batch : SENSORS +-> VALUE
    THEN
      reading := reading <+ batch ||
      permit := permit - zone[dom(batch)]
    END;

  Withdraw(ss) =
    PRE ss : dom(reading)
    THEN
      reading := {ss} <<| reading ||
      permit := permit - {zone(ss)}
    END;

  Configure(zz,ll,uu) =
    PRE zz : ZONES & ll : VALUE & uu : VALUE & ll <= uu
    THEN
      lower := lower <+ {zz |-> ll} ||
      upper := upper <+ {zz |-> uu} ||
      permit := permit - {zz}
    END;

  Authorize(zz) =
    PRE zz : ZONES &
        active(zz) /= {} &
        quorum(zz) <= card(active(zz)) &
        lower(zz) <= min(values(zz)) &
        max(values(zz)) <= upper(zz)
    THEN
      permit := permit \/ {zz}
    END;

  Revoke(zz) =
    PRE zz : ZONES
    THEN
      permit := permit - {zz}
    END;

  vv <-- ReadSensor(ss) =
    PRE ss : dom(reading)
    THEN
      vv := reading(ss)
    END;

  count,lo,hi <-- ZoneSummary(zz) =
    PRE zz : ZONES & active(zz) /= {}
    THEN
      count := card(active(zz)) ||
      lo := min(values(zz)) ||
      hi := max(values(zz))
    END
END
