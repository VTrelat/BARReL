# ZoneMonitor: design and completed implementation

Designed 29 September 2026; implemented and checked 30 September 2026. The B source is `specs/ZoneMonitor.mch`, the complete native POG is `specs/zonemonitor/ZoneMonitor.pog`, and the BARReL proof is `examples/ZoneMonitor.lean`. All 146 retained obligations are proved, published by `qed`, and audited for transitive axioms.

This case demonstrates the framework as a whole: importing B obligations, representing partial expressions with WD evidence, sharing repeated WD goals, automatic discharge, individual interactive proofs, and final publication. Its obligations arise from a sensor authorization policy and eight operations. There is no duplicated workload added solely to increase the counts.

## Model and guarantee

The finite nonempty carriers `SENSORS` and `ZONES` have a fixed total assignment `zone : SENSORS --> ZONES` and positive quorum map `quorum : ZONES --> NATURAL1`. Measurements belong to a nonempty integer interval `VALUE`. Here `:` denotes B membership, `-->` the total-function space, and `+->` the partial-function space.

Mutable state:

- `reading : SENSORS +-> VALUE`, containing available readings.
- `lower, upper : ZONES --> VALUE`, the configured interval for each zone.
- `permit <: ZONES`, the currently authorized zones.

The B definitions are:

```text
active(z) == dom(reading) /\ zone~[{z}]
values(z) == reading[active(z)]
```

Quorum counts `card(active(z))`, not `card(values(z))`: multiple sensors may report the same value. In addition to typing, the invariant requires ordered bounds for every zone and, for every permitted zone, nonempty available sensors, sufficient quorum, and minimum/maximum readings within those bounds. The nonempty condition precedes the extrema. Finiteness follows from the sensor carrier; nonemptiness of the image also uses `active(z) <: dom(reading)`.

A zone need not have enough installed sensors to attain its quorum. Such a zone cannot be authorized. Initialization sets `reading` and `permit` to the empty set and copies ordered initial bound maps supplied as constants. The proved guarantee concerns recorded measurements and authorization consistency; sensor accuracy and eventual authorization are outside the model.

## Implemented operations

| Operation | Guard and effect | Main proof content |
| --- | --- | --- |
| `Record(s,v)` | Override one reading and revoke its zone | Partial-function typing; preservation in other zones |
| `RecordBatch(batch)` | Override with a partial-function batch and revoke `zone[dom(batch)]` | Frame argument for every unaffected zone |
| `Withdraw(s)` | Require an available reading, remove it, and revoke its zone | Domain subtraction; preservation in other zones |
| `Configure(z,l,u)` | Set ordered bounds and revoke the zone | Total-function typing and singleton override |
| `Authorize(z)` | Require nonempty readings, quorum, and both bounds; add the zone | Guard WD and authorization-policy preservation |
| `Revoke(z)` | Remove a permit | Restriction of the invariant |
| `ReadSensor(s)` | Require an available reading and return it | Guarded application |
| `ZoneSummary(z)` | Require nonempty available sensors; return count and extrema | Finite sets and nonempty images |

All parameter typing guards are present in the machine. A batch may be empty. No refinement chain, sequence history, clock, division, modulo, or exponentiation is needed.

## Central proof and helper modules

Let `reading' = reading <+ batch` and `T = zone[dom(batch)]`. If `z` is outside `T`, no sensor assigned to `z` belongs to the batch domain. Override preserves both the domain and the values of readings in that zone. Thus its available-sensor set and its image under `reading` are unchanged. Every old permit outside `T` retains its nonemptiness, quorum and extremum bounds. Since the operation assigns `permit' = permit - T`, every remaining permit satisfies the policy.

This argument is proved by reusable lemmas `available_overload` and `readings_overload`, with analogous domain-subtraction lemmas for withdrawal. The manuscript includes the actual `Operation_RecordBatch_15` proof command and explains its separate WD prerequisite.

- `ZoneMonitorSupport.lean`: generic relational frame lemmas and finite/nonempty-set facts.
- `ZoneMonitorProofs.lean`: singleton override and application lemmas.
- `ZoneMonitorAutomation.lean`: the explicitly supplied import-time WD extension.
- `ZoneMonitorSourceWD.lean`: lemmas and the explicitly invoked `zone_source_wd` tactic.
- `ZoneMonitorEvidence.lean`: completion checks, transitive axiom audit and evidence export.

These are case-study additions; the BARReL core is unchanged. The measured automatic rate includes the supplied extension, not just stock automation.

## Executed validation

Run from the repository root:

```sh
specs/zonemonitor/check.sh --regenerate
```

This command passed end to end: native Atelier B generation, backend and helper builds, the complete proof, `qed`, the axiom audit, and evidence export. Without `--regenerate`, the script checks the retained POG without needing a native Atelier B installation.

The POG is generated with `pog -w`, retaining source WD obligations as well as principal obligations. In particular it includes the output-expression WD goals for both read-only operations. The default `import machine` path omits `-w`; the case therefore uses `import pog ZoneMonitor from "specs/zonemonitor"` with the complete retained POG.

| Obligation class | Total | Automatic at import | Explicit proof commands |
| --- | ---: | ---: | ---: |
| Principal | 41 | 10 | 31 |
| Atelier B source WD | 39 | 10 | 29 |
| BARReL-generated WD | 66 | 51 | 15 |
| Total | 146 | 71 | 75 |

Encoding the 80 source goals produces 754 WD requests, reduced to 66 distinct goals with 688 reuses. Of these 66, 51 are automatic (77.3%). Shared WD goals belong to their first generating source goal in the per-operation table; later consumers are retained in the JSON dependencies. The 29 explicit source-WD commands invoke `zone_source_wd` and are not counted as import-time automation.

The run uses Lean 4.31.0, 20,000 heartbeats per import-time attempt and 200,000 for explicit proofs. No pending, skipped, admitted or unpublished obligations remain. Each published declaration's complete transitive axiom set is contained in `propext`, `Classical.choice`, and `Quot.sound`. This establishes kernel checking of the translated propositions, not verification of the source generator or translator.

`paper/ifs/validation/ZoneMonitor.{log,json,csv}` and `ZoneMonitor-manifest.json` retain the proof log, per-declaration evidence, operation counts, backend revision, source hashes and settings. An anonymized archival artifact remains to be prepared for submission.

Industrial experience is supplementary. No historical refactor baseline, disabled-feature experiment, full industrial benchmark campaign or mandatory refinement is part of this case.
