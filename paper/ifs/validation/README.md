# ZoneMonitor validation — 30 September 2026

`specs/zonemonitor/check.sh --regenerate` passed end to end: native Atelier B generation with source WD, `lake build`, helper-module compilation, full BARReL proof, `qed`, transitive axiom audit and count export. The case-study proof emitted no warnings or errors.

| Obligation class | Total | Automatic at import | Explicit proof commands |
| --- | ---: | ---: | ---: |
| Principal | 41 | 10 | 31 |
| Atelier B source WD | 39 | 10 | 29 |
| BARReL-generated WD | 66 | 51 | 15 |
| Total | 146 | 71 | 75 |

The 66 generated WD goals result from 754 requests, with 688 reuses. The import uses 20,000 heartbeats per attempt and the explicit `ZoneMonitorAutomation` extension; interactive proofs use 200,000. These figures describe that configuration, not unextended stock automation. The source-WD proof commands invoke `zone_source_wd` explicitly and are counted as explicit commands.

- `ZoneMonitor.log`: successful proof and audit output.
- `ZoneMonitor.json`: each published obligation, automatic/manual status, WD dependencies and complete transitive axiom set.
- `ZoneMonitor.csv`: per-operation counts. Shared WD goals belong to their first generating source goal.
- `ZoneMonitor-manifest.json`: dependency version, backend revision, source hashes, settings and totals.

The exporter refuses pending, skipped, admitted or unpublished obligations and rejects every axiom except `propext`, `Classical.choice` and `Quot.sound`. This checks the actual translated declarations; it does not verify Atelier B's generator or BARReL's translator.

## Earlier existing-example checks — 29 September 2026

Repository revision: `7c3facb31bb69e077834206c6cb090d71e6c2fe2`.
Lean toolchain: `leanprover/lean4:v4.31.0`; Mathlib revision specified by the project: `v4.31.0`.

Executed from the repository root against existing compiled imports, with a 90-second limit each:

```sh
timeout --kill-after=5s 90s lake env lean examples/JobQueue.lean
timeout --kill-after=5s 90s lake env lean examples/MinSearch.lean
```

| Input | Result | Diagnostics |
| --- | --- | --- |
| JobQueue | Exit 0; 3/15 subgoals automatic, 12 individual proof commands, final `qed` | Three unused-variable warnings; no error or sorry warning |
| MinSearch | Exit 0; 27 individual proof commands across three imports, all three `qed` commands | No warnings or errors |

The logs are retained in this directory. The two example sources contained no `sorry`, `admit` or custom `axiom`. These earlier checks did not include an exhaustive transitive axiom audit or a fresh full-library build. They are separate from ZoneMonitor's evidence. Relevant compiled imports had timestamps newer than their source files.

Input SHA-256:

```text
d376ecbffcf003373d4d6f1ff8a2ca3e93be42ff35793614d13dfade6be96a11  examples/JobQueue.lean
428dbece9dd110920075ba0fd52abd8dcc8965be34bdf2cad8bb9fbc00d72e76  examples/MinSearch.lean
```
