# BARReL — iFS 2027 regular research paper

Title: **BARReL: A modern backend for Atelier B in Lean**. Preserve this title.

This manuscript presents BARReL as a whole and is intended to become its main archival research reference. The ITP 2026 submission was rejected: it is not an accepted predecessor, and this is not an extension paper or a report of changes since a published version. The older manuscript is now in `paper/itp/`; it remains a useful source for the full framework account.

The writing target is a **regular research paper**, not a tool-paper recommendation. Contributions cover the B-to-Lean pipeline and mathematical library, contextual WD generation and explicit proof dependencies, extensible automation, and the interactive proof interface. WD sharing and implementation optimizations are parts of this design. They do not define the entire paper's contribution.

## Case study and evidence

The new case is **ZoneMonitor**, a completely proved machine for authorizing zones based on redundant sensor readings. Its partial reading map, quorum counts and guarded extrema create a natural WD workload. Batch updates require a preservation proof for unaffected zones. The B source is `specs/ZoneMonitor.mch`; its BARReL proof is `examples/ZoneMonitor.lean`.

See `CASE-STUDY-PLAN.md` for the design and implementation record. The complete POG contains 41 principal obligations and 39 source WD obligations. BARReL generates 754 WD requests, retains 66 distinct goals, and automatically discharges 51 of them (77.3%) with the explicitly supplied case-study helpers. All 146 retained obligations are proved and published; the transitive axiom audit permits only `propext`, `Classical.choice` and `Quot.sound`. JSON, CSV, source hashes and the successful proof log are in `validation/`.

Industrial experience can support a short, scoped scaling paragraph. The agreed scope does not require a full benchmark campaign, historical refactor comparison, disabled-feature experiments, edit-latency study, or mandatory refinement chain. Previously recorded synthetic timings are not paper results.

From the repository root, run `specs/zonemonitor/check.sh --regenerate` to regenerate the full source POG with Atelier B, build the backend and helper modules, prove the case, audit all published declarations and regenerate the counts. Omit `--regenerate` to use the retained POG without a native Atelier B installation. The full POG includes source WD checks for the read-only operations; BARReL's default machine-import path omits these. The earlier JobQueue and MinSearch logs remain separate historical checks.

## Venue and anonymity

Rules checked on 29 September 2026 against the [ETAPS joint call](https://etaps.org/2027/cfp/) and [iFS page](https://etaps.org/2027/conferences/ifs/):

- Regular research submissions use **double-blind review**.
- The long-paper limit is **16 pages plus at most 2 pages of references**, in Springer LNCS format.
- Submission is **15 October 2026, Anywhere on Earth**. Notification is 22 December 2026.
- A data availability statement is required in the proceedings version, immediately before references, outside the page limit. A provisional statement is included.
- Voluntary artifact submission is 11 January 2027; final paper is 25 January 2027.

`main.tex` uses anonymous authors and empty PDF author metadata. Keep `\anonymoustrue` for review; `\anonymousfalse` produces the identified author block copied from the original manuscript. The working-draft notice is controlled by `\draftnoticefalse`. These switches are not an artifact anonymity audit; an anonymized archival artifact remains to be deposited.

There is a [public June 2026 preprint](https://arxiv.org/abs/2606.20121) of the same BARReL research. Public availability is distinct from accepted archival publication. Its existence is recorded here for submission/disclosure decisions, without treating it as a separate predecessor in the research narrative. The manuscript does not claim first-ever public disclosure. Any eventual AI-use disclosure should reflect actual practice; the old blanket denial was not copied.

## Build and files

From `paper/ifs`, run:

```sh
latexmk
```

The local `.latexmkrc` uses **pdflatex**, BibTeX and `splncs04`; the output is `build/main.pdf`.

```sh
latexmk -pvc
latexmk -c
latexmk -outdir=build/template template/template.tex
```

Use only one continuous build process. The last command builds the reusable template from this directory.

- `main.tex`, `preamble.tex`, `sections/`: the manuscript and shared setup.
- `references.bib`: B, Lean, partiality and related mathematical toolkits.
- `CASE-STUDY-PLAN.md`: design and completed implementation record for the fresh machine.
- `template/template.tex`: reusable LNCS skeleton.
- `llncs.cls`, `splncs04.bst`: unmodified Springer files; provenance and hashes are in `TEMPLATE-PROVENANCE.md`.
- `validation/`: build/visual QA and earlier example-check logs, each with its evidence limits.

The iFS source is self-contained and does not input the earlier LIPIcs manuscript.

## Implementation sources and evidence boundaries

The inspected implementation revision is `7c3facb31bb69e077834206c6cb090d71e6c2fe2`. This identifies the source inspected; it is not a comparison baseline.

| Topic | Repository source |
| --- | --- |
| Context-closed WD goals | `../../Barrel/Encoder.lean:298` |
| WD for extrema/application/size/cardinality | `../../Barrel/Encoder.lean:243` |
| Direct arithmetic operators without those generated WD arguments | `../../Barrel/Encoder.lean:69` |
| Carrier representation | `../../POGReader/Parser.lean:27`, `../../POGReader/Extractor.lean:113` |
| Shared conditions within an import | `../../Barrel/Discharger.lean:37` |
| Extensible WD collections and automatic tactics | `../../Barrel/Tactics.lean:5` |
| Finite-image extrema rules for partial functions | `../../Barrel/Builtins/Arithmetic.lean:450` |
| Individual proof commands and completion | `../../Barrel/Discharger.lean:398`, `:432`, `:483` |
| Checked environment merge and reuse | `../../Barrel/Context.lean:44` |

The referenced chat [Refactor BARReL goal discharger](thread://01a0ec4e-4b9f-7e33-98da-42a35f85deeb?hostId=local) was read and checked against current code. Its features belong in the complete architecture description, not in a before/after publication narrative. The ITP reviews inform clarity, accurate related work and the strength of the new case; they do not determine a reduced tool-paper scope.

Relevant public sources checked while preparing the bibliography include [Russell](https://sozeau.gitlabpages.inria.fr/www/research/russell.en.html), the [Z Mathematical Toolkit](https://isa-afp.org/entries/Z_Toolkit.html), [Schmalz's thesis record](https://hdl.handle.net/20.500.11850/64337), and [Growing Mathlib](https://arxiv.org/abs/2508.21593).
