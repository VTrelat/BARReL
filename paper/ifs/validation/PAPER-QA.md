# Preliminary paper QA - 30 September 2026

- `latexmk` built `build/main.pdf` using the local pdflatex/BibTeX configuration: 16 pages total. The body ends on page 15; the data availability statement follows, and references occupy parts of pages 15 and 16. This is within the 16-page body plus 2-page reference limit.
- The final log contains no LaTeX warnings, undefined citations/references, overfull boxes or underfull boxes.
- All 16 final pages were rendered with Poppler and visually inspected. The two tables, B/Lean listings, mathematical symbols, page transitions and reference list render without clipping or overlap.
- The exact original title, `BARReL: A modern backend for Atelier B in Lean`, appears in the manuscript and PDF metadata. The manuscript targets a regular research paper on the complete framework.
- Partial-function spaces use the B-specific barred arrow macro copied from the original manuscript. B source listings retain ASCII `+->`; no generic partial-function harpoon is used.
- PDF author metadata is empty; the title block and running heads are anonymous. The draft notice is dated 30 September 2026. This is not a complete submission-artifact anonymity audit.
- All PDF external-link annotations were checked for malformed backslash escapes; none were found. This is a syntax check, not a live reachability check of every URL.
- The reusable LNCS template was successfully built on 29 September with `latexmk -outdir=build/template template/template.tex`; its source was not changed in this revision.
- ZoneMonitor is now implemented and completely proved in BARReL. `specs/zonemonitor/check.sh --regenerate` passed native full-POG generation, backend/helper builds, proof completion, transitive axiom audit and count export. The manuscript's 41 principal, 39 source-WD and 66 generated-WD counts match the retained evidence. All 146 obligations are published without admissions.
- The reported 51/66 generated-WD automatic proofs use the explicitly documented case-study extension. The 29 source-WD commands invoking `zone_source_wd` are counted as explicit commands. No stock-automation comparison is claimed.
- An independent source/evidence review checked the manuscript counts, manifest hashes, actual proof excerpt, completion status, axiom sets and B notation. Its two findings were corrected: prospective workflow language and misclassification of the five initialization goals as preservation goals.
- No refactor comparison or full industrial benchmark campaign is included. Industrial evidence remains supplementary.
- Earlier JobQueue and MinSearch logs were retained separately and are not ZoneMonitor evidence.
- Changes cover `paper/ifs`, the new ZoneMonitor source/POG/scripts and its Lean modules. The concurrent relocation of the older manuscript to `paper/itp` was preserved. No BARReL core changes were needed.
- An anonymized archival artifact remains to be deposited. The manuscript remains a working draft, not a claim of submission readiness.
