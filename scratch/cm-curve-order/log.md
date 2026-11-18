# cm-curve-order results

- VERIFIED: base `664e00417`; merged refreshed `origin/wip/cm-fibre-split` at `fe5ad6a96` (includes requested `324f0655a`). Checked `origin/main` at `15c9e93d3`: no CMFoldRebase in its history; target remains open77. No fetch or push.
- VERIFIED (source): `CMCurveOrder` at `324f0655a` has no dimension hypothesis on A; the merged version adds `A.dim = 2`. `Statement.lean` copies the original body verbatim; the new module proves that body and specializes it to the consumer's unchanged surface statement.
- VERIFIED (source): T6 `HomFreeFiniteC` includes the bound on the rank of `End(E)`, in addition to finiteness and freeness. `diophantine_zq.tex` `thm:height` proof L582–586 uses the geometric order without citation.
