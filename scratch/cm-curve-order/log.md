# cm-curve-order results

- VERIFIED: base `664e00417`; merged refreshed `origin/wip/cm-fibre-split` at `fe5ad6a96` (includes requested `324f0655a`). Checked `origin/main` at `15c9e93d3`: no CMFoldRebase in its history; target remains open77. No fetch or push.
- VERIFIED (source): `CMCurveOrder` at `324f0655a` has no dimension hypothesis on A; the merged version adds `A.dim = 2`. `Statement.lean` copies the original body verbatim; the new module proves that body and specializes it to the consumer's unchanged surface statement.
- VERIFIED (source): T6 `HomFreeFiniteC` includes the bound on the rank of `End(E)`, in addition to finiteness and freeness. `diophantine_zq.tex` `thm:height` proof L582–586 uses the geometric order without citation.
- VERIFIED (compiled, EXIT 0): `CMCurveOrder.lean` and generated `CMCurveOrder/Fold.lean`, checked with sequential `lake env lean -o`. Cached imports came from the two merged worktrees. The rank comparison uses explicit natural-number coercions to the type of T6's bound.
- VERIFIED (source): the open4 entry supplies `cmFibreSplit_of_curveOrder324` with G2 and the existing inputs; open77's GR9 path and unchanged bundle conversions carry the four remaining CM fields. The generated fold is deterministic (`cmp`).
