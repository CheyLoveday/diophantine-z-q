# r3-residual (2026-11-17)

**Result.** Height-dict's step R3 ("uniformization clauses ⇒ biholomorphic") is now a Lean theorem whose
statement mentions no uniformization. The three fields `bostLowerBoundPrinted`, `gaudronRemondThm14Printed`
and `javanpeykarPrintedMapHF` are proved from leaves over the print's stable height, i.e. the metric
integrated over the complex manifold `A_τ(ℂ)^an` with densities in every holomorphic chart. Extra hypothesis:
T35 only (`mumfordTorsionAlgClosed`). Against the 11-17 re-rating this is −3 GLUE; on this base's kinds.tsv
it is −1 (16/18 → 17/17).

**What compiles** (standard axioms), in the new file `ZInQKernel/Contrib/OneProof/AnalyticStableHeight.lean`:
- `IsHolChart`: holomorphic charts, defined from the algebraic coordinates alone.
- `exists_holChart` / `exists_holChart_at`: algebraic coordinates are holomorphic charts, and charts exist at
  every point.
- `holChart_transition`: the charts form a complex atlas.
- `unif_holChart`: every analytic uniformization is a local biholomorphism.
- `regular_holo_in_holChart`: regular functions are holomorphic in these charts.
- `jacobian_bounds` and `hasAnFormDensityAt_iff`: the density read in any holomorphic chart is equivalent to
  height-fix's `HasFormDensityAt`, so the density does not depend on the chart.
- `isAnStableHeight_iff`: the new height equals height-fix's height.
- New leaves `BostLowerBoundAn`, `GaudronRemondThm14An`, `JavanpeykarAnMin`. The last uses the printed
  `deg_B`, which also removes Javanpeykar's given-degree step. Converse lemmas show none is stronger than the
  row it replaces.
- `#discharges` is recorded, the autofold spec is written, and the dry-run module compiles.

**What remains.**
- Gaudron–Rémond: `isogDeg = #ker(K̄)` against GR's degree needs `#ker(K̄) ≤ deg`. Not proved, so the GR row
  may stay GLUE on that step alone.
- Optional: identify `IsHolChart` with the vendored `ComplexPoint` manifold atlas.
- Optional: Pazuki's `CPts` uniformization, same argument.

Report: docs/research/r3-residual.md. Scratch: scratch/r3-residual/.
