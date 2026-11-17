# r3-residual log

## Setup (2026-11-17 01:20 PST)
- Base e1b31749 (wip/r3-residual). Built `ZInQKernel.Contrib.OneProof.PrintedStableHeight` and
  `ZInQKernel.Contrib.OneProof.JavanpeykarRebase` (lake build OK, ~2 min, cached).
- Targets (VERIFIED, read): `ZInQ.HeightFix.BostLowerBoundPrinted` (PrintedStableHeight.lean:670),
  `ZInQ.HeightFix.GaudronRemondThm14Printed` (:679), `JavanpeykarRebase.JavanpeykarPrintedMap`
  (JavanpeykarRebase.lean:196). All three take `IsPrintedStableHeight A x` in hypothesis position.
- `HasFormDensityAt` (:240) is Φ-free as a definition; Φ enters only the *proofs* that the algebraic
  charts `chartAt F p` are charts (`exists_chart`, through `M.arch τ`) and holomorphic
  (`chartAt_comp_hasStrictFDerivAt`, hypothesis `hΦ`).

## Plan
1. Φ-free definition of the holomorphic charts of A_τ(ℂ)^an (`IsHolChart`: biholomorphic to the
   translated algebraic coordinates at every point of the domain) and the print's measure
   `(i/2)^g η̃ ∧ η̄̃` in *every* holomorphic chart (`HasAnFormDensityAt`, coefficient
   `l · det D(F_p ∘ φ⁻¹)(φ p)`).
2. Prove (T35): algebraic charts are holomorphic charts; transitions between holomorphic charts are
   biholomorphic; every analytic uniformization is a local biholomorphism; `IsAnFormMeasure ↔ IsFormMeasure`
   (Jacobian change of variables, Mathlib `addHaar_image_le_mul_of_det_lt`).
3. Leaves over `IsAnStableHeight`; consumers through `isAnStableHeight_iff`.

## Results (all VERIFIED: compiled with `lake env lean`, standard axioms)
- 01:35 `exists_chart_of_lift` (generic IFT chart on a uniformized group) compiles.
- 01:40 `IsHolChart` (Φ-free def) + `chart_comp_unif` + `exists_holChart` compile; axioms standard.
- 01:45 `jacobian_bounds` (Mathlib `addHaar_image_le_mul_of_det_lt` / `mul_le_addHaar_image_of_lt_det`),
  `HasAnFormDensityAt`, `IsAnFormMeasure`, `IsAnMetricSq`, `IsAnStableHeight` compile.
- 01:50 `hasAnFormDensityAt_iff`, `isAnFormMeasure_iff`, `isAnMetricSq_iff`, `isAnStableHeight_iff` compile
  (hypotheses: T35, `A.dim = g`, `η ≠ 0`).
- leaves `BostLowerBoundAn`, `GaudronRemondThm14An`, `JavanpeykarAnMap`, `JavanpeykarAnMin`; consumers
  `bostLowerBoundPrinted_of_an`, `gaudronRemondThm14Printed_of_an`, `javanpeykarPrintedMap_of_an(_min)`;
  converses `*_of_printed`, `javanpeykarAnMin_of_map` compile.
- `chart_comp_of`, `exists_algCoord`, `exists_holChart_at`, `holChart_transition`, `unif_holChart`,
  `holo_in_chart_of_lift`, `regular_holo_in_holChart` compile.
- 02:10 `ZInQKernel/Contrib/OneProof/AnalyticStableHeight.lean` = scratch R3.lean + header; `lake build
  +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.AnalyticStableHeight`
  OK (14274 jobs, 12 min). `#discharges` (discharges.txt):
  bostLowerBoundPrinted by bostLowerBoundPrinted_of_an, assumes [BostLowerBoundAn, MumfordTorsionAlgClosed];
  gaudronRemondThm14Printed by gaudronRemondThm14Printed_of_an, assumes [GaudronRemondThm14An, MumfordTorsionAlgClosed];
  javanpeykarPrintedMapHF by javanpeykarPrintedMap_of_an_min, assumes [JavanpeykarAnMin, MumfordTorsionAlgClosed];
  all axioms [propext, Classical.choice, Quot.sound].
- autofold dry run: `strict count: 16/18 on 34 -> 17/17 on 34; strictest 16/18 -> 17/17` (this base rates
  bost/GR Printed LEAF; against the 11-17 re-rating, all three GLUE, the fold is -3 GLUE). Dry-run module
  (FoldDryRun.lean) compiles; `sixContactMin_of_open56` standard axioms.
- Not done: GR `isogDeg = #ker(K̄)` vs printed degree (needs `#ker(K̄) ≤ deg`, finite flat group schemes);
  link of `IsHolChart` with the vendored Paul-Lez `ComplexPoint` manifold (bridge Pts τ ≃ CPt(𝒢_τ)).
