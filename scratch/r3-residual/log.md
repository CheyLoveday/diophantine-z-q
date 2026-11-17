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
