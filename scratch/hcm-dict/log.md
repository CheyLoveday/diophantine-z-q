# hcm-dict results log

Base: wip/leaf-fold33b 4da8d4f32 (origin/main merged: already up to date).
Build tree: reflink copy of ~/dzq-wt/leaf-fold33b/.lake/build and lean/.lake/build (same commit, Main.lean identical).

## Target
`T5Glue.ShimuraMainCM` (ZInQKernel/Contrib/OneProof/RingClassLattice.lean:912), frozenTarget binder `hCM`;
kinds.tsv row 37: consequence / GLUE / GLUE.

## Inputs found (VERIFIED, read in tree)
- Vendored FLT (Apache-2.0) `PeriodPair.isUniformization_toPoint` : `(℘, ℘'/2)` is a surjective group hom
  `ℂ → L.weierstrassCurve(ℂ)` with kernel exactly `L.lattice` (`y² = x³ − g₂/4·x − g₃/4`), built in tree.
- `PeriodPair.discriminant_ne_zero`, `PeriodPair.exists_variableChange_smul_weierstrassCurve_eq` (vendored, built).
- Mathlib `PeriodPair.analyticOnNhd_weierstrassP`, `analyticOnNhd_derivWeierstrassP`, `deriv_weierstrassP`,
  `DiscreteTopology L.lattice`.
- `T5Glue.IsScale` + `.g₂ .g₃ .weierstrassP .derivWeierstrassP` (RingClassLattice.lean §1).
- Local holomorphic lift through `℘` (vendored S_PeriodPair_exists_differentiable..., ModularCurve
  `kw_surgehgf4_hH2d_...`): template for the local lift step.
