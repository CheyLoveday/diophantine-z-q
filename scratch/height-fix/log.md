# height-fix log

Base: wip/height-dict 15cc5a60, merged origin/main (0caafe66, STATUS.md only) -> 4d9056fc.

## 2026-11-16
- 13:20 `lake build ZInQKernel.Contrib.OneProof.HeightDictionary`: OK (12753 jobs). VERIFIED.
- Plan: new file ZInQKernel/Contrib/OneProof/PrintedFaltingsHeight.lean (namespace ZInQ.HeightFix), importing
  HeightDictionary. HeightDictionary.lean itself is not edited (javanpeykar-fix merged it).
- Fix1.lean compiles (VERIFIED): `eq_of_density` (two finite measures on a compact space with the same local
  densities in charts are equal), `DensAt`, `densAt_map`, `densAt_of_invariant`, `eq_of_densAt`,
  `isMulLeftInvariant_of_densAt`; defs `chartAt`, `HasFormDensityAt`, `IsFormMeasure`, `IsPrintedMetricSq`
  (existence AND uniqueness of the mass); `metrized_setup`, `isFormMeasure_iff` (invariance proved),
  `isPrintedMetricSq_iff` (printed metric = torusMetricSq for eta != 0).
