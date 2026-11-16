# pic-dict results log

Base e22df37cd (leaf-fold30). Rows: `T09Pic.PicZeroAbVar` (TailZ24:302), `T09Pic.PhiAmpleIsogeny` (TailZ24:366),
`T09Pic.WeilPairingMumford` (TailZ24:708); all three are fields of `HDec.HSyn.OpenAddedLeaves17` (TailZ34:111).

## 2026-11-16
- 02:59 started `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` (no prebuilt tree on this
  base anywhere on the host; output scratch/pic-dict/build.out).
- Findings (VERIFIED, read in source): `picardFunctor f` is `presheafToSheaf (fppfTopology.over S)` of
  `picardPresheaf f` (T ↦ Pic(X ×_S T), no quotient by Pic(T)); `toPicardFunctor` = `toSheafify`. Mathlib has
  `Presheaf.isLocallyInjective_toSheafify'` / `isLocallySurjective_toSheafify'` and
  `pointOfClosedPoint` (AlgClosed/Basic.lean). So L5 should be provable: every fppf covering sieve of Spec K̄
  contains the identity.
- The vendored library proves Kleiman 9.2.5 in general form (`Picard/Descent.lean`,
  `isIso_picardFunctorNormalized_ι_comp_toPicardFunctor`, under `IsIso pushforwardUnitMap` universally); not needed
  for L5.
