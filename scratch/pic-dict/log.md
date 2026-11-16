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
- 04:00 build finished (62 min wall, exit 0).
- 04:45 scratch/pic-dict/Core.lean compiles (`lake env lean`, ~10 s after imports). VERIFIED, axioms
  [propext, Classical.choice, Quot.sound] for:
  - `PicDict.picPointsAlgClosed : T09Pic.PicPointsAlgClosed` (L5 is a theorem). Proof: every fppf covering sieve of a
    scheme contains every point with values in an algebraically closed field (induction on `Precoverage.Saturate`,
    Nullstellensatz `pointOfClosedPoint`), then Mathlib's `isLocallyInjective_toSheafify'` /
    `isLocallySurjective_toSheafify'`.
  - dictionary glue: `toPicardFunctor_picClass`, `picClass_mul`, `picClass_injective`, `picClass_gal`,
    `picClass_dual`, `picClass_phiL` (M_{λ_L x} = t_x^*L_K̄ ⊗ L_K̄⁻¹), `phiPt_translInv` (from the square),
    `exists_lift_pt`, `exists_pt_of_isClosed`, `surjective_of_forall_pt`.
  - `weilPairingMumford_of_printed` (9 Mumford-type leaves at A_K̄ + `WeilFormulaGalois` glue + field
    `PhiAmpleIsogeny`) : `T09Pic.WeilPairingMumford`.
  - `phiAmpleIsogeny_of_printed` (`MumfordKLFinite`, `MumfordPhiSurjective`, `AmpleBaseChangeAlgClosure`,
    `PicZeroPtsTranslInv` (composite), `FiniteOfFiniteKerPts` (glue)) : `T09Pic.PhiAmpleIsogeny`.
