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
- 04:30-04:45 scratch/pic-dict/Transport.lean (VERIFIED, compiles, standard axioms): `pullbackObjUnitIso_comp`
  (pOUI compatible with pullbackComp, via the adjunction mate `conjugateEquiv_pullbackComp_inv`),
  pullbackComp coherence lemmas, `coherence_I`, `coherence_II`, `wf_transport` (Mumford's formula is carried by
  any `g` with `t' ≫ g = g ≫ t`, `g ≫ m = m ≫ g` to `g.appTop` of the formula), `wf_iso`, and
  `weilFormulaGaloisEx` (the Galois clause, transport along `1 × Spec σ`). Uses the vendored
  `pullbackObjUnitIso_conj_app_top` (FreeGeneratorPullback.lean).
- Merged into ZInQKernel/Contrib/OneProof/PicDictionary.lean; `lake build ZInQKernel.Contrib.OneProof.PicDictionary`
  succeeds. `#discharges` (scratch/pic-dict/discharges.txt):
  `DISCHARGES [OpenAddedLeaves17.weilPairingMumford] by PicDict.weilPairingMumford_of_printed` still assumes the
  9 Mumford-type leaves and `T09Pic.PhiAmpleIsogeny`; standard axioms.
- autofold dry-run (scratch/pic-dict/autofold.json, weilPairingMumford only, no --allow-rise):
  `strict count: 40/8 on 48 -> 48/8 on 56; strictest 39/9 -> 48/8`; with the three rows re-rated
  consequence GLUE/GLUE as cove-80 does in lf31 (temporary kinds.tsv edit, restored):
  `strict count: 37/11 on 48 -> 46/10 on 56; strictest 37/11 -> 46/10` (-1 strict, -1 strictest).
  The dry-run module compiles (`sixContactMin_of_open35`, standard axioms).
- ~05:00 `finiteOfFiniteKerPts` proved (scratch/pic-dict/Finite.lean; merged). `phiAmpleIsogeny_of_printed` now takes
  4 leaves (`MumfordKLFinite`, `MumfordPhiSurjective`, `AmpleBaseChangeAlgClosure`, composite `PicZeroPtsTranslInv`).
- ~05:10 `mumfordWeilDual_of_pairing : MumfordWeilPairing → MumfordWeilDual` proved by `Transport.wf_transport`
  along `f × 1` (scratch/pic-dict/Dual.lean; merged). `weilPairingMumford_of_printed` now takes 8 leaves +
  `PhiAmpleIsogeny`. VERIFIED: module builds; #discharges updated; dry-runs:
  weil only `40/8 on 48 -> 47/8 on 55; strictest 39/9 -> 47/8` (lf31 rating: `37/11 -> 45/10; 37/11 -> 45/10`);
  both rows `40/8 -> 47/9 on 56; strictest 39/9 -> 47/9` (lf31: `37/11 -> 46/10; 37/11 -> 46/10`).
  Both dry-run modules compile (sixContactMin_of_open35, standard axioms).
- ~05:15 `mumfordWeilCompat_of_pairing` proved (Transport.wf_transport₂, coherence_III; scratch/pic-dict/Compat.lean).
- ~05:25 AC restatement (scratch/pic-dict/AlgClosed.lean, merged): leaves for `k` algebraically closed and
  `X : AbVar k` with `X(k) = 𝟙_ ⟶ X.X`, `t_x = lift (𝟙, toUnit ≫ x) ≫ μ`, `n_X = 𝟙^n`, Mumford's `Pic⁰` =
  translation-invariant classes, Mumford's formula: `MumfordSquareAC`, `MumfordMulNPicZeroAC`,
  `MumfordPhiSurjectiveAC`, `MumfordWeilPairingAC`, `MumfordWeilNondegAC`, `MumfordWeilAltAC`, `MumfordKLFiniteAC`.
  Bridge to `A_K̄ := Over.pullback (Spec K̄ → Spec K)` of `A` proved: `tr_pts` (translations), `mul_AKbar`,
  `pts_mul`, `pts` bijective, `formula_bridge`; `*_of_ac` for each leaf. VERIFIED, standard axioms.
- Final: `weilPairingMumford_of_ac` (7 leaves + phiAmpleIsogeny), `phiAmpleIsogeny_of_ac` (4 leaves, one composite).
  #discharges: 11 lines discharge (both forms listed). Dry-runs (scratch/pic-dict/autofold.json):
  `40/8 on 48 -> 46/8 on 54; strictest 39/9 -> 46/8`; lf31 rating `37/11 -> 44/10; strictest 37/11 -> 44/10`.
  Both rows: `40/8 -> 46/9 on 55; 39/9 -> 46/9`; lf31 `37/11 -> 45/10; 37/11 -> 45/10`. Dry-run modules compile.
