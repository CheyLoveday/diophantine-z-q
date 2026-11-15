# c-to-printed results log

Base e38375b3. Compile harness: `scratch/c-to-printed/run.sh FILE.lean` (lean with LEAN_PATH on ~/ctp-lib, a copy
of the e38375b3 build). One Lean process at a time.

- T0.lean: `import ZInQKernel.OneProof.H.TailZ14; #check @ReductGlue.NeronLocalizesDVR` compiles (VERIFIED, 4.7 s).

## Field statements (VERIFIED, read in ZInQKernel/OneProof/H/)
- shimuraFamily: `QMSplit.Moduli.ShimuraFamily`, TailU.lean:1952.
- semistableNeronBaseChange: `ZInQ.HeightSplit.SemistableNeronBaseChange`, TailY.lean:145.
- faltingsLemma5BC: `ZInQ.HeightSplit.FaltingsLemma5BC`, TailY.lean:609 (base form FaltingsLemma5 :560).
- neronLocalizesDVR: `ReductGlue.NeronLocalizesDVR`, TailZ14.lean:882.

## Part N: neronLocalizesDVR (Neron.lean)
- Leaf `CToPrinted.BLR_1_2_4`: BLR 1.2 Prop. 4 (UNVERIFIED number/wording) over any Dedekind domain R with
  fraction field K, X smooth separated quasi-compact over Spec R: `IsNeronModelOver R K X ↔ ∀ maximal 𝔭, ∀ R𝔭 with
  IsLocalization.AtPrime R𝔭 𝔭 (and R → R𝔭 → K), IsNeronModelOver R𝔭 K (X ×_R R𝔭)`.
- Definition `IsNeronModelOver R K X` (BLR 1.2 Def. 1): smooth, separated, locally finite type, quasi-compact, and
  `Hom_R(Y,X) → Hom_K(Y_K,X_K)` bijective for every smooth R-scheme Y. Mathlib objects only.
- Glue proved: `isLocalization_center` (a DVR O of a number field L is `IsLocalization.AtPrime O (center O)` for
  `toOL`), `isNeronModelOver_of` (kernel `GroupModel.IsNeronModel` ⇒ printed property of `𝒩.G`).
- `neronLocalizesDVR_of_printed : BLR_1_2_4 → ReductGlue.NeronLocalizesDVR` COMPILES, axioms
  [propext, Classical.choice, Quot.sound] (VERIFIED, ~5 s).

## Part S: semistableNeronBaseChange (SS2) (CToPrinted.lean, Neron.lean renamed)
- `semistableNeronBaseChange_of_printedBLR : BLR_1_2_4 → IdentityComponentBaseChangeDVR → IdentityComponentOL →
  OpenImmersionOfLocal → SemistableNeronBaseChange` COMPILES (VERIFIED; reduct-glue's proof with Part N).
- New definition `idCompSet G` (G⁰ as a set: x in the connected component of e(f x) in f⁻¹{f x}); Mathlib has no
  identity component over a base.
- Printed-form leaves stated (compile as defs): `SGA3_VIB_3_10` (G smooth group over S ⇒ IsOpen idCompSet),
  `SGA7_IX_3_3` (c : 𝒩 ×_O O' → 𝒩' hom with iso generic fibre, U open = idCompSet ⇒ U.ι ≫ c open immersion with
  range idCompSet 𝒩'), `EGAIV_8_10_5_openImm` (limit setting of the kernel's EGAIV_8_10_5_xii, open immersions).
- Named glue (unproved): `IdentityComponentGroupModel`, `IdentityComponentFromPrinted`, `OpenImmersionLocalization`.
- `semistableNeronBaseChange_of_printed` (4 printed leaves + 3 glue ⇒ SS2) COMPILES, standard axioms (VERIFIED).

## Part F: faltingsLemma5BC (CToPrinted.lean)
- Definitions: `kerScheme f = pullback f.left η_Y.left` (G = ker φ_𝒩), `kerUnit f hf` (unit section, from
  IsMonHom.one_hom), `kerOmegaLog f hf = ∑ᶠ P, log #(ker(s.stalkMap P)).Cotangent` (log #s*Ω¹_{G/S}, stalkwise
  conormal; Mathlib has no sheaf of relative differentials on schemes), `ExtendsIsogeny`.
- Leaves: `FaltingsLemma5Printed` (Faltings 1983 Lemma 5 identity h(B) = h(A) + ½ log deg φ − [K:ℚ]⁻¹ log #s*Ω¹,
  UNVERIFIED), `RaynaudKernelBound` (log #s*Ω¹ ≤ [K:ℚ] log deg φ, Raynaud Ast. 127 VII 2.1.3, UNVERIFIED).
- Glue proved: `exists_extension` (Néron extension of φ is a homomorphism; reduct-glue's isMonHom_of_ext),
  `kerOmegaLog_nonneg`.
- `faltingsLemma5_of_printed`, `faltingsLemma5BC_of_printed` COMPILE, standard axioms (VERIFIED).

## Part H: shimuraFamily (Shimura.lean)
- Shimura.lean = verbatim copy of scratch/shimura-split/ShimuraFam.lean (still compiles at e38375b3, VERIFIED) +
  section CToPrinted.Shimura.
- `InGamma3 x := InO x ∧ x * star x = 1 ∧ ∃ y, InO y ∧ x = 1 + 3y` (Γ_S = B^×_+ ∩ K₃).
- Leaf `ShimuraMainThmIY3`: fine witness (Y,Φ) with R1fpProps, yτ with IsShimuraHolFamily (moduli clause +
  holomorphic), and fibres of yτ = Γ(3)-orbits (GL(2,ℝ) action through BPAnalytic.QM.iota). Main Thm I minus
  reciprocity (needs global Artin map: not in Mathlib 4.35) and minus surjectivity onto V_S(ℂ) (needs V_S over
  ℚ(ζ₃) + Deligne's comparison).
- `shimuraFamily_of_mainThmI : ShimuraMainThmIY3 → HDec.QMSplit.Moduli.ShimuraFamily` COMPILES, standard axioms
  (VERIFIED); verbatim copy check `example : ShimuraFamily = HDec.QMSplit.Moduli.ShimuraFamily := rfl` passes.

## Part S, glue `OpenImmersionLocalization` PROVED (CToPrinted.lean, section OIL)
- `isOpenImmersion_pb_pb_iff` (base change along u then v ~ along u ≫ v, via Over.pullbackComp).
- Index `Idx 𝔭 = 𝔭.primeCompl` preordered by divisibility (directed, nonempty); `ringDiagP`, `specDiagP`;
  `ringCoconeOIsColimit` (O = colim_{a∉𝔭} 𝓞_L[1/a], via IsLocalization + mem_iff_exists), `specConeOIsLimit`.
- `exists_away_of_dvr`: EGA IV 8.10.5 at one DVR gives s ∉ 𝔭_O with base change to 𝓞_L[1/s] an open immersion.
- `openImmersionLocalization : EGAIV_8_10_5_openImm → ReductGlue.OpenImmersionOfLocal` COMPILES (open cover of
  Y by Y ×_S D(s_𝔭) via Cover.mkOfCovers; IsZariskiLocalAtTarget.of_openCover; pullbackRightPullbackFstIso).
- `semistableNeronBaseChange_of_printed'` (4 printed leaves + 2 glue) COMPILES. All 7 #print axioms standard.
