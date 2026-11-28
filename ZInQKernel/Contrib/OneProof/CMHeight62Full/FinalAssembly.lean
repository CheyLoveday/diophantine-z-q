import ZInQKernel.Contrib.OneProof.CMHeight62Full.TreeStep7
import ZInQKernel.Contrib.OneProof.CMHeight62Full.TreeH3
import ZInQKernel.Contrib.OneProof.CMHeight62Full.PlaceAssembly2
import ZInQKernel.Contrib.OneProof.CMHeight62Full.CentreData
import ZInQKernel.Contrib.OneProof.CMHeight62Full.RelDimOne

/-!
# cmHeight62 (finite place): the final assembly

This file discharges the two open inputs of `TreeStep7.step7`.

* `shortComparisonInput`: `ShortComparisonInput` from the tree instance of item H3
  (`treeH3_n11Inst`): `X' = ι(x)` and `Y' = ι(y)` satisfy the base-changed short equation, have
  pole orders two and three at the identity place and no other pole, and `t_L = −X'/Y'`.
* `localAssemblyCore`: `LocalAssemblyCore` from the reduced per-place assembly
  `localComparison_reduced`. The fraction field `Ω` of the generic stalk that H2 gives is also a
  fraction field of the local ring `A` of the chart (the generic stalk is `A` localized at the
  prime `(t)`, node L2 (a)), and the inputs are moved along `Frac A ≅ Ω`. The centre data `hL1`
  is `CentreData.exists_centre_data` for `Frac A`. Its inputs are discharged here: the
  transcendence degree of `κ_w` (`SpecialFibreGap.trdegLeOne_specialFibreValuation`), the base
  map at the generic point (from the chart's compatibility with the structure map), the generic
  subring, and the horizontal subrings (a valuation subring containing `R = (𝓞_L)_s` and the
  inverse of an element of `s` contains `L`). The group model is smooth of relative dimension one
  (`GroupModel.smoothOfRelativeDimension_one`) and irreducible
  (`irreducibleSpace_of_isIrreducible_genericFibre`), and reduced (`groupModel_isReduced`: it is
  flat over `𝓞_L` with reduced generic fibre `E_L`, which is scheme-theoretically dense), hence
  integral.
* `step7_unconditional : Step7` and `cmHeight62_unconditional : CMHeight62`, with no hypotheses.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory IsLocalRing
open ZInQ.DefFaltings WeierstrassCurve
open PlaceAssembly PlaceAssembly2 SpecialFibreValuation SpecialFibreFunctionField

/-! ## 1. Algebraic glue -/

section Glue

/-- A field `Ω` that is a fraction field of a localization `S = M⁻¹A` of a domain `A` is a
fraction field of `A`. -/
theorem fa_isFractionRing_of_isLocalization {A Ω : Type*} [CommRing A] [IsDomain A] [Field Ω]
    [Algebra A Ω] (M : Submonoid A) (S : Type*) [CommRing S] [Algebra A S] [Algebra S Ω]
    [IsScalarTower A S Ω] [IsLocalization M S] [IsFractionRing S Ω]
    (hM : M ≤ nonZeroDivisors A) : IsFractionRing A Ω := by
  have hinj : Function.Injective (algebraMap A Ω) := by
    rw [IsScalarTower.algebraMap_eq A S Ω]
    exact (IsFractionRing.injective S Ω).comp (IsLocalization.injective S hM)
  have : FaithfulSMul A Ω := (faithfulSMul_iff_algebraMap_injective A Ω).2 hinj
  refine IsFractionRing.of_field A Ω (fun z => ?_)
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := S) z
  obtain ⟨⟨r₁, m₁⟩, h₁⟩ := IsLocalization.surj M x
  obtain ⟨⟨r₂, m₂⟩, h₂⟩ := IsLocalization.surj M y
  have e₁ := congrArg (algebraMap S Ω) h₁
  have e₂ := congrArg (algebraMap S Ω) h₂
  simp only [map_mul, ← IsScalarTower.algebraMap_apply] at e₁ e₂
  have hm : algebraMap A Ω (m₁ : A) * algebraMap A Ω (m₂ : A) ≠ 0 := by
    rw [← map_mul]
    exact (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero (hM (M.mul_mem m₁.2 m₂.2)))
  refine ⟨r₁ * m₂, m₁ * r₂, ?_⟩
  rw [map_mul, map_mul, ← e₁, ← e₂]
  have key : ∀ X Y M₁ M₂ : Ω, M₁ * M₂ ≠ 0 → X / Y = X * M₁ * M₂ / (M₁ * (Y * M₂)) := by
    intro X Y M₁ M₂ h
    rw [show X * M₁ * M₂ = X * (M₁ * M₂) by ring, show M₁ * (Y * M₂) = Y * (M₁ * M₂) by ring,
      mul_div_mul_right _ _ h]
  exact key _ _ _ _ hm

/-- The localization of a domain at a prime maps to its fraction field, compatibly. -/
theorem fa_exists_atPrime_algebra (R : Type*) [CommRing R] [IsDomain R] (p : Ideal R)
    [p.IsPrime] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    ∃ (_ : Algebra (Localization.AtPrime p) K), IsScalarTower R (Localization.AtPrime p) K := by
  have hg : ∀ y : p.primeCompl, IsUnit (algebraMap R K (y : R)) := fun y =>
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2
      (fun h0 => (Ideal.mem_primeCompl_iff.1 y.2) (by rw [h0]; exact p.zero_mem)))
  letI : Algebra (Localization.AtPrime p) K :=
    (IsLocalization.lift (S := Localization.AtPrime p) hg).toAlgebra
  exact ⟨this, IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hg x).symm)⟩

/-- **A fraction field of `D ≅ A_𝔮` as a fraction field of `A`.** Let `χ : A_𝔮 ≅ D` and `Ω` a
fraction field of `D` with an `L`-algebra structure compatible with `R → A` and `R → L`. Then `Ω`
is a fraction field of `A` (through `χ`), compatibly with `R`, and the image of `D` in `Ω` is the
set of `g` with `s g = r` for `r, s ∈ A`, `s ∉ 𝔮`. -/
theorem fa_exists_omegaPackage {R A D Ω L : Type*} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] (𝔮 : Ideal A) [𝔮.IsPrime] [CommRing D] (χ : Localization.AtPrime 𝔮 ≃+* D)
    [Field Ω] [Algebra D Ω] [IsFractionRing D Ω] [Field L] [Algebra R L] [Algebra L Ω]
    (hc : ∀ r : R,
      algebraMap D Ω (χ (algebraMap A (Localization.AtPrime 𝔮) (algebraMap R A r))) =
        algebraMap L Ω (algebraMap R L r)) :
    ∃ (_ : Algebra A Ω) (_ : IsFractionRing A Ω) (_ : Algebra R Ω) (_ : IsScalarTower R A Ω)
      (_ : IsScalarTower R L Ω),
      (∀ a : A,
        algebraMap A Ω a = algebraMap D Ω (χ (algebraMap A (Localization.AtPrime 𝔮) a))) ∧
      ∀ g : Ω, g ∈ (algebraMap D Ω).range ↔
        ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * g = algebraMap A Ω r := by
  letI : Algebra A D := (χ.toRingHom.comp (algebraMap A (Localization.AtPrime 𝔮))).toAlgebra
  letI : Algebra A Ω := ((algebraMap D Ω).comp (algebraMap A D)).toAlgebra
  haveI : IsScalarTower A D Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsLocalization.AtPrime D 𝔮 := IsLocalization.isLocalization_of_algEquiv 𝔮.primeCompl
    (AlgEquiv.ofRingEquiv (f := χ) (fun _ => rfl))
  haveI : IsFractionRing A Ω := fa_isFractionRing_of_isLocalization 𝔮.primeCompl D
    (Ideal.primeCompl_le_nonZeroDivisors 𝔮)
  letI : Algebra R Ω := ((algebraMap L Ω).comp (algebraMap R L)).toAlgebra
  haveI : IsScalarTower R L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R A Ω := IsScalarTower.of_algebraMap_eq (fun r => (hc r).symm)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun _ => rfl, fun g => mem_range_algebraMap_iff_of_isLocalization 𝔮 g⟩

/-- **Moving to `Frac A`.** An isomorphism `Ψ : Ω ≅ F` of `L`-algebras, for a fraction field `Ω`
of `A`, gives `Ψ₀ = Ψ ∘ ε : Frac A ≅ F` for the isomorphism `ε : Frac A ≅ Ω` of `A`-algebras,
with the `L`-algebra structure on `Frac A` carried along `ε`. -/
theorem fa_exists_fracTransport {R A Ω L F : Type*} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [Field L] [Algebra R L]
    [Algebra L Ω] [Algebra R Ω] [IsScalarTower R A Ω] [IsScalarTower R L Ω]
    [Field F] [Algebra L F] (Ψ : Ω ≃ₐ[L] F) :
    ∃ (_ : Algebra L (FractionRing A)) (_ : IsScalarTower R L (FractionRing A))
      (ε : FractionRing A ≃ₐ[A] Ω) (Ψ₀ : FractionRing A ≃ₐ[L] F), ∀ g, Ψ₀ g = Ψ (ε g) := by
  let ε : FractionRing A ≃ₐ[A] Ω := IsLocalization.algEquiv (nonZeroDivisors A) (FractionRing A) Ω
  letI : Algebra L (FractionRing A) :=
    (ε.symm.toAlgHom.toRingHom.comp (algebraMap L Ω)).toAlgebra
  have hL : ∀ c : L, algebraMap L (FractionRing A) c = ε.symm (algebraMap L Ω c) := fun _ => rfl
  haveI : IsScalarTower R L (FractionRing A) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    rw [hL, ← IsScalarTower.algebraMap_apply R L Ω]
    apply ε.injective
    rw [AlgEquiv.apply_symm_apply, IsScalarTower.algebraMap_apply R A (FractionRing A),
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply R A Ω]
  let Ψ₀ : FractionRing A ≃ₐ[L] F :=
    AlgEquiv.ofRingEquiv (f := ε.toRingEquiv.trans Ψ.toRingEquiv) (fun c => by
      rw [RingEquiv.trans_apply, hL]
      change Ψ (ε (ε.symm (algebraMap L Ω c))) = _
      rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes])
  exact ⟨inferInstance, inferInstance, ε, Ψ₀, fun _ => rfl⟩

/-- **Horizontal valuation subrings contain `K`.** A valuation subring of `Ω` containing the image
of a discrete valuation ring `R` and the inverse of a nonzero element of `𝔪_R` contains the image
of `K = Frac R`. -/
theorem fa_mem_of_dvr_overring {R K Ω : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω]
    [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω] (Q : ValuationSubring Ω)
    (hR : ∀ r : R, algebraMap R Ω r ∈ Q) {t : R} (ht0 : t ≠ 0) (htm : t ∈ maximalIdeal R)
    (hti : (algebraMap R Ω t)⁻¹ ∈ Q) (c : K) : algebraMap K Ω c ∈ Q := by
  have hinj : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : algebraMap R Ω ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht0 hϖ
  have hn : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hu
    exact (mem_maximalIdeal _).1 htm (hu ▸ u.isUnit)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hU0 : algebraMap R Ω (u : R) ≠ 0 := (map_ne_zero_iff _ hinj).2 u.ne_zero
  have hπinv : (algebraMap R Ω ϖ)⁻¹ ∈ Q := by
    have heq : (algebraMap R Ω ϖ)⁻¹ =
        (algebraMap R Ω t)⁻¹ * algebraMap R Ω (u : R) * algebraMap R Ω ϖ ^ k := by
      rw [hu, map_mul, map_pow, pow_succ]
      field_simp
    rw [heq]
    exact mul_mem (mul_mem hti (hR _)) (pow_mem (hR _) k)
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) c
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have hV : algebraMap R Ω ((v⁻¹ : Rˣ) : R) = (algebraMap R Ω (v : R))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, Units.inv_mul, map_one]
  have heq : algebraMap K Ω (algebraMap R K x / algebraMap R K y) =
      algebraMap R Ω x * algebraMap R Ω ((v⁻¹ : Rˣ) : R) * (algebraMap R Ω ϖ)⁻¹ ^ m := by
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hv,
      map_mul, map_pow, hV, div_eq_mul_inv, mul_inv, inv_pow]
    ring
  rw [heq]
  exact mul_mem (mul_mem (hR _) (hR _)) (pow_mem hπinv m)

end Glue

/-! ## 2. `ShortComparisonInput` (items H3 and H4) -/

section Short

open HDec.CMBranch.CMjBridges (AbVarFunctionField abVarIdentity)

/-- **`ShortComparisonInput`**, from the tree instance of item H3. -/
theorem shortComparisonInput : ShortComparisonInput := by
  intro K _ _ L _ _ _ E hdim D 𝒢 hη P hpL
  obtain ⟨hW, hx, hy, hxS, hyS, -⟩ := treeH3_n11Inst hdim D 𝒢 hη P hpL
  have h1 : treeH3Iota E L D.fXY = -treeH3Iota E L D.X / treeH3Iota E L D.Y := by
    rw [ZInQ.Contrib.CMHeight62.ShortData.fXY, map_div₀, map_neg]
  exact ⟨_, _, hW, hx, hy, hxS, hyS, (treeH3Iota_fXY L D).symm.trans h1⟩

end Short

/-! ## 3. The group model is integral -/

section Integral

/-- A scheme flat over a domain `R` whose generic fibre is reduced is reduced: the generic fibre
is scheme-theoretically dense (a flat base change of `Spec K → Spec R`). -/
theorem fa_isReduced_of_flat {R : Type} [CommRing R] [IsDomain R] (K : Type) [Field K]
    [Algebra R K] [IsFractionRing R K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] (h : AlgebraicGeometry.IsReduced
      (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    AlgebraicGeometry.IsReduced X := by
  have hpt : ∀ y : Spec (CommRingCat.of K), Spec.map (CommRingCat.ofHom (algebraMap R K)) y =
      genericPoint (Spec (CommRingCat.of R)) := fun y => by
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R K) y.asIdeal = (⊥ : Ideal R)
    haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
    rw [Ideal.eq_bot_of_prime y.asIdeal]
    exact (RingHom.ker_eq_bot_iff_eq_zero _).2 fun x hx =>
      IsFractionRing.injective R K (hx.trans (map_zero _).symm)
  haveI : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    refine ⟨fun x => ?_⟩
    let y : Spec (CommRingCat.of K) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
    refine closure_mono ?_ (specializes_iff_mem_closure.1 (genericPoint_specializes x))
    rintro _ rfl
    exact ⟨y, hpt y⟩
  haveI : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  exact IsSchemeTheoreticallyDominant.isReduced
    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- **The group model is reduced**: it is flat over `𝓞_L`, and its generic fibre is `E_L`. -/
theorem groupModel_isReduced (𝒢 : GroupModel E L) : AlgebraicGeometry.IsReduced 𝒢.G.left := by
  haveI := isIntegral_of_geometricallyIntegral (E.baseChange L).X
  have hgf : AlgebraicGeometry.IsReduced (Limits.pullback 𝒢.G.hom
      (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))) := by
    have hY : AlgebraicGeometry.IsReduced (E.baseChange L).X.left := inferInstance
    exact @isReduced_of_isOpenImmersion _ _ ((Over.forget _).mapIso 𝒢.gen).hom
      (IsOpenImmersion.of_isIso _) hY
  exact fa_isReduced_of_flat L 𝒢.G.hom hgf

/-- **The group model is integral**: reduced, and irreducible since it is flat over `𝓞_L` with an
irreducible generic fibre. -/
theorem groupModel_isIntegral (𝒢 : GroupModel E L) : AlgebraicGeometry.IsIntegral 𝒢.G.left :=
  (isIntegral_iff_irreducibleSpace_and_isReduced _).2
    ⟨irreducibleSpace_of_isIrreducible_genericFibre 𝒢.G.hom
      (GroupModel.isIrreducible_genericFibre 𝒢), groupModel_isReduced 𝒢⟩

end Integral

/-! ## 4. `LocalAssemblyCore` (node L6) -/

section Core

set_option maxHeartbeats 1000000 in
/-- **`LocalAssemblyCore`**, from the reduced per-place assembly and the centre data of
`CentreData.exists_centre_data`. -/
theorem localAssemblyCore : LocalAssemblyCore := by
  intro K _ E L _ _ _ 𝒢 _ _ hprop v s hs _ _ _ _ _ _ _ _ _ _ F _ _ Ω _ _ _ _ Ψ P _ hdimP hfd
    hv hτ hc W X' Y' hW hX' hY' hXS hYS tG htG
  haveI := hprop
  -- the base: `R = (𝓞_L)_s`
  have hsb : s.asIdeal ≠ ⊥ := hs ▸ v.ne_bot
  haveI : s.asIdeal.IsMaximal := hs ▸ v.isMaximal
  haveI : PerfectField (ResidueField (Localization.AtPrime s.asIdeal)) :=
    SmallGlue.perfectField_residueField_ringOfIntegers s.asIdeal hsb
  haveI : CharZero (Localization.AtPrime s.asIdeal) :=
    SmallGlue.charZero_localization_ringOfIntegers s.asIdeal
  obtain ⟨_, _⟩ := fa_exists_atPrime_algebra (𝓞 L) s.asIdeal L
  haveI : IsFractionRing (Localization.AtPrime s.asIdeal) L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization s.asIdeal.primeCompl _ L
  -- the group model: relative dimension one, integral
  haveI : SmoothOfRelativeDimension 1 𝒢.G.hom := GroupModel.smoothOfRelativeDimension_one 𝒢
  haveI : AlgebraicGeometry.IsIntegral 𝒢.G.left := groupModel_isIntegral 𝒢
  -- the chart, the uniformizer, the parameter and the instances on `A`
  obtain ⟨A₀, _, _, hstd, σ, φ, φη, hφ, hsp, hR⟩ := exists_localModel_genericUnit_algebraMap 𝒢 s
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime s.asIdeal)
  obtain ⟨t, ht, -, hdim, hmax, hker, B, hB⟩ := localStructure_of_standardSmooth σ hϖ
  obtain ⟨h1, h2, h3, h4, h5⟩ := placeInstances σ hϖ hdim hmax
  -- `𝒪_{𝒢,ξ} ≅ A_(t)` (node L2 (a))
  haveI h𝔮 := isPrime_span_sectionParam σ hker
  obtain ⟨e', he'⟩ := localizationAtSectionKer_equiv σ hker
  let χ : Localization.AtPrime
      (Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t}) ≃+* 𝒢.genStalk :=
    e'.symm.toRingEquiv.trans φη
  have hχ0 : ∀ x : A₀, χ (algebraMap (Localization.AtPrime (sectionPrime σ))
      (Localization.AtPrime
        (Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t}))
      (algebraMap A₀ _ x)) = φη (algebraMap A₀ (Localization.AtPrime (RingHom.ker σ)) x) := by
    intro x
    change φη (e'.symm (algebraMap (Localization.AtPrime (sectionPrime σ)) _
      (algebraMap A₀ _ x))) = _
    rw [← IsScalarTower.algebraMap_apply A₀ (Localization.AtPrime (sectionPrime σ))
      (Localization.AtPrime
        (Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t})),
      AlgEquiv.commutes]
  have hχA : ∀ a : Localization.AtPrime (sectionPrime σ),
      χ (algebraMap _ (Localization.AtPrime
        (Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t})) a) =
        𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) (φ a) := by
    have hext : χ.toRingHom.comp (algebraMap (Localization.AtPrime (sectionPrime σ))
        (Localization.AtPrime
          (Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t}))) =
        (𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s)).hom.comp
          (φ : _ →+* _) := by
      refine IsLocalization.ringHom_ext (sectionPrime σ).primeCompl (RingHom.ext fun z => ?_)
      exact (hχ0 z).trans (hsp z).symm
    intro a
    exact RingHom.congr_fun hext a
  have hcR : ∀ r : Localization.AtPrime s.asIdeal,
      algebraMap 𝒢.genStalk Ω (χ (algebraMap (Localization.AtPrime (sectionPrime σ))
        (Localization.AtPrime
          (Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t}))
        (algebraMap (Localization.AtPrime s.asIdeal) (Localization.AtPrime (sectionPrime σ))
          r))) = algebraMap L Ω (algebraMap (Localization.AtPrime s.asIdeal) L r) := by
    have hext : (algebraMap 𝒢.genStalk Ω).comp (χ.toRingHom.comp
        ((algebraMap (Localization.AtPrime (sectionPrime σ)) (Localization.AtPrime
          (Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t}))).comp
          (algebraMap (Localization.AtPrime s.asIdeal)
            (Localization.AtPrime (sectionPrime σ))))) =
        (algebraMap L Ω).comp (algebraMap (Localization.AtPrime s.asIdeal) L) := by
      refine IsLocalization.ringHom_ext s.asIdeal.primeCompl (RingHom.ext fun c => ?_)
      change algebraMap 𝒢.genStalk Ω (χ (algebraMap (Localization.AtPrime (sectionPrime σ))
        (Localization.AtPrime
          (Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t}))
        (algebraMap (Localization.AtPrime s.asIdeal) (Localization.AtPrime (sectionPrime σ))
          (algebraMap (𝓞 L) (Localization.AtPrime s.asIdeal) c)))) =
        algebraMap L Ω (algebraMap (Localization.AtPrime s.asIdeal) L
          (algebraMap (𝓞 L) (Localization.AtPrime s.asIdeal) c))
      rw [hχA, stalkSpecializes_stalkStructMap 𝒢 s σ φ hR c, hc c,
        ← IsScalarTower.algebraMap_apply (𝓞 L) (Localization.AtPrime s.asIdeal) L]
    intro r
    exact RingHom.congr_fun hext r
  -- `Ω` is a fraction field of `A`; then move to `Frac A`
  obtain ⟨_, _, _, _, _, hAΩ, hrange⟩ := fa_exists_omegaPackage
    (R := Localization.AtPrime s.asIdeal) (A := Localization.AtPrime (sectionPrime σ))
    (Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t}) χ hcR
  obtain ⟨_, _, ε, Ψ₀, hΨ₀⟩ := fa_exists_fracTransport (R := Localization.AtPrime s.asIdeal)
    (A := Localization.AtPrime (sectionPrime σ)) Ψ
  have hεA : ∀ a : Localization.AtPrime (sectionPrime σ),
      ε (algebraMap _ (FractionRing (Localization.AtPrime (sectionPrime σ))) a) =
        algebraMap _ Ω a := fun a => ε.commutes a
  -- the tree place, on `Frac A`
  have hgen₀ : ∀ g : FractionRing (Localization.AtPrime (sectionPrime σ)),
      P.valuation (Ψ₀ g) ≤ 1 ↔ ∃ r s' : Localization.AtPrime (sectionPrime σ),
        s' ∉ Ideal.span {algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t} ∧
          algebraMap _ _ s' * g = algebraMap _ _ r := by
    intro g
    rw [hΨ₀, hv, hrange]
    constructor
    · rintro ⟨r, s', hs', h⟩
      refine ⟨r, s', hs', ε.injective ?_⟩
      rw [map_mul, hεA, hεA, h]
    · rintro ⟨r, s', hs', h⟩
      refine ⟨r, s', hs', ?_⟩
      rw [← hεA, ← hεA, ← map_mul, h]
  have hPt₀ : P.valuation (Ψ₀ (algebraMap (Localization.AtPrime (sectionPrime σ))
      (FractionRing (Localization.AtPrime (sectionPrime σ)))
      (algebraMap A₀ (Localization.AtPrime (sectionPrime σ)) t))) = WithZero.exp (-1 : ℤ) := by
    rw [hΨ₀, hεA, hAΩ, hχ0]
    exact hτ _ (maximalIdeal_eq_span_of_ringEquiv σ hker φη)
  let ι₀ : 𝒢.genStalk →+* FractionRing (Localization.AtPrime (sectionPrime σ)) :=
    ε.symm.toAlgHom.toRingHom.comp (algebraMap 𝒢.genStalk Ω)
  have hι₀ : ∀ x : A₀, ι₀ (φη (algebraMap A₀ _ x)) =
      algebraMap (Localization.AtPrime (sectionPrime σ))
        (FractionRing (Localization.AtPrime (sectionPrime σ))) (algebraMap A₀ _ x) := by
    intro x
    change ε.symm (algebraMap 𝒢.genStalk Ω (φη (algebraMap A₀ _ x))) = _
    rw [← hχ0, ← hAΩ]
    exact ε.symm.commutes _
  have htG₀ : Ψ₀ (ι₀ tG) = -X' / Y' := by
    rw [hΨ₀]
    change Ψ (ε (ε.symm (algebraMap 𝒢.genStalk Ω (tG : 𝒢.genStalk)))) = _
    rw [AlgEquiv.apply_symm_apply]
    exact htG
  -- the centre data
  have htr := SpecialFibreGap.trdegLeOne_specialFibreValuation (A₀ := A₀)
    (A := Localization.AtPrime (sectionPrime σ)) (sectionPrime σ).primeCompl
    (FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ
  have hρ : (Spec.map (CentreData.functionFieldHom 𝒢.unitSection s σ φ) ≫
      𝒢.G.left.fromSpecStalk (genericPoint 𝒢.G.left)) ≫ 𝒢.G.hom =
      Spec.map (CommRingCat.ofHom ((algebraMap (Localization.AtPrime s.asIdeal)
        (FractionRing (Localization.AtPrime (sectionPrime σ)))).comp
          (algebraMap (𝓞 L) (Localization.AtPrime s.asIdeal)))) := by
    rw [Category.assoc, SpecialFibreGap.fromSpecStalk_comp_hom, ← Spec.map_comp]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun c => ?_))
    change (CentreData.functionFieldHom 𝒢.unitSection s σ φ).hom
      (SpecialFibreGap.stalkStructMap 𝒢.G (genericPoint 𝒢.G.left) c) =
        algebraMap (Localization.AtPrime s.asIdeal)
          (FractionRing (Localization.AtPrime (sectionPrime σ)))
          (algebraMap (𝓞 L) (Localization.AtPrime s.asIdeal) c)
    have hgen : SpecialFibreGap.stalkStructMap 𝒢.G (genericPoint 𝒢.G.left) c =
        (𝒢.G.left.presheaf.stalkSpecializes
          (genericPoint_specializes (𝒢.unitSection s))).hom
          (SpecialFibreGap.stalkStructMap 𝒢.G (𝒢.unitSection s) c) := by
      have h := congrArg (fun k => k.hom c) (structGermHom_stalkSpecializes 𝒢.G.hom
        (genericPoint_specializes (𝒢.unitSection s)))
      exact h.symm
    rw [hgen, ← hR c, CentreData.functionFieldHom_germ,
      ← IsScalarTower.algebraMap_apply (Localization.AtPrime s.asIdeal)
        (Localization.AtPrime (sectionPrime σ))
        (FractionRing (Localization.AtPrime (sectionPrime σ)))]
  have hAgdef : ∀ x, x ∈ genericSubring Ψ₀ P ↔
      ∃ r u : Localization.AtPrime (sectionPrime σ),
        u ∉ RingHom.ker (localSection σ) ∧ algebraMap _ _ u * x = algebraMap _ _ r := by
    intro x
    refine (mem_genericSubring_iff Ψ₀ P x).trans ((hgen₀ x).trans ?_)
    rw [hker]
  refine localComparison_reduced 𝒢 W v s hs σ φ φη hφ hsp hR hϖ ht hmax hker B hB Ψ₀ P hfd
    hdimP hgen₀ hPt₀ hW hX' hY' hXS hYS ι₀ hι₀ tG htG₀ ?_
  intro f hf
  have hhor : ∀ Q : ValuationSubring (FractionRing (Localization.AtPrime (sectionPrime σ))),
      (∀ r : Localization.AtPrime s.asIdeal,
        algebraMap (Localization.AtPrime s.asIdeal) _ r ∈ Q) →
      (∃ t' : 𝓞 L, t' ≠ 0 ∧ (algebraMap (Localization.AtPrime s.asIdeal) _
        (algebraMap (𝓞 L) (Localization.AtPrime s.asIdeal) t'))⁻¹ ∈ Q ∧ t' ∈ s.asIdeal) →
      IsDiscreteValuationRing Q → Q ≠ genericSubring Ψ₀ P → f ∈ Q := by
    rintro Q hQR ⟨t', ht0, hti, hts⟩ hD hQ
    refine hf Q (fun c => ?_) hD hQ
    refine fa_mem_of_dvr_overring (K := L) Q hQR ?_ ?_ hti c
    · exact (map_ne_zero_iff _ (IsLocalization.injective (Localization.AtPrime s.asIdeal)
        (Ideal.primeCompl_le_nonZeroDivisors s.asIdeal))).2 ht0
    · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ s.asIdeal t').2 hts
  have hcd := CentreData.exists_centre_data 𝒢.unitSection s σ φ hϖ 𝒢.G.hom (unitSection_comp 𝒢)
    hφ htr hρ (genericSubring Ψ₀ P) hAgdef hhor
  exact hcd

end Core

/-! ## 5. `Step7` and `CMHeight62` -/

/-- **`Step7`**, with no hypotheses. -/
theorem step7_unconditional : ZInQ.Contrib.CMHeight62.Step7 :=
  step7 localAssemblyCore shortComparisonInput

/-- **`CMHeight62`**, with no hypotheses: `cmHeight62_of_step7'` applied to `Step7`. -/
theorem cmHeight62_unconditional : HDec.CMBranch.CMHeight62 :=
  cmHeight62_full localAssemblyCore shortComparisonInput

end ZInQ.Contrib.CMHeight62Full
