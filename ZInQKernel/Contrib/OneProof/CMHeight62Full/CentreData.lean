import ZInQKernel.Contrib.OneProof.CMHeight62Full.Centre
import ZInQKernel.Contrib.OneProof.CMHeight62Full.HorizontalPrimes
import ZInQKernel.Contrib.OneProof.CMHeight62Full.SpecialFibreDVR
import ZInQKernel.Contrib.OneProof.CMHeight62Full.LocalStructureScheme
import ZInQKernel.Contrib.OneProof.CMHeight62Full.SpecialFibreValuation

/-!
# Centres of constant places on a smooth proper model (completion of `hcentre`)

`Centre.hcentre_of_model` reduces the hypothesis `hcentre` of
`SpecialFibreFunctionField.reduce_mem_polePart` to local facts at the centres. This file proves
those facts for a proper morphism `g : X ⟶ Spec S` that is smooth of relative dimension one.

* `chart_depthTwo`, `chart_horizontal`: at a localization of a standard smooth algebra of
  relative dimension one at a maximal ideal containing `ϖ`, the image of `ϖ` is a nonzerodivisor
  in the maximal ideal with a discrete valuation ring as quotient (node L1a), and the horizontal
  height-one localizations are discrete valuation rings (node L2 (b)).
* `exists_aeval_mem_nonunits`, `isMaximal_of_forall_aeval_mem`, `chart_isMaximal`: a centre of a
  constant place `O ≠ ⊤` is a closed point of the special fibre, since residues of a place of a
  field of transcendence degree at most one are algebraic over the constants.
* `exists_chart`: the stalk at any point is the localization of a standard smooth algebra of
  relative dimension one over the local ring of its image, compatibly with the stalk map of `g`.
* `centre_stalkMap_apply`, `centre_image_eq`: a centre given by the valuative criterion lies over
  the image of the closed point, compatibly with the base map.
* `hcentre_of_smoothModel`: `hcentre` from these facts, with two inputs left explicit: a point
  `e₀` which is not a centre of a place `O ≠ ē, ⊤`, and a valuation subring `Ag` containing the
  local ring of no other point over `s`.
* `eq_top_of_inv_mem`, `eq_top_of_specialFibrePlace_le`, `ne_of_isCentre`: the identity point is
  not a centre of a place `O ≠ ē, ⊤`.
* `exists_centre_hom`, `exists_generic_centre`: the special-fibre valuation is centred at the
  generic point of the special-fibre component through `e(s)`, with a local surjection onto `𝒪_w`.
* `functionFieldHom`, `exists_centre_data`: the instantiation to `A = 𝒪_{X,e(s)}`, `Ω = Frac A`.
  The base map `R → Ω` is not determined by the isomorphism `φ` alone, so its compatibility with
  `g` at the generic point stays an explicit hypothesis (`hρ`), as in `hcentre_of_model`.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

namespace CentreData

open IsLocalRing

section ChartLocal

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [PerfectField (ResidueField R)] {ϖ : R} (hϖ : Irreducible ϖ)
  {B : Type*} [CommRing B] [Algebra R B] [Algebra.IsStandardSmoothOfRelativeDimension 1 R B]
  (𝔭 : Ideal B) [𝔭.IsMaximal] (h𝔭 : algebraMap R B ϖ ∈ 𝔭)
  {T : Type*} [CommRing T] [IsLocalRing T] [Algebra B T] [IsLocalization.AtPrime T 𝔭]
  [Algebra R T] [IsScalarTower R B T]

include hϖ h𝔭 in
/-- **Depth-two inputs at a closed point of the special fibre.** For any localization `T` of a
standard smooth `R`-algebra of relative dimension one at a maximal ideal containing `ϖ`, the
image of `ϖ` is a nonzerodivisor in the maximal ideal and `T ⧸ (ϖ)` is a discrete valuation
ring. -/
theorem chart_depthTwo :
    IsNoetherianRing T ∧ algebraMap R T ϖ ∈ nonZeroDivisors T ∧
      algebraMap R T ϖ ∈ maximalIdeal T ∧
      ∃ (_ : IsDomain (T ⧸ Ideal.span {algebraMap R T ϖ})),
        IsDiscreteValuationRing (T ⧸ Ideal.span {algebraMap R T ϖ}) := by
  obtain ⟨-, -, hnoeth, -, hnzd, hm, hdom, hdvr, -⟩ := closedPoint_depthTwo hϖ 𝔭 h𝔭
  let e : Localization.AtPrime 𝔭 ≃ₐ[B] T :=
    IsLocalization.algEquiv 𝔭.primeCompl (Localization.AtPrime 𝔭) T
  have he : ∀ r : R, e (algebraMap R (Localization.AtPrime 𝔭) r) = algebraMap R T r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R B (Localization.AtPrime 𝔭),
      IsScalarTower.algebraMap_apply R B T, AlgEquiv.commutes]
  have hnoethT : IsNoetherianRing T := isNoetherianRing_of_ringEquiv _ e.toRingEquiv
  have hspan : Ideal.span {algebraMap R T ϖ} =
      Ideal.map (e.toRingEquiv : Localization.AtPrime 𝔭 →+* T)
        (Ideal.span {algebraMap R (Localization.AtPrime 𝔭) ϖ}) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun x => Ideal.span {x}) (he ϖ).symm
  let q := Ideal.quotientEquiv _ _ e.toRingEquiv hspan
  have hdomT : IsDomain (T ⧸ Ideal.span {algebraMap R T ϖ}) :=
    Function.Injective.isDomain q.symm.toRingHom q.symm.injective
  refine ⟨hnoethT, ?_, ?_, hdomT,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing q⟩
  · rw [← he]
    exact (mem_nonZeroDivisors_iff_left).2 fun x hx => by
      have h := (mem_nonZeroDivisors_iff_left).1 hnzd (e.symm x) (by
        apply e.injective
        rw [map_mul, AlgEquiv.apply_symm_apply, map_zero, hx])
      rw [← e.apply_symm_apply x, h, map_zero]
  · rw [← he]
    exact (map_mem_nonunits_iff (e.toRingEquiv : Localization.AtPrime 𝔭 →+* T) _).2 hm

variable [CharZero R] [IsDomain T]

omit [PerfectField (ResidueField R)] [IsLocalRing T] in
include hϖ 𝔭 in
/-- **Horizontal primes at a chart point.** Height-one primes of `T` not containing `ϖ` have
discrete valuation rings as localizations. -/
theorem chart_horizontal (𝔮 : Ideal T) [𝔮.IsPrime] (h1 : 𝔮.height = 1)
    (hϖ𝔮 : algebraMap R T ϖ ∉ 𝔮) : IsDiscreteValuationRing (Localization.AtPrime 𝔮) :=
  isDiscreteValuationRing_localization_horizontal hϖ 𝔭.primeCompl 𝔮 h1 hϖ𝔮

end ChartLocal

section ResidueAlgebraic

open Polynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A proper valuation subring has a nonzero element of value less than one. -/
theorem exists_ne_zero_mem_nonunits {O : ValuationSubring K} (htop : O ≠ ⊤) :
    ∃ z : K, z ≠ 0 ∧ z ∈ O.nonunits := by
  obtain ⟨y, hy⟩ : ∃ y : K, y ∉ O := by
    by_contra h
    push Not at h
    exact htop (eq_top_iff.2 fun y _ => h y)
  have hy0 : y ≠ 0 := fun h => hy (h ▸ O.zero_mem)
  refine ⟨y⁻¹, inv_ne_zero hy0, O.mem_nonunits_iff.2 ?_⟩
  have h1 : 1 < O.valuation y := by
    rw [← not_le]
    exact fun h => hy ((O.valuation_le_one_iff y).1 h)
  rw [map_inv₀]
  exact inv_lt_one_of_one_lt₀ h1

/-- **Residues of a place are algebraic over the constants.** If `K/k` has transcendence degree at
most one and `O ≠ ⊤` is a place of `K/k`, every `x ∈ O` satisfies a nonzero polynomial over `k`
modulo the maximal ideal of `O`. -/
theorem exists_aeval_mem_nonunits (htr : TrdegLeOne k K) {O : ValuationSubring K}
    (hO : IsConstPlace k O) (htop : O ≠ ⊤) {x : K} (hx : x ∈ O) :
    ∃ p : k[X], p ≠ 0 ∧ aeval x p ∈ O.nonunits := by
  by_cases halg : IsAlgebraic k x
  · obtain ⟨p, hp0, hpx⟩ := halg
    refine ⟨p, hp0, ?_⟩
    rw [hpx]
    exact O.mem_nonunits_iff.2 (by rw [map_zero]; exact zero_lt_one)
  have hA := htr x halg
  obtain ⟨z, hz0, hz⟩ := exists_ne_zero_mem_nonunits htop
  have hzO : z ∈ O := (O.valuation_le_one_iff z).1 (O.mem_nonunits_iff.1 hz).le
  obtain ⟨Q, hQ0, hQz⟩ := hA.isAlgebraic z
  obtain ⟨q, hQq, hndvd⟩ := Q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hQ0 0
  simp only [map_zero, sub_zero] at hQq hndvd
  have hq : aeval z q = 0 := by
    rw [hQq, map_mul, map_pow, aeval_X] at hQz
    exact (mul_eq_zero.1 hQz).resolve_left (pow_ne_zero _ hz0)
  have hq0 : q.coeff 0 ≠ 0 := fun h => hndvd (X_dvd_iff.2 h)
  have hsub : ∀ c : Algebra.adjoin k {x}, (c : K) ∈ O := fun c =>
    GroupCurveNotP1.adjoin_le_place hO hx c.2
  have hdiv : aeval z q.divX ∈ O := by
    rw [aeval_eq_sum_range]
    refine Subring.sum_mem O.toSubring fun i _ => ?_
    rw [Algebra.smul_def]
    exact mul_mem (hsub _) (pow_mem hzO i)
  have hcoeff : ((q.coeff 0 : Algebra.adjoin k {x}) : K) = -(z * aeval z q.divX) := by
    have h := congrArg (aeval z) (X_mul_divX_add q)
    rw [hq, map_add, map_mul, aeval_X, aeval_C] at h
    change z * aeval z q.divX + ((q.coeff 0 : Algebra.adjoin k {x}) : K) = 0 at h
    linear_combination h
  obtain ⟨p, hp⟩ : ((q.coeff 0 : Algebra.adjoin k {x}) : K) ∈ (aeval x : k[X] →ₐ[k] K).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]
    exact (q.coeff 0).2
  change aeval x p = _ at hp
  refine ⟨p, ?_, ?_⟩
  · rintro rfl
    apply hq0
    apply Subtype.ext
    rw [← hp]
    simp
  · rw [hp, hcoeff]
    refine O.mem_nonunits_iff.2 ?_
    rw [Valuation.map_neg, map_mul]
    calc O.valuation z * O.valuation (aeval z q.divX) ≤ O.valuation z * 1 :=
          mul_le_mul_of_nonneg_left ((O.valuation_le_one_iff _).2 hdiv) zero_le
      _ < 1 := by rw [mul_one]; exact O.mem_nonunits_iff.1 hz

end ResidueAlgebraic

section Maximal

open Polynomial

/-- **Closed points.** A prime `𝔭` of an `R`-algebra `B` lying over the maximal ideal of the local
ring `R` is maximal when every `b ∈ B` is a root modulo `𝔭` of a polynomial over `R` that is
nonzero modulo `𝔪_R`. -/
theorem isMaximal_of_forall_aeval_mem {R : Type*} [CommRing R] [IsLocalRing R] {B : Type*}
    [CommRing B] [Algebra R B] (𝔭 : Ideal B) [𝔭.IsPrime]
    (hm : maximalIdeal R ≤ 𝔭.comap (algebraMap R B))
    (h : ∀ b : B, ∃ p : R[X], p.map (residue R) ≠ 0 ∧ aeval b p ∈ 𝔭) : 𝔭.IsMaximal := by
  let _ : Algebra (ResidueField R) (B ⧸ 𝔭) := Ideal.Quotient.algebraQuotientOfLEComap hm
  have : IsScalarTower R (ResidueField R) (B ⧸ 𝔭) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hint : Algebra.IsIntegral (ResidueField R) (B ⧸ 𝔭) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, hp0, hpb⟩ := h b
    refine IsAlgebraic.isIntegral ⟨p.map (residue R), hp0, ?_⟩
    have h1 : aeval (Ideal.Quotient.mk 𝔭 b) (p.map (residue R)) =
        aeval (Ideal.Quotient.mk 𝔭 b) p := by
      rw [← ResidueField.algebraMap_eq, aeval_map_algebraMap]
    rw [h1, ← Ideal.Quotient.mkₐ_eq_mk R, aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hpb
  refine Ideal.Quotient.maximal_of_isField _ ?_
  exact isField_of_isIntegral_of_isField' (R := ResidueField R) (Field.toIsField _)

end Maximal

section Chart

open AlgebraicGeometry CategoryTheory

/-- The germ of `f^♯ y` at `x` is the stalk map applied to the germ of `y` at `f x`. -/
theorem germ_appLE_apply {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (x : X) (hx : x ∈ V) (h : f x ∈ U) (y : Γ(Y, U)) :
    (X.presheaf.germ V x hx).hom ((f.appLE U V e).hom y) =
      (f.stalkMap x).hom ((Y.presheaf.germ U (f x) h).hom y) := by
  have key : Y.presheaf.germ U (f x) h ≫ f.stalkMap x =
      f.appLE U V e ≫ X.presheaf.germ V x hx := by
    rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  exact (congrArg (fun φ => φ.hom y) key).symm

attribute [local instance] chartBaseAlgebra

/-- **A chart at any point.** For `g : X ⟶ Spec S` smooth of relative dimension one and a point
`c` whose image has a discrete valuation ring `R` as local ring, there is a standard smooth
`R`-algebra `B` of relative dimension one and a prime `𝔭` of `B` with `B_𝔭 ≅ 𝒪_{X,c}`, compatibly
with the stalk map of `g` on `R`. -/
theorem exists_chart {S : Type} [CommRing S] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S))
    [SmoothOfRelativeDimension 1 g] (c : X) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra (Localization.AtPrime (g c).asIdeal) B),
      Algebra.IsStandardSmoothOfRelativeDimension 1 (Localization.AtPrime (g c).asIdeal) B ∧
      ∃ (𝔭 : Ideal B) (_ : 𝔭.IsPrime) (ψ : Localization.AtPrime 𝔭 ≃+* X.presheaf.stalk c),
        ∀ r, ψ (algebraMap _ (Localization.AtPrime 𝔭) r) =
          (g.stalkMap c).hom (specStalkEquiv (g c) r) := by
  obtain ⟨U, hU, V, hV, hcV, hVU, hss⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := g) c
  have hsU : g c ∈ U := hVU hcV
  let RU := Γ(Spec (CommRingCat.of S), U)
  let A := Γ(X, V)
  let _ : Algebra RU A := (g.appLE U V hVU).hom.toAlgebra
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension 1 RU A := hss
  let Rs := Localization.AtPrime (g c).asIdeal
  let ψ0 := specStalkEquiv (g c)
  let _ : Algebra RU Rs := (ψ0.symm.toRingHom.comp
    ((Spec (CommRingCat.of S)).presheaf.germ U (g c) hsU).hom).toAlgebra
  let q := (hU.primeIdealOf ⟨g c, hsU⟩).asIdeal
  let _ : Algebra RU ((Spec (CommRingCat.of S)).presheaf.stalk (g c)) :=
    ((Spec (CommRingCat.of S)).presheaf.germ U (g c) hsU).hom.toAlgebra
  have hqs : IsLocalization.AtPrime ((Spec (CommRingCat.of S)).presheaf.stalk (g c)) q :=
    hU.isLocalization_stalk ⟨g c, hsU⟩
  have hq : IsLocalization.AtPrime Rs q :=
    IsLocalization.isLocalization_of_algEquiv _
      (AlgEquiv.ofRingEquiv (f := ψ0.symm) (fun _ => rfl))
  let p := (hV.primeIdealOf ⟨c, hcV⟩).asIdeal
  let _ : Algebra A (X.presheaf.stalk c) := (X.presheaf.germ V c hcV).hom.toAlgebra
  have hp : IsLocalization.AtPrime (X.presheaf.stalk c) p := hV.isLocalization_stalk ⟨c, hcV⟩
  have hgerm : ∀ u : RU, algebraMap A (X.presheaf.stalk c) (algebraMap RU A u) =
      (g.stalkMap c).hom (((Spec (CommRingCat.of S)).presheaf.germ U (g c) hsU).hom u) :=
    fun u => germ_appLE_apply g U V hVU c hcV hsU u
  have hp_iff : ∀ a : A, a ∈ p ↔ algebraMap A (X.presheaf.stalk c) a ∈ maximalIdeal _ := by
    intro a
    conv_lhs => rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk c) p]
    rfl
  set M := Algebra.algebraMapSubmonoid A q.primeCompl
  have hdisj : Disjoint (M : Set A) (p : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨u, hu, rfl⟩ hup
    have hunit : IsUnit (((Spec (CommRingCat.of S)).presheaf.germ U (g c) hsU).hom u) :=
      IsLocalization.map_units _ (⟨u, hu⟩ : q.primeCompl)
    have h2 := (hp_iff _).1 hup
    rw [hgerm, mem_maximalIdeal, mem_nonunits_iff] at h2
    exact h2 (hunit.map _)
  have hB := chartBase_isLocalization (A := A) (Rs := Rs) q
  let 𝔭 : Ideal (chartBase RU Rs A) := p.map (algebraMap A (chartBase RU Rs A))
  have h𝔭 : 𝔭.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ p inferInstance hdisj
  have hc𝔭 : 𝔭.comap (algebraMap A (chartBase RU Rs A)) = p :=
    IsLocalization.under_map_of_isPrime_disjoint M _ inferInstance hdisj
  obtain ⟨φ, hφA⟩ := exists_localizationEquiv_of_comap (T := X.presheaf.stalk c) q p 𝔭 hc𝔭
  refine ⟨chartBase RU Rs A, inferInstance, inferInstance,
    Algebra.IsStandardSmoothOfRelativeDimension.baseChange _ _, 𝔭, h𝔭, φ, ?_⟩
  have hext : (φ : Localization.AtPrime 𝔭 →+* X.presheaf.stalk c).comp
      (algebraMap Rs (Localization.AtPrime 𝔭)) = (g.stalkMap c).hom.comp (ψ0 : Rs →+* _) := by
    refine IsLocalization.ringHom_ext q.primeCompl (RingHom.ext fun u => ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    have h1 : algebraMap Rs (chartBase RU Rs A) (algebraMap RU Rs u) =
        algebraMap A (chartBase RU Rs A) (algebraMap RU A u) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.right_algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rw [IsScalarTower.algebraMap_apply Rs (chartBase RU Rs A) (Localization.AtPrime 𝔭), h1,
      hφA, hgerm]
    change _ = (g.stalkMap c).hom (ψ0 (ψ0.symm _))
    rw [RingEquiv.apply_symm_apply]
  exact fun r => RingHom.congr_fun hext r

end Chart

section Helpers

open AlgebraicGeometry CategoryTheory SpecialFibreFunctionField

/-- `specStalkEquiv` is compatible with the structure maps from `S`. -/
theorem specStalkEquiv_algebraMap {S : Type} [CommRing S] (x : Spec (CommRingCat.of S)) (t : S) :
    specStalkEquiv x (algebraMap S _ t) =
      ((Spec (CommRingCat.of S)).presheaf.germ ⊤ x trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom t) :=
  congrArg (fun f => f.hom t) (Spec.algebraMap_stalkIso_inv x)

variable {S : Type} [CommRing S] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S)) (c : X)
  {V : CommRingCat.{0}} (φ : X.presheaf.stalk c ⟶ V) (ρO : CommRingCat.of S ⟶ V)
  (h : Spec.map φ ≫ X.fromSpecStalk c ≫ g = Spec.map ρO)
include h

/-- At a centre, the local map composed with the stalk map of `g` is the base map. -/
theorem centre_stalkMap_apply (t : S) :
    φ.hom ((g.stalkMap c).hom (specStalkEquiv (g c) (algebraMap S _ t))) = ρO.hom t := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq] at h
  simp only [← Spec.map_comp] at h
  have h' := Spec.map_injective h
  rw [specStalkEquiv_algebraMap]
  exact congrArg (fun f => f.hom t) h'

/-- A centre lies over the image of the closed point. -/
theorem centre_image_eq [IsLocalRing V] [IsLocalHom φ.hom] :
    g c = Spec.map ρO (IsLocalRing.closedPoint V) := by
  have e1 : (Spec.map φ ≫ X.fromSpecStalk c ≫ g) (IsLocalRing.closedPoint V) = g c := by
    change g ((X.fromSpecStalk c) ((Spec.map φ) (IsLocalRing.closedPoint V))) = _
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  rw [← e1, h]

end Helpers

section Units

open SpecialFibreFunctionField

variable {Ω : Type*} [Field Ω] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {w : Valuation Ω Γ₀} {T : Type*} [CommRing T] (F : T →+* Ω)

/-- An element whose value is less than one is not a unit, when `w ≤ 1` on the image of `T`. -/
theorem not_isUnit_of_val_lt_one (hF : ∀ b, w (F b) ≤ 1) {b : T} (hb : w (F b) < 1) :
    ¬ IsUnit b := by
  rintro ⟨u, rfl⟩
  have h := congrArg (fun y => w (F y)) u.mul_inv
  simp only [map_mul, map_one] at h
  have h2 : w (F u) * w (F ↑u⁻¹) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right' (hF _)) hb
  rw [h] at h2
  exact lt_irrefl _ h2

theorem reduce_mul' {x y : Ω} (hx : w x ≤ 1) (hy : w y ≤ 1) (hxy : w (x * y) ≤ 1) :
    reduce w (x * y) hxy = reduce w x hx * reduce w y hy := by
  simp only [reduce, ← map_mul]
  rfl

/-- An element whose residue lies in the maximal ideal of `O` is not a unit, when `T` maps into
`Õ`. -/
theorem not_isUnit_of_reduce_mem_nonunits {O : ValuationSubring (ResidueField w.valuationSubring)}
    (hF : ∀ b, F b ∈ liftValuationSubring w O) {b : T} (hb1 : w (F b) ≤ 1)
    (hb : reduce w (F b) hb1 ∈ O.nonunits) : ¬ IsUnit b := by
  rintro ⟨u, rfl⟩
  obtain ⟨hv, hvO⟩ := hF ↑u⁻¹
  have hv1 : w (F ↑u⁻¹) ≤ 1 := (w.mem_valuationSubring_iff _).1 hv
  have hmul : F u * F ↑u⁻¹ = 1 := by rw [← map_mul, u.mul_inv, map_one]
  have h1 : w (F u * F ↑u⁻¹) ≤ 1 := by rw [hmul, map_one]
  have hr := reduce_mul' hb1 hv1 h1
  have hr1 : reduce w (F u * F ↑u⁻¹) h1 = 1 := by
    simp only [reduce, hmul]
    exact map_one _
  rw [hr1] at hr
  have hvO' : O.valuation (reduce w (F ↑u⁻¹) hv1) ≤ 1 := (O.valuation_le_one_iff _).2 hvO
  have h2 := O.mem_nonunits_iff.1 hb
  have h3 : O.valuation (reduce w (F u) hb1 * reduce w (F ↑u⁻¹) hv1) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hvO') h2
  rw [← hr, map_one] at h3
  exact lt_irrefl _ h3

end Units

section ChartMaximal

open Polynomial SpecialFibreFunctionField

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
  (hϖ : Irreducible ϖ) {B : Type*} [CommRing B] [Algebra R B] (𝔭 : Ideal B) [𝔭.IsPrime]
  {T : Type*} [CommRing T] [IsLocalRing T] [Algebra B T] [IsLocalization.AtPrime T 𝔭]
  [Algebra R T] [IsScalarTower R B T]
  {Ω : Type*} [Field Ω] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {w : Valuation Ω Γ₀}
  (F : T →+* Ω) (ρR : R →+* Ω) (hFR : ∀ r, F (algebraMap R T r) = ρR r)
  (hR : ∀ r, w (ρR r) ≤ 1) (hm : ∀ r ∈ maximalIdeal R, w (ρR r) < 1)
  [Algebra (ResidueField R) (ResidueField w.valuationSubring)]
  (hk : ∀ r, algebraMap (ResidueField R) _ (residue R r) = reduce w (ρR r) (hR r))
  {O : ValuationSubring (ResidueField w.valuationSubring)}
  (hdom : ∀ b, F b ∈ liftValuationSubring w O)

omit [Algebra (ResidueField R) (ResidueField w.valuationSubring)] in
include hϖ hFR hm hdom in
/-- At a centre, the image of `ϖ` lies in the prime `𝔭` of the chart. -/
theorem chart_mem : algebraMap R B ϖ ∈ 𝔭 := by
  have hFw : ∀ b, w (F b) ≤ 1 := fun b =>
    (w.mem_valuationSubring_iff _).1 (liftValuationSubring_le O (hdom b))
  have hϖm : ϖ ∈ maximalIdeal R := hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ
  have hT : algebraMap R T ϖ ∈ maximalIdeal T := (mem_maximalIdeal _).2
    (not_isUnit_of_val_lt_one F hFw (by rw [hFR]; exact hm ϖ hϖm))
  rw [← IsLocalization.AtPrime.under_maximalIdeal T 𝔭]
  change algebraMap B T (algebraMap R B ϖ) ∈ maximalIdeal T
  rwa [← IsScalarTower.algebraMap_apply]

include hϖ hFR hm hk hdom in
/-- **The centre is a closed point.** If `κ_w` has transcendence degree at most one over the
residue field of `R` and `O ≠ ⊤` is a constant place, the prime `𝔭` of the chart at a centre of
`O` is maximal. -/
theorem chart_isMaximal (htr : TrdegLeOne (ResidueField R) (ResidueField w.valuationSubring))
    (hO : IsConstPlace (ResidueField R) O) (htop : O ≠ ⊤) : 𝔭.IsMaximal := by
  have hFw : ∀ b, w (F b) ≤ 1 := fun b =>
    (w.mem_valuationSubring_iff _).1 (liftValuationSubring_le O (hdom b))
  have hp𝔭 : ∀ x : B, x ∈ 𝔭 ↔ algebraMap B T x ∈ maximalIdeal T := fun x => by
    rw [← IsLocalization.AtPrime.under_maximalIdeal T 𝔭]
    rfl
  have hmem := chart_mem hϖ 𝔭 F ρR hFR hm hdom
  refine isMaximal_of_forall_aeval_mem (R := R) 𝔭 ?_ fun b => ?_
  · rw [hϖ.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  set y := algebraMap B T b
  have hx : reduce w (F y) (hFw y) ∈ O := (mem_liftValuationSubring (hFw y)).1 (hdom y)
  obtain ⟨q, hq0, hq⟩ := exists_aeval_mem_nonunits htr hO htop hx
  obtain ⟨p, rfl⟩ := Polynomial.map_surjective (residue R) residue_surjective q
  refine ⟨p, hq0, (hp𝔭 _).2 ((mem_maximalIdeal _).2 ?_)⟩
  rw [← Polynomial.aeval_algebraMap_apply]
  refine not_isUnit_of_reduce_mem_nonunits F hdom (hFw _) ?_
  let ρw : R →+* w.valuationSubring :=
    ρR.codRestrict _ fun r => (w.mem_valuationSubring_iff _).2 (hR r)
  let z : w.valuationSubring := ⟨F y, (w.mem_valuationSubring_iff _).2 (hFw y)⟩
  have hFeval : F (aeval y p) = ((eval₂ ρw z p : w.valuationSubring) : Ω) := by
    have h1 : F (aeval y p) = eval₂ ρR (F y) p := by
      rw [aeval_def, hom_eval₂]
      congr 1
      exact RingHom.ext hFR
    have h2 : ((eval₂ ρw z p : w.valuationSubring) : Ω) =
        eval₂ (w.valuationSubring.subtype.comp ρw) (F y) p :=
      hom_eval₂ p ρw w.valuationSubring.subtype z
    rw [h1, h2]
    rfl
  have hred : reduce w (F (aeval y p)) (hFw _) = residue _ (eval₂ ρw z p) := by
    simp only [reduce, hFeval]
  have hcomp : (residue w.valuationSubring).comp ρw =
      (algebraMap (ResidueField R) _).comp (residue R) := by
    ext r
    simp only [RingHom.comp_apply, hk]
    rfl
  rw [hred, hom_eval₂, hcomp, ← eval₂_map, ← aeval_def]
  exact hq

end ChartMaximal

section Overring

variable {D K : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [Field K]

/-- **Overrings of a discrete valuation ring.** Let `ι : D → K` embed a discrete valuation ring in
a field which is its fraction field. A valuation subring `O ⊇ ι D` containing the inverse of the
image of a nonzero nonunit is all of `K`. -/
theorem eq_top_of_inv_mem (ι : D →+* K) (hι : Function.Injective ι)
    (hfrac : ∀ z : K, ∃ a b : D, ι b ≠ 0 ∧ z * ι b = ι a) (O : ValuationSubring K)
    (hle : ∀ d, ι d ∈ O) {d : D} (hd0 : d ≠ 0) (hdu : ¬ IsUnit d) (hd : (ι d)⁻¹ ∈ O) :
    O = ⊤ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible D
  have hπ0 : ι π ≠ 0 := (map_ne_zero_iff ι hι).2 hπ.ne_zero
  have hunit : ∀ u : Dˣ, (ι u)⁻¹ ∈ O := fun u => by
    have : (ι u)⁻¹ = ι ↑u⁻¹ := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ ((u.isUnit.map ι).ne_zero), ← map_mul,
        Units.inv_mul, map_one]
    rw [this]
    exact hle _
  have hπinv : (ι π)⁻¹ ∈ O := by
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hπ
    rcases n with _ | n
    · exact absurd (by simp) hdu
    · have h1 : (ι π)⁻¹ = ι π ^ n * ι ↑u * (ι (↑u * π ^ (n + 1)))⁻¹ := by
        rw [map_mul, map_pow, mul_inv, pow_succ, mul_inv]
        field_simp [(u.isUnit.map ι).ne_zero, hπ0]
      rw [h1]
      exact O.mul_mem _ _ (O.mul_mem _ _ (O.pow_mem (hle π) n) (hle _)) hd
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨a, b, hb, hz⟩ := hfrac z
  have hb0 : b ≠ 0 := fun h => hb (by rw [h, map_zero])
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  have hu0 := (u.isUnit.map ι).ne_zero
  have hz' : z = ι a * (ι u)⁻¹ * ((ι π)⁻¹) ^ m := by
    rw [← hz, map_mul, map_pow, inv_pow]
    field_simp
  rw [hz']
  exact O.mul_mem _ _ (O.mul_mem _ _ (hle a) (hunit u)) (O.pow_mem hπinv m)

end Overring

section PlaceOverring

open SpecialFibreFunctionField SpecialFibreValuation

variable {R : Type*} [CommRing R]
  {A : Type*} [CommRing A] [IsNoetherianRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A]
  {Ω : Type*} [Field Ω] [Algebra A Ω] [IsFractionRing A Ω]
  {ϖ : R} (hϖ : Irreducible ϖ) [IsDomain (A ⧸ Ideal.span {algebraMap R A ϖ})]
  [IsDiscreteValuationRing (A ⧸ Ideal.span {algebraMap R A ϖ})]

include hϖ in
/-- **Only `ē` and `⊤` contain `A`.** A valuation subring `O` of `κ_w` whose lift `Õ` contains `A`
is `ē` or `⊤`. -/
theorem eq_top_of_specialFibrePlace_le
    (O : ValuationSubring (ResidueField (specialFibreValuation A Ω hϖ).valuationSubring))
    (hle : ∀ a : A, algebraMap A Ω a ∈ liftValuationSubring _ O)
    (hne : O ≠ specialFibrePlace A Ω hϖ) : O = ⊤ := by
  have hle' : ∀ y, specialFibreResidueMap A Ω hϖ y ∈ O := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨_, h2⟩ := hle a
    exact h2
  have hēO : ∀ z ∈ specialFibrePlace A Ω hϖ, z ∈ O := fun z hz => by
    obtain ⟨y, rfl⟩ := (mem_specialFibrePlace hϖ).1 hz
    exact hle' y
  obtain ⟨z, hzO, hzē⟩ : ∃ z ∈ O, z ∉ specialFibrePlace A Ω hϖ := by
    by_contra h
    push Not at h
    exact hne (le_antisymm (fun z hz => h z hz) (fun z hz => hēO z hz))
  have hz0 : z ≠ 0 := fun h => hzē (h ▸ (specialFibrePlace A Ω hϖ).zero_mem)
  obtain ⟨y, hy⟩ := (mem_specialFibrePlace hϖ).1
    (((specialFibrePlace A Ω hϖ).mem_or_inv_mem z).resolve_left hzē)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, inv_eq_zero] at hy
    exact hz0 hy
  have hyu : ¬ IsUnit y := by
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    apply hzē
    have h1 : specialFibreResidueMap A Ω hϖ y * specialFibreResidueMap A Ω hϖ v = 1 := by
      rw [← map_mul, hv, map_one]
    rw [hy] at h1
    rw [(inv_mul_eq_one₀ hz0).1 h1]
    exact (mem_specialFibrePlace hϖ).2 ⟨_, rfl⟩
  refine eq_top_of_inv_mem _ (specialFibreResidueMap_injective hϖ)
    (exists_mul_specialFibreResidueMap_eq hϖ) O hle' hy0 hyu ?_
  rw [hy, inv_inv]
  exact hzO

end PlaceOverring

section Assembly

open AlgebraicGeometry CategoryTheory SpecialFibreFunctionField Centre

/-- **`hcentre` from a smooth proper model.** Let `g : X ⟶ Spec S` be proper and smooth of relative
dimension one with `X` integral, `τ : K(X) ≅ Ω`, `s` a point with `R = S_s` a discrete valuation
ring of characteristic zero with perfect residue field and uniformizer `ϖ`, and `w` a discrete
valuation of `Ω` centred at `η` (a local surjection `𝒪_{X,η} → 𝒪_w` compatible with `τ`), with
`w ≤ 1` on `R` and `w < 1` on `𝔪_R` through `ρR : R → Ω`, and `κ_w` of transcendence degree at most
one over `κ(s)`. The base map `ρR` is compatible with `g` at the generic point (`hρ`). Let `e₀` be
a point which is not a centre of any constant place `O ≠ ē, ⊤` (`he₀`), and `Ag` a valuation subring
of `Ω` not containing the local ring of any point `c ≠ e₀` over `s` (`hAg`). If `f` lies in every
discrete valuation subring containing the image of `S`, inverting an element of `s`, and different
from `Ag`, then the hypothesis `hcentre` of `reduce_mem_polePart` holds. -/
theorem hcentre_of_smoothModel {S : Type} [CommRing S] {X : Scheme.{0}} [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of S)) [IsProper g] [SmoothOfRelativeDimension 1 g]
    {Ω : Type} [Field Ω] (τ : X.functionField ⟶ CommRingCat.of Ω)
    (hτ : Function.Bijective τ.hom)
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {w : Valuation Ω Γ₀}
    {ϖw : Ω} (hϖ0 : ϖw ≠ 0) (hϖw : w ϖw < 1) (hdisc : ∀ x : Ω, x ≠ 0 → ∃ m : ℤ, w x = w ϖw ^ m)
    (s : Spec (CommRingCat.of S)) [IsDomain (Localization.AtPrime s.asIdeal)]
    [IsDiscreteValuationRing (Localization.AtPrime s.asIdeal)]
    [PerfectField (ResidueField (Localization.AtPrime s.asIdeal))]
    [CharZero (Localization.AtPrime s.asIdeal)]
    {ϖ : Localization.AtPrime s.asIdeal} (hϖ : Irreducible ϖ)
    (ρR : Localization.AtPrime s.asIdeal →+* Ω) (hR : ∀ r, w (ρR r) ≤ 1)
    (hm : ∀ r ∈ maximalIdeal (Localization.AtPrime s.asIdeal), w (ρR r) < 1)
    [Algebra (ResidueField (Localization.AtPrime s.asIdeal)) (ResidueField w.valuationSubring)]
    (hk : ∀ r, algebraMap (ResidueField (Localization.AtPrime s.asIdeal)) _ (residue _ r) =
      reduce w (ρR r) (hR r))
    (htr : TrdegLeOne (ResidueField (Localization.AtPrime s.asIdeal))
      (ResidueField w.valuationSubring))
    (hρ : (Spec.map τ ≫ X.fromSpecStalk (genericPoint X)) ≫ g =
      Spec.map (CommRingCat.ofHom (ρR.comp (algebraMap S (Localization.AtPrime s.asIdeal)))))
    (η : X) (φ₀ : X.presheaf.stalk η ⟶ CommRingCat.of w.valuationSubring) [IsLocalHom φ₀.hom]
    (hφ₀ : ∀ b, τ.hom ((X.presheaf.stalkSpecializes (genericPoint_specializes η)).hom b) =
      algebraMap w.valuationSubring Ω (φ₀.hom b)) (hφ₀s : Function.Surjective φ₀.hom)
    (ē : ValuationSubring (ResidueField w.valuationSubring)) (e₀ : X)
    (he₀ : ∀ O : ValuationSubring (ResidueField w.valuationSubring),
      IsConstPlace (ResidueField (Localization.AtPrime s.asIdeal)) O → O ≠ ē → O ≠ ⊤ →
      ∀ (c : X) (φ : X.presheaf.stalk c ⟶ CommRingCat.of (liftValuationSubring w O)),
      IsLocalHom φ.hom →
      (∀ b, τ.hom ((X.presheaf.stalkSpecializes (genericPoint_specializes c)).hom b) =
        algebraMap (liftValuationSubring w O) Ω (φ.hom b)) → c ≠ e₀)
    (Ag : ValuationSubring Ω)
    (hAg : ∀ c : X, g c = s → c ≠ e₀ → ∃ b : X.presheaf.stalk c,
      τ.hom ((X.presheaf.stalkSpecializes (genericPoint_specializes c)).hom b) ∉ Ag)
    {f : Ω}
    (hhor : ∀ Q : ValuationSubring Ω,
      (∀ t : S, ρR (algebraMap S (Localization.AtPrime s.asIdeal) t) ∈ Q) →
      (∃ t : S, t ≠ 0 ∧ (ρR (algebraMap S (Localization.AtPrime s.asIdeal) t))⁻¹ ∈ Q ∧
        t ∈ s.asIdeal) →
      IsDiscreteValuationRing Q → Q ≠ Ag → f ∈ Q) :
    ∀ O : ValuationSubring (ResidueField w.valuationSubring),
      IsConstPlace (ResidueField (Localization.AtPrime s.asIdeal)) O →
      O ≠ ē → ∃ (Ac : Subring Ω) (ϖ : Ac), (∀ a ∈ Ac, a ∈ liftValuationSubring w O) ∧
        (∀ g : Ω, (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 →
          ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r) → g ∈ Ac) ∧
        (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → ϖ ∈ 𝔮 → ∀ g : Ω, w g ≤ 1 →
          ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r) ∧
        (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → ϖ ∉ 𝔮 →
          ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * f = r) := by
  intro O hO hne
  by_cases htop : O = ⊤
  · subst htop
    exact centre_spec_top w hϖ0 hϖw hdisc f
  have hρRO : ∀ r, ρR r ∈ liftValuationSubring w O := fun r =>
    (mem_liftValuationSubring (hR r)).2 (by rw [← hk]; exact hO _)
  let ρRO : Localization.AtPrime s.asIdeal →+* liftValuationSubring w O :=
    ρR.codRestrict _ hρRO
  let ρO : S →+* liftValuationSubring w O := ρRO.comp (algebraMap S _)
  have hsq : (Spec.map τ ≫ X.fromSpecStalk (genericPoint X)) ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap (liftValuationSubring w O) Ω)) ≫
        Spec.map (CommRingCat.ofHom ρO) := by
    rw [hρ, ← Spec.map_comp]
    rfl
  obtain ⟨c, φ, hφ, hspec, hgerm⟩ := exists_centre_germ g τ (liftValuationSubring w O)
    (Spec.map (CommRingCat.ofHom ρO)) hsq
  have hOw : ∀ b ∈ liftValuationSubring w O, w b ≤ 1 := fun b hb =>
    (w.mem_valuationSubring_iff _).1 (liftValuationSubring_le O hb)
  -- the centre lies over `s`
  have hcs : g c = s := by
    rw [centre_image_eq g c φ _ hspec]
    apply PrimeSpectrum.ext
    ext t
    change ρO t ∈ maximalIdeal (liftValuationSubring w O) ↔ t ∈ s.asIdeal
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime s.asIdeal)
      s.asIdeal t]
    constructor
    · intro h
      by_contra hn
      rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hn
      exact (mem_maximalIdeal _).1 h (hn.map ρRO)
    · intro h
      refine (mem_maximalIdeal _).2 (not_isUnit_of_val_lt_one (w := w)
        (liftValuationSubring w O).subtype (fun b => hOw b b.2) ?_)
      exact hm _ h
  subst hcs
  obtain ⟨B, _, _, hB, 𝔭, h𝔭, ψ, hψ⟩ := exists_chart g c
  let _ : Algebra B (X.presheaf.stalk c) :=
    (ψ.toRingHom.comp (algebraMap B (Localization.AtPrime 𝔭))).toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk c) 𝔭 :=
    IsLocalization.isLocalization_of_algEquiv 𝔭.primeCompl
      (AlgEquiv.ofRingEquiv (f := ψ) (fun _ => rfl))
  let _ : Algebra (Localization.AtPrime (g c).asIdeal) (X.presheaf.stalk c) :=
    ((g.stalkMap c).hom.comp (specStalkEquiv (g c)).toRingHom).toAlgebra
  have : IsScalarTower (Localization.AtPrime (g c).asIdeal) B (X.presheaf.stalk c) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change (g.stalkMap c).hom (specStalkEquiv (g c) r) =
        ψ (algebraMap B _ (algebraMap _ B r))
      rw [← IsScalarTower.algebraMap_apply, hψ]
  let F : X.presheaf.stalk c →+* Ω :=
    (X.presheaf.stalkSpecializes (genericPoint_specializes c) ≫ τ).hom
  have hFR : ∀ r, F (algebraMap (Localization.AtPrime (g c).asIdeal) (X.presheaf.stalk c) r) =
      ρR r := by
    intro r
    have hext : F.comp (algebraMap (Localization.AtPrime (g c).asIdeal) (X.presheaf.stalk c)) =
        ρR := by
      refine IsLocalization.ringHom_ext (g c).asIdeal.primeCompl (RingHom.ext fun t => ?_)
      have h1 := centre_stalkMap_apply g c φ (CommRingCat.ofHom ρO) hspec t
      have h2 := hgerm ((g.stalkMap c).hom (specStalkEquiv (g c) (algebraMap S _ t)))
      change τ.hom ((X.presheaf.stalkSpecializes (genericPoint_specializes c)).hom
        ((g.stalkMap c).hom (specStalkEquiv (g c) (algebraMap S _ t)))) = _
      rw [h2, h1]
      rfl
    exact RingHom.congr_fun hext r
  have hdom : ∀ b, F b ∈ liftValuationSubring w O := fun b => by
    change τ.hom ((X.presheaf.stalkSpecializes (genericPoint_specializes c)).hom b) ∈ _
    rw [hgerm b]
    exact (φ.hom b).2
  have h𝔭mem := chart_mem hϖ 𝔭 F ρR hFR hm hdom
  have h𝔭max := chart_isMaximal hϖ 𝔭 F ρR hFR hR hm hk hdom htr hO htop
  obtain ⟨hnoeth, hnzd, hmT, hdomq, hdvrq⟩ :=
    chart_depthTwo hϖ 𝔭 h𝔭mem (T := X.presheaf.stalk c)
  have hdomT : IsDomain (X.presheaf.stalk c) := depthTwo_isDomain hnzd hmT
  let _ : Algebra (X.presheaf.stalk c) Ω := F.toAlgebra
  have := isFractionRing_stalk c τ hτ
  have hdom' : ∀ b : X.presheaf.stalk c,
      algebraMap (X.presheaf.stalk c) Ω b ∈ liftValuationSubring w O := hdom
  have hAw : ∀ b, w (τ.hom ((X.presheaf.stalkSpecializes (genericPoint_specializes c)).hom b))
      ≤ 1 := fun b => hOw _ (hdom b)
  have hcη : c ≠ η := by
    rintro rfl
    apply htop
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨b, rfl⟩ := hφ₀s y
    have hmem : algebraMap w.valuationSubring Ω (φ₀.hom b) ∈ liftValuationSubring w O := by
      rw [← hφ₀, hgerm]
      exact (φ.hom b).2
    obtain ⟨_, hres⟩ := hmem
    exact hres
  have hcen := exists_val_eq_one_of_centre g τ w c η hAw φ₀ hφ₀ hcη
  have hϖm : ϖ ∈ maximalIdeal (Localization.AtPrime (g c).asIdeal) :=
    hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ
  have hϖw' : w (algebraMap (X.presheaf.stalk c) Ω
      (algebraMap (Localization.AtPrime (g c).asIdeal) (X.presheaf.stalk c) ϖ)) < 1 := by
    change w (F _) < 1
    rw [hFR]
    exact hm ϖ hϖm
  have hce₀ := he₀ O hO hne htop c φ hφ hgerm
  have hhor' : ∀ 𝔮 : Ideal (X.presheaf.stalk c), 𝔮.IsPrime → 𝔮.height = 1 →
      algebraMap (Localization.AtPrime (g c).asIdeal) (X.presheaf.stalk c) ϖ ∉ 𝔮 →
      ∃ r s : X.presheaf.stalk c, s ∉ 𝔮 ∧
        algebraMap (X.presheaf.stalk c) Ω s * f = algebraMap (X.presheaf.stalk c) Ω r := by
    intro 𝔮 hq h1 hϖq
    have := chart_horizontal hϖ 𝔭 𝔮 h1 hϖq
    refine exists_of_forall_valuationSubring 𝔮
      (fun Q => (∀ t : S, ρR (algebraMap S (Localization.AtPrime (g c).asIdeal) t) ∈ Q) ∧
        ∃ t : S, t ≠ 0 ∧ (ρR (algebraMap S (Localization.AtPrime (g c).asIdeal) t))⁻¹ ∈ Q ∧
          t ∈ (g c).asIdeal) Ag
      (fun Q hP hD hQ => hhor Q hP.1 hP.2 hD hQ) ⟨fun t => ?_, ?_⟩ ?_
    · rw [← hFR]
      exact algebraMap_mem_localizationValuationSubring 𝔮 _
    · obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (g c).asIdeal.primeCompl ϖ
      change IsLocalization.mk' (Localization.AtPrime (g c).asIdeal) a b = ϖ at hab
      have hspec' := IsLocalization.mk'_spec (Localization.AtPrime (g c).asIdeal) a b
      rw [hab] at hspec'
      have hbu : IsUnit (algebraMap S (Localization.AtPrime (g c).asIdeal) (b : S)) :=
        IsLocalization.map_units _ b
      set ι := algebraMap (Localization.AtPrime (g c).asIdeal) (X.presheaf.stalk c)
      have haq : ι (algebraMap S _ a) ∉ 𝔮 := by
        rw [← hspec', map_mul]
        intro hmem
        rcases hq.mem_or_mem hmem with h | h
        · exact hϖq h
        · exact hq.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hbu.map ι))
      refine ⟨a, ?_, ?_, ?_⟩
      · rintro rfl
        rw [map_zero, map_zero] at haq
        exact haq 𝔮.zero_mem
      · rw [← hFR]
        exact inv_algebraMap_mem_localizationValuationSubring 𝔮 haq
      · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime (g c).asIdeal)
          (g c).asIdeal a, ← hspec']
        exact Ideal.mul_mem_right _ _ hϖm
    · intro heq
      obtain ⟨b, hb⟩ := hAg c rfl hce₀
      apply hb
      change algebraMap (X.presheaf.stalk c) Ω b ∈ Ag
      rw [← heq]
      exact algebraMap_mem_localizationValuationSubring 𝔮 b
  exact centre_spec w hnzd hmT O hdom' hϖw' hcen hhor'

end Assembly

section CentreHom

open Centre

variable {C : Type*} [CommRing C] (p0 : Ideal C) [p0.IsPrime] {Tη : Type*} [CommRing Tη]
  [Algebra C Tη] [IsLocalization.AtPrime Tη p0] {Ω : Type*} [Field Ω] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation Ω Γ₀) (F : Tη →+* Ω) (G : C →+* Ω)
  (hFG : ∀ c, F (algebraMap C Tη c) = G c) (hG1 : ∀ c, w (G c) ≤ 1)
  (hGlt : ∀ c, w (G c) < 1 ↔ c ∈ p0)
  (hsurj : ∀ g : Ω, w g ≤ 1 → ∃ c d : C, d ∉ p0 ∧ G d * g = G c)

include hFG hG1 hGlt hsurj in
/-- **The centre of `w`.** If `T` is the localization of `C` at `p₀`, and `G : C → Ω` has `w ≤ 1`
everywhere, `w < 1` exactly on `p₀`, and every element of `𝒪_w` is a fraction `G c / G d` with
`d ∉ p₀`, then `F : T → Ω` factors through a local surjection `T → 𝒪_w`. -/
theorem exists_centre_hom :
    ∃ φ₀ : Tη →+* w.valuationSubring, IsLocalHom φ₀ ∧ (∀ b, F b = φ₀ b) ∧
      Function.Surjective φ₀ := by
  have hGd : ∀ d : C, d ∉ p0 → w (G d) = 1 := fun d hd =>
    le_antisymm (hG1 d) (not_lt.1 fun h => hd ((hGlt d).1 h))
  have hmk : ∀ (c : C) (d : p0.primeCompl),
      F (IsLocalization.mk' Tη c d) * G d = G c := by
    intro c d
    rw [← hFG, ← hFG, ← map_mul, IsLocalization.mk'_spec]
  have hval : ∀ (c : C) (d : p0.primeCompl), w (F (IsLocalization.mk' Tη c d)) = w (G c) := by
    intro c d
    have h := congrArg w (hmk c d)
    rwa [map_mul, hGd d d.2, mul_one] at h
  have hF1 : ∀ b, w (F b) ≤ 1 := fun b => by
    obtain ⟨⟨c, d⟩, rfl⟩ := IsLocalization.mk'_surjective p0.primeCompl b
    rw [hval]
    exact hG1 c
  let φ₀ : Tη →+* w.valuationSubring :=
    F.codRestrict _ fun b => (w.mem_valuationSubring_iff _).2 (hF1 b)
  refine ⟨φ₀, ⟨fun b hb => ?_⟩, fun _ => rfl, fun ⟨g, hg⟩ => ?_⟩
  · by_contra hnu
    have := IsLocalization.AtPrime.isLocalRing Tη p0
    obtain ⟨⟨c, d⟩, rfl⟩ := IsLocalization.mk'_surjective p0.primeCompl b
    have hc : c ∈ p0 := (IsLocalization.AtPrime.mk'_mem_maximal_iff Tη p0 c d).1
      ((IsLocalRing.mem_maximalIdeal _).2 hnu)
    have h1 := val_eq_one_of_isUnit w hb
    change w (F _) = 1 at h1
    rw [hval] at h1
    exact absurd ((hGlt c).2 hc) (by rw [h1]; exact lt_irrefl _)
  · obtain ⟨c, d, hd, hcd⟩ := hsurj g ((w.mem_valuationSubring_iff _).1 hg)
    refine ⟨IsLocalization.mk' Tη c (⟨d, hd⟩ : p0.primeCompl), Subtype.ext ?_⟩
    have hd0 : G d ≠ 0 := fun h => by
      have := hGd d hd
      rw [h, map_zero] at this
      exact zero_ne_one this
    change F _ = g
    apply mul_right_cancel₀ hd0
    rw [hmk c ⟨d, hd⟩, ← hcd, mul_comm]

end CentreHom

section Instantiation

open AlgebraicGeometry CategoryTheory SpecialFibreFunctionField SpecialFibreValuation

variable {S : Type} [CommRing S] {X : Scheme.{0}} [IsIntegral X]
  (e : Spec (CommRingCat.of S) ⟶ X) (s : Spec (CommRingCat.of S))
  [IsDomain (Localization.AtPrime s.asIdeal)]
  [IsDiscreteValuationRing (Localization.AtPrime s.asIdeal)]
  {A₀ : Type} [CommRing A₀] [Algebra (Localization.AtPrime s.asIdeal) A₀]
  (σ : A₀ →ₐ[Localization.AtPrime s.asIdeal] Localization.AtPrime s.asIdeal)
  (φ : Localization.AtPrime (sectionPrime σ) ≃+* X.presheaf.stalk (e s))

/-- The isomorphism `K(X) ≅ Frac A` induced by `φ : A ≅ 𝒪_{X,e(s)}`. -/
def functionFieldHom :
    X.functionField ⟶ CommRingCat.of (FractionRing (Localization.AtPrime (sectionPrime σ))) :=
  CommRingCat.ofHom (IsFractionRing.ringEquivOfRingEquiv (A := X.presheaf.stalk (e s))
    (K := X.functionField) φ.symm).toRingHom

theorem functionFieldHom_bijective : Function.Bijective (functionFieldHom e s σ φ).hom :=
  (IsFractionRing.ringEquivOfRingEquiv (A := X.presheaf.stalk (e s))
    (K := X.functionField) (L := FractionRing (Localization.AtPrime (sectionPrime σ)))
    φ.symm).bijective

/-- Through `functionFieldHom`, the generic germ of `φ a` is `a`. -/
theorem functionFieldHom_germ (a : Localization.AtPrime (sectionPrime σ)) :
    (functionFieldHom e s σ φ).hom
        ((X.presheaf.stalkSpecializes (genericPoint_specializes (e s))).hom (φ a)) =
      algebraMap _ (FractionRing (Localization.AtPrime (sectionPrime σ))) a := by
  change IsFractionRing.ringEquivOfRingEquiv φ.symm
    (algebraMap (X.presheaf.stalk (e s)) X.functionField (φ a)) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, RingEquiv.symm_apply_apply]

variable [IsDomain (Localization.AtPrime (sectionPrime σ))]
  [IsNoetherianRing (Localization.AtPrime (sectionPrime σ))]
  [FaithfulSMul (Localization.AtPrime s.asIdeal) (Localization.AtPrime (sectionPrime σ))]
  {ϖ : Localization.AtPrime s.asIdeal} (hϖ : Irreducible ϖ)
  [IsDomain (Localization.AtPrime (sectionPrime σ) ⧸
    Ideal.span {(algebraMap (Localization.AtPrime s.asIdeal)
      (Localization.AtPrime (sectionPrime σ)) ϖ)})]
  [IsDiscreteValuationRing (Localization.AtPrime (sectionPrime σ) ⧸
    Ideal.span {(algebraMap (Localization.AtPrime s.asIdeal)
      (Localization.AtPrime (sectionPrime σ)) ϖ)})]

include hϖ in
/-- **The identity point is not a centre.** A constant place `O ≠ ⊤` of `κ_w` with a centre at
`e(s)` contains the image of `A / ϖA`, hence equals `ē`. -/
theorem ne_of_isCentre (O : ValuationSubring (ResidueField
      (specialFibreValuation (Localization.AtPrime (sectionPrime σ))
        (FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ).valuationSubring))
    (hne : O ≠ specialFibrePlace (Localization.AtPrime (sectionPrime σ))
      (FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ) (htop : O ≠ ⊤) (c : X)
    (φc : X.presheaf.stalk c ⟶ CommRingCat.of (liftValuationSubring _ O))
    (hgc : ∀ b, (functionFieldHom e s σ φ).hom
      ((X.presheaf.stalkSpecializes (genericPoint_specializes c)).hom b) =
        algebraMap (liftValuationSubring _ O) _ (φc.hom b)) : c ≠ e s := by
  rintro rfl
  refine htop (eq_top_of_specialFibrePlace_le hϖ O (fun a => ?_) hne)
  have hmem : algebraMap _ (FractionRing (Localization.AtPrime (sectionPrime σ))) a ∈
      liftValuationSubring _ O := by
    rw [← functionFieldHom_germ e s σ φ a, hgc]
    exact (φc.hom (φ a)).2
  exact hmem

omit [IsDiscreteValuationRing (Localization.AtPrime (sectionPrime σ) ⧸
  Ideal.span {(algebraMap (Localization.AtPrime s.asIdeal)
    (Localization.AtPrime (sectionPrime σ)) ϖ)})] in
include hϖ in
set_option maxHeartbeats 800000 in
/-- **The centre of `w` on `X`.** The prime `(ϖ)` of `𝒪_{X,e(s)} ≅ A` is the generic point `η` of
the special-fibre component through `e(s)`, and `τ` restricts to a local surjection
`𝒪_{X,η} → 𝒪_w`. -/
theorem exists_generic_centre :
    ∃ (η : X) (φ₀ : X.presheaf.stalk η ⟶ CommRingCat.of
      (specialFibreValuation (Localization.AtPrime (sectionPrime σ))
        (FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ).valuationSubring),
      IsLocalHom φ₀.hom ∧
      (∀ b, (functionFieldHom e s σ φ).hom
        ((X.presheaf.stalkSpecializes (genericPoint_specializes η)).hom b) =
          algebraMap _ (FractionRing (Localization.AtPrime (sectionPrime σ))) (φ₀.hom b)) ∧
      Function.Surjective φ₀.hom := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := e s) (U := ⊤) trivial
  let _ : Algebra Γ(X, V) (X.presheaf.stalk (e s)) := (X.presheaf.germ V (e s) hxV).hom.toAlgebra
  have hp : IsLocalization.AtPrime (X.presheaf.stalk (e s)) (hV.primeIdealOf ⟨e s, hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨e s, hxV⟩
  let P := Ideal.span {(algebraMap (Localization.AtPrime s.asIdeal)
    (Localization.AtPrime (sectionPrime σ)) ϖ)}
  have hP : P.IsPrime := isPrime_span_algebraMap _
  let ψ : Γ(X, V) →+* Localization.AtPrime (sectionPrime σ) :=
    φ.symm.toRingHom.comp (X.presheaf.germ V (e s) hxV).hom
  let p0 := P.comap ψ
  have hp0 : p0.IsPrime := Ideal.comap_isPrime ψ P
  let y : Spec Γ(X, V) := ⟨p0, hp0⟩
  have hη : hV.fromSpec y ∈ V := by
    have h : hV.fromSpec y ∈ (V : Set X) := hV.range_fromSpec ▸ ⟨y, rfl⟩
    exact h
  let algη : Algebra Γ(X, V) (X.presheaf.stalk (hV.fromSpec y)) :=
    (X.presheaf.germ V (hV.fromSpec y) hη).hom.toAlgebra
  have hηl : IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec y)) p0 :=
    hV.isLocalization_stalk' y hη
  -- `η` specializes to `e(s)`
  have hle : p0 ≤ (hV.primeIdealOf ⟨e s, hxV⟩).asIdeal := by
    intro c hc
    rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk (e s))
      (hV.primeIdealOf ⟨e s, hxV⟩).asIdeal]
    change algebraMap Γ(X, V) (X.presheaf.stalk (e s)) c ∈ IsLocalRing.maximalIdeal _
    have hPm : ψ c ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (sectionPrime σ)) := by
      refine (IsLocalRing.le_maximalIdeal hP.ne_top) hc
    have h1 : φ (ψ c) = algebraMap Γ(X, V) (X.presheaf.stalk (e s)) c := by
      change φ (φ.symm _) = _
      rw [RingEquiv.apply_symm_apply]
      rfl
    rw [← h1]
    exact (map_mem_nonunits_iff
      (φ : Localization.AtPrime (sectionPrime σ) →+* X.presheaf.stalk (e s)) _).2 hPm
  have hηs : hV.fromSpec y ⤳ e s := by
    have h := ((PrimeSpectrum.le_iff_specializes y (hV.primeIdealOf ⟨e s, hxV⟩)).1 hle).map
      hV.fromSpec.continuous
    rwa [hV.fromSpec_primeIdealOf] at h
  -- the maps `F` and `G`
  let F : X.presheaf.stalk (hV.fromSpec y) →+*
      FractionRing (Localization.AtPrime (sectionPrime σ)) :=
    (X.presheaf.stalkSpecializes (genericPoint_specializes _) ≫ functionFieldHom e s σ φ).hom
  let G : Γ(X, V) →+* FractionRing (Localization.AtPrime (sectionPrime σ)) :=
    (algebraMap _ _).comp ψ
  have hFG : ∀ c, F (algebraMap Γ(X, V) (X.presheaf.stalk (hV.fromSpec y)) c) = G c := by
    intro c
    have h1 : algebraMap Γ(X, V) (X.presheaf.stalk (hV.fromSpec y)) c =
        (X.presheaf.stalkSpecializes hηs).hom ((X.presheaf.germ V (e s) hxV).hom c) :=
      (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hxV hηs c).symm
    have h2 := congrArg (fun m => m.hom ((X.presheaf.germ V (e s) hxV).hom c))
      (TopCat.Presheaf.stalkSpecializes_comp X.presheaf (genericPoint_specializes _) hηs)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
    change (functionFieldHom e s σ φ).hom
      ((X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom _) = _
    rw [h1, h2]
    have h3 : (X.presheaf.germ V (e s) hxV).hom c = φ (ψ c) := by
      change _ = φ (φ.symm _)
      rw [RingEquiv.apply_symm_apply]
    rw [h3, functionFieldHom_germ]
    rfl
  have hG1 : ∀ c, specialFibreValuation (Localization.AtPrime (sectionPrime σ))
      (FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ (G c) ≤ 1 := fun c =>
    specialFibreValuation_algebraMap_le_one hϖ (ψ c)
  have hGlt : ∀ c, specialFibreValuation (Localization.AtPrime (sectionPrime σ))
      (FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ (G c) < 1 ↔ c ∈ p0 := fun c =>
    specialFibreValuation_algebraMap_lt_one_iff hϖ (ψ c)
  have hunit : ∀ d : Γ(X, V), d ∉ (hV.primeIdealOf ⟨e s, hxV⟩).asIdeal → IsUnit (ψ d) := by
    intro d hd
    have h := IsLocalization.map_units (X.presheaf.stalk (e s))
      (⟨d, hd⟩ : (hV.primeIdealOf ⟨e s, hxV⟩).asIdeal.primeCompl)
    exact h.map φ.symm.toRingHom
  have hfrac : ∀ a : Localization.AtPrime (sectionPrime σ), ∃ c d : Γ(X, V),
      d ∉ (hV.primeIdealOf ⟨e s, hxV⟩).asIdeal ∧ ψ c = a * ψ d := by
    intro a
    obtain ⟨⟨c, d⟩, hcd⟩ := IsLocalization.mk'_surjective
      (hV.primeIdealOf ⟨e s, hxV⟩).asIdeal.primeCompl (φ a)
    refine ⟨c, d, d.2, ?_⟩
    have h := IsLocalization.mk'_spec (X.presheaf.stalk (e s)) c d
    change IsLocalization.mk' _ c d = φ a at hcd
    rw [hcd] at h
    change φ.symm (algebraMap _ _ c) = a * φ.symm (algebraMap _ _ (d : Γ(X, V)))
    rw [← h, map_mul, RingEquiv.symm_apply_apply]
  have hsurj : ∀ g, specialFibreValuation (Localization.AtPrime (sectionPrime σ))
      (FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ g ≤ 1 →
      ∃ c d : Γ(X, V), d ∉ p0 ∧
      G d * g = G c := by
    intro g hg
    obtain ⟨r, t, ht, hrt⟩ := (specialFibreValuation_le_one_iff hϖ g).1 hg
    obtain ⟨c1, d1, hd1, h1⟩ := hfrac r
    obtain ⟨c2, d2, hd2, h2⟩ := hfrac t
    refine ⟨c1 * d2, d1 * c2, ?_, ?_⟩
    · change ψ (d1 * c2) ∉ P
      rw [map_mul, h2]
      intro hmem
      rcases hP.mem_or_mem hmem with h | h
      · exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hunit d1 hd1))
      rcases hP.mem_or_mem h with h' | h'
      · exact ht h'
      · exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (hunit d2 hd2))
    · simp only [G, RingHom.comp_apply, map_mul, h1, h2]
      rw [← hrt]
      ring
  have key := @exists_centre_hom Γ(X, V) _ p0 hp0
    (X.presheaf.stalk (hV.fromSpec y)) _ algη hηl _ _ _ _
    (specialFibreValuation (Localization.AtPrime (sectionPrime σ))
      (FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ) F G hFG hG1 hGlt hsurj
  obtain ⟨φ₀, hloc, hF, hφs⟩ := key
  refine ⟨hV.fromSpec y, CommRingCat.ofHom φ₀, hloc, fun b => ?_, hφs⟩
  have h := hF b
  simp only [F, CommRingCat.hom_comp, RingHom.comp_apply] at h
  rw [h]
  rfl

include hϖ in
set_option maxHeartbeats 800000 in
/-- **`hcentre` at a finite place (`exists_centre_data`).** Let `g : X ⟶ Spec S` be proper and
smooth of relative dimension one with `X` integral, `s` a point with `R = S_s` a discrete
valuation ring of characteristic zero with perfect residue field and uniformizer `ϖ`, and
`φ : A ≅ 𝒪_{X,e(s)}` for the local ring `A` of the chart at the section prime. Put `Ω = Frac A`,
`w` the special-fibre valuation and `ē` the special-fibre place. The remaining inputs are explicit:
`hρ` (the base map `R → Ω` is the one of `g` at the generic point), `htr` (`κ_w` has
transcendence degree at most one) and `hAg` (`Ag` contains the local ring of no point `c ≠ e(s)`
over `s`); the point at which `w` is centred is `exists_generic_centre`.
Then every constant place `O ≠ ē` has a centre as required by `reduce_mem_polePart`. -/
theorem exists_centre_data (g : X ⟶ Spec (CommRingCat.of S)) [IsProper g]
    [SmoothOfRelativeDimension 1 g]
    [PerfectField (ResidueField (Localization.AtPrime s.asIdeal))]
    [CharZero (Localization.AtPrime s.asIdeal)]
    (htr : letI := (residueHom (specialFibreValuation (Localization.AtPrime (sectionPrime σ))
        (FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ)
        (specialFibreValuation_algebraMap_base_le_one hϖ)
        (specialFibreValuation_algebraMap_base_lt_one hϖ)).toAlgebra
      TrdegLeOne (ResidueField (Localization.AtPrime s.asIdeal))
        (ResidueField (specialFibreValuation (Localization.AtPrime (sectionPrime σ))
          (FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ).valuationSubring))
    (hρ : (Spec.map (functionFieldHom e s σ φ) ≫ X.fromSpecStalk (genericPoint X)) ≫ g =
      Spec.map (CommRingCat.ofHom ((algebraMap (Localization.AtPrime s.asIdeal)
        (FractionRing (Localization.AtPrime (sectionPrime σ)))).comp
          (algebraMap S (Localization.AtPrime s.asIdeal)))))
    (Ag : ValuationSubring (FractionRing (Localization.AtPrime (sectionPrime σ))))
    (hAg : ∀ c : X, g c = s → c ≠ e s → ∃ b : X.presheaf.stalk c,
      (functionFieldHom e s σ φ).hom
        ((X.presheaf.stalkSpecializes (genericPoint_specializes c)).hom b) ∉ Ag)
    {f : FractionRing (Localization.AtPrime (sectionPrime σ))}
    (hhor : ∀ Q : ValuationSubring (FractionRing (Localization.AtPrime (sectionPrime σ))),
      (∀ t : S, algebraMap (Localization.AtPrime s.asIdeal) _
        (algebraMap S (Localization.AtPrime s.asIdeal) t) ∈ Q) →
      (∃ t : S, t ≠ 0 ∧ (algebraMap (Localization.AtPrime s.asIdeal) _
        (algebraMap S (Localization.AtPrime s.asIdeal) t))⁻¹ ∈ Q ∧ t ∈ s.asIdeal) →
      IsDiscreteValuationRing Q → Q ≠ Ag → f ∈ Q) :
    letI := (residueHom (specialFibreValuation (Localization.AtPrime (sectionPrime σ))
        (FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ)
        (specialFibreValuation_algebraMap_base_le_one hϖ)
        (specialFibreValuation_algebraMap_base_lt_one hϖ)).toAlgebra
    ∀ O : ValuationSubring (ResidueField (specialFibreValuation
        (Localization.AtPrime (sectionPrime σ))
        (FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ).valuationSubring),
      IsConstPlace (ResidueField (Localization.AtPrime s.asIdeal)) O →
      O ≠ specialFibrePlace (Localization.AtPrime (sectionPrime σ))
        (FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ →
      ∃ (Ac : Subring (FractionRing (Localization.AtPrime (sectionPrime σ)))) (π : Ac),
        (∀ a ∈ Ac, a ∈ liftValuationSubring (specialFibreValuation
          (Localization.AtPrime (sectionPrime σ))
          (FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ) O) ∧
        (∀ g : FractionRing (Localization.AtPrime (sectionPrime σ)),
          (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 →
            ∃ r u : Ac, u ∉ 𝔮 ∧
              (u : FractionRing (Localization.AtPrime (sectionPrime σ))) * g = r) → g ∈ Ac) ∧
        (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → π ∈ 𝔮 →
          ∀ g : FractionRing (Localization.AtPrime (sectionPrime σ)),
            specialFibreValuation (Localization.AtPrime (sectionPrime σ))
              (FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ g ≤ 1 →
            ∃ r u : Ac, u ∉ 𝔮 ∧
              (u : FractionRing (Localization.AtPrime (sectionPrime σ))) * g = r) ∧
        (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → π ∉ 𝔮 →
          ∃ r u : Ac, u ∉ 𝔮 ∧
            (u : FractionRing (Localization.AtPrime (sectionPrime σ))) * f = r) := by
  have hR := specialFibreValuation_algebraMap_base_le_one
    (A := Localization.AtPrime (sectionPrime σ))
    (Ω := FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ
  have hm := specialFibreValuation_algebraMap_base_lt_one
    (A := Localization.AtPrime (sectionPrime σ))
    (Ω := FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ
  let _ := (residueHom (specialFibreValuation (Localization.AtPrime (sectionPrime σ))
    (FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ) hR hm).toAlgebra
  have hk : ∀ r, algebraMap (ResidueField (Localization.AtPrime s.asIdeal)) _ (residue _ r) =
      reduce (specialFibreValuation (Localization.AtPrime (sectionPrime σ))
        (FractionRing (Localization.AtPrime (sectionPrime σ))) hϖ)
        (algebraMap (Localization.AtPrime s.asIdeal) _ r) (hR r) := by
    intro r
    have := isLocalHom_toIntegers _ hR hm
    change residueHom _ hR hm (residue _ r) = _
    rw [residueHom, ResidueField.map_residue]
    rfl
  have hϖm : ϖ ∈ maximalIdeal (Localization.AtPrime s.asIdeal) :=
    hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ
  have hϖ0 : algebraMap (Localization.AtPrime s.asIdeal)
      (FractionRing (Localization.AtPrime (sectionPrime σ))) ϖ ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply _ (Localization.AtPrime (sectionPrime σ))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
      (algebraMap_ne_zero_of_irreducible _ hϖ)
  obtain ⟨η, φ₀, hφ₀l, hφ₀, hφ₀s⟩ := exists_generic_centre e s σ φ hϖ
  refine hcentre_of_smoothModel g (functionFieldHom e s σ φ) (functionFieldHom_bijective e s σ φ)
    hϖ0 (hm ϖ hϖm) (fun x hx => specialFibreValuation_eq_zpow hϖ hx) s hϖ
    (algebraMap _ _) hR hm hk htr hρ η φ₀ hφ₀ hφ₀s _ (e s) ?_ Ag hAg hhor
  intro O hO hne htop c φc _ hgc
  exact ne_of_isCentre e s σ φ hϖ O hne htop c φc hgc

end Instantiation

end CentreData

end ZInQ.Contrib.CMHeight62Full
