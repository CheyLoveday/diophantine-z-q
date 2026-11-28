import ZInQKernel.Contrib.OneProof.CMHeight62Full.Centre
import ZInQKernel.Contrib.OneProof.CMHeight62Full.HorizontalPrimes
import ZInQKernel.Contrib.OneProof.CMHeight62Full.SpecialFibreDVR
import ZInQKernel.Contrib.OneProof.CMHeight62Full.LocalStructureScheme

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

end CentreData

end ZInQ.Contrib.CMHeight62Full
