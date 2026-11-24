import ZInQKernel.Contrib.OneProof.RC.ModelGeneric4.QuotientFunctionField
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_veluQuotient2_Delta_ne_zero
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_stepCurve_stepSubgroup_two_eq

/-! # The order-two Vélu step as a map of function fields

The vendored order-two step `veluQuotient2` comes only with its point map `veluPointMap2`. Here the
same rational formulas `x ↦ x + G/(x - x₀)` and `y ↦ y - G(a₁(x - x₀) + y - y₀)/(x - x₀)²`
define a map of function fields, and its restriction of places is the vendored point map. This is
the missing ingredient for the composite at even level. -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric4

open AlgebraicCurve Polynomial
open P2MW.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.WeierstrassCurve.Affine

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false

attribute [-instance] WeierstrassCurve.Affine.CoordinateRing.moduleFinite
  WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral
  WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions
  WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions
  WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions

variable {F : Type} [Field F] [DecidableEq F] (W : WeierstrassCurve F) (x₀ y₀ : F)

/-- The generic first coordinate of the order-two Vélu map, `x + G/(x - x₀)`. -/
noncomputable def twoXFun : W.toAffine.FunctionField :=
  polyToFunctionField W.toAffine X +
    algebraMap F _ (W.veluGx x₀ y₀) / (polyToFunctionField W.toAffine X - algebraMap F _ x₀)

/-- The generic second coordinate of the order-two Vélu map,
`y - G(a₁(x - x₀) + y - y₀)/(x - x₀)²`. -/
noncomputable def twoYFun : W.toAffine.FunctionField :=
  yGen W.toAffine - algebraMap F _ (W.veluGx x₀ y₀) *
    (algebraMap F _ W.a₁ * (polyToFunctionField W.toAffine X - algebraMap F _ x₀) +
      yGen W.toAffine - algebraMap F _ y₀) /
    (polyToFunctionField W.toAffine X - algebraMap F _ x₀) ^ 2

omit [DecidableEq F] in
theorem veluQuotient2_map {K : Type} [Field K] (f : F →+* K) :
    (W.veluQuotient2 x₀ y₀).map f = (W.map f).veluQuotient2 (f x₀) (f y₀) := by
  ext <;> simp [veluQuotient2, veluGx, b₂, map_ofNat]

omit [DecidableEq F] in
theorem twoFun_equation (h2 : (2 : F) ≠ 0) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) :
    ((W.veluQuotient2 x₀ y₀).map (algebraMap F W.toAffine.FunctionField)).toAffine.Equation
      (twoXFun W x₀ y₀) (twoYFun W x₀ y₀) := by
  let φ := algebraMap F W.toAffine.FunctionField
  have hP := equation_map_polyToFunctionField_yGen (W := W.toAffine)
  have hQ' : (W.map φ).toAffine.Equation (φ x₀) (φ y₀) :=
    (W.toAffine.map_equation φ.injective x₀ y₀).mpr hQ
  have hgy' : (W.map φ).veluGy (φ x₀) (φ y₀) = 0 := by
    have : (W.map φ).veluGy (φ x₀) (φ y₀) = φ (W.veluGy x₀ y₀) := by
      simp [veluGy, map_ofNat]
    rw [this, hgy, map_zero]
  have hx : polyToFunctionField W.toAffine X ≠ φ x₀ := polyToFunctionField_X_ne_algebraMap x₀
  have h2' : (2 : W.toAffine.FunctionField) ≠ 0 := by
    rw [show (2 : W.toAffine.FunctionField) = φ 2 by simp [map_ofNat]]
    exact (map_ne_zero φ).mpr h2
  have key := (W.map φ).velu2_map_equation h2' hP hQ' hgy' hx
  rw [veluQuotient2_map]
  have hG : (W.map φ).veluGx (φ x₀) (φ y₀) = φ (W.veluGx x₀ y₀) := by
    simp [veluGx, map_ofNat]
  simp only [velu2X, velu2Y, hG, map_a₁] at key
  exact key

omit [DecidableEq F] in
theorem twoFun_eval₂_polynomial (h2 : (2 : F) ≠ 0) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) :
    ((W.veluQuotient2 x₀ y₀).toAffine.polynomial).eval₂
        (Polynomial.aeval (twoXFun W x₀ y₀) : F[X] →ₐ[F] W.toAffine.FunctionField).toRingHom
        (twoYFun W x₀ y₀) = 0 := by
  have heq := twoFun_equation W x₀ y₀ h2 hQ hgy
  rw [WeierstrassCurve.Affine.equation_iff'] at heq
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at heq
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul, map_pow,
    Polynomial.aeval_C, Polynomial.aeval_X]
  linear_combination heq

omit [DecidableEq F] in
/-- The generic first coordinate is transcendental: the generic abscissa is a root of a monic
quadratic over the algebra it generates. -/
theorem transcendental_twoXFun : Transcendental F (twoXFun W x₀ y₀) := by
  intro halg
  apply transcendental_polyToFunctionField_X (W := W.toAffine)
  have hint : _root_.IsIntegral F (twoXFun W x₀ y₀) := halg.isIntegral
  let S := Algebra.adjoin F ({twoXFun W x₀ y₀} : Set W.toAffine.FunctionField)
  have hS : Algebra.IsIntegral F S :=
    ⟨fun s => by
      have := adjoin_le_integralClosure hint s.2
      exact (isIntegral_algHom_iff S.val Subtype.val_injective).mp this⟩
  have hu : twoXFun W x₀ y₀ ∈ S := Algebra.subset_adjoin rfl
  have hd : polyToFunctionField W.toAffine X - algebraMap F W.toAffine.FunctionField x₀ ≠ 0 :=
    sub_ne_zero.mpr (polyToFunctionField_X_ne_algebraMap x₀)
  let p : S[X] := X ^ 2 + (C (-(⟨twoXFun W x₀ y₀, hu⟩ + algebraMap F S x₀)) * X +
    C (⟨twoXFun W x₀ y₀, hu⟩ * algebraMap F S x₀ + algebraMap F S (W.veluGx x₀ y₀)))
  have hmonic : p.Monic := monic_X_pow_add (by exact_mod_cast degree_linear_lt)
  have hroot : aeval (polyToFunctionField W.toAffine X) p = 0 := by
    simp only [p, map_add, map_mul, map_pow, aeval_X, aeval_C]
    change polyToFunctionField W.toAffine X ^ 2 + (-(twoXFun W x₀ y₀ +
      algebraMap F W.toAffine.FunctionField x₀) * polyToFunctionField W.toAffine X +
      (twoXFun W x₀ y₀ * algebraMap F W.toAffine.FunctionField x₀ +
      algebraMap F W.toAffine.FunctionField (W.veluGx x₀ y₀))) = 0
    simp only [twoXFun]
    field_simp
    ring
  have hxS : _root_.IsIntegral S (polyToFunctionField W.toAffine X) := ⟨p, hmonic, hroot⟩
  exact (isIntegral_trans _ hxS).isAlgebraic

variable {W x₀ y₀}
variable (h2 : (2 : F) ≠ 0) (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)

omit [DecidableEq F] in
include h2 hQ hgy in
/-- The order-two Vélu map on coordinate rings. -/
noncomputable def twoCoordHom :
    (W.veluQuotient2 x₀ y₀).toAffine.CoordinateRing →ₐ[F] W.toAffine.FunctionField where
  __ := AdjoinRoot.lift
    (Polynomial.aeval (twoXFun W x₀ y₀) : F[X] →ₐ[F] W.toAffine.FunctionField).toRingHom
    (twoYFun W x₀ y₀) (twoFun_eval₂_polynomial W x₀ y₀ h2 hQ hgy)
  commutes' c := by
    show AdjoinRoot.lift _ _ (twoFun_eval₂_polynomial W x₀ y₀ h2 hQ hgy)
      (algebraMap F _ c) = algebraMap F W.toAffine.FunctionField c
    rw [CoordinateRing.algebraMap_eq_mk_C_C, AdjoinRoot.lift_mk, eval₂_C]
    exact Polynomial.aeval_C _ c

omit [DecidableEq F] in
theorem twoCoordHom_mk (g : Polynomial (Polynomial F)) :
    twoCoordHom h2 hQ hgy (WeierstrassCurve.Affine.CoordinateRing.mk
        (W.veluQuotient2 x₀ y₀).toAffine g) =
      g.eval₂ (Polynomial.aeval (twoXFun W x₀ y₀) : F[X] →ₐ[F] W.toAffine.FunctionField).toRingHom
        (twoYFun W x₀ y₀) :=
  AdjoinRoot.lift_mk (twoFun_eval₂_polynomial W x₀ y₀ h2 hQ hgy) g

omit [DecidableEq F] in
theorem twoCoordHom_comp_algebraMap :
    (twoCoordHom h2 hQ hgy).toRingHom.comp
        (algebraMap F[X] (W.veluQuotient2 x₀ y₀).toAffine.CoordinateRing) =
      (Polynomial.aeval (twoXFun W x₀ y₀) : F[X] →ₐ[F] W.toAffine.FunctionField).toRingHom := by
  refine RingHom.ext fun q => ?_
  show twoCoordHom h2 hQ hgy (algebraMap F[X] _ q) = _
  rw [algebraMap_polynomial_eq_mk_C, twoCoordHom_mk, eval₂_C]

omit [DecidableEq F] in
theorem twoCoordHom_injective : Function.Injective (twoCoordHom h2 hQ hgy) := by
  have hker : RingHom.ker (twoCoordHom h2 hQ hgy).toRingHom = ⊥ := by
    haveI : Module.Finite F[X] (W.veluQuotient2 x₀ y₀).toAffine.CoordinateRing :=
      Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis
        (W.veluQuotient2 x₀ y₀).toAffine)
    refine Ideal.eq_bot_of_under_eq_bot (R := F[X]) ?_
    rw [Ideal.under_def, RingHom.comap_ker, twoCoordHom_comp_algebraMap,
      ← RingHom.injective_iff_ker_eq_bot]
    exact (injective_iff_map_eq_zero _).mpr fun q hq =>
      transcendental_iff.mp (transcendental_twoXFun W x₀ y₀) q hq
  exact (RingHom.injective_iff_ker_eq_bot (twoCoordHom h2 hQ hgy).toRingHom).mpr hker

/-- The order-two Vélu map on function fields. -/
noncomputable def twoFFHom :
    (W.veluQuotient2 x₀ y₀).toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField :=
  IsFractionRing.liftAlgHom (twoCoordHom_injective h2 hQ hgy)

omit [DecidableEq F] in
theorem twoFFHom_algebraMap (r : (W.veluQuotient2 x₀ y₀).toAffine.CoordinateRing) :
    twoFFHom h2 hQ hgy (algebraMap _ (W.veluQuotient2 x₀ y₀).toAffine.FunctionField r) =
      twoCoordHom h2 hQ hgy r :=
  IsFractionRing.lift_algebraMap (twoCoordHom_injective h2 hQ hgy) r

omit [DecidableEq F] in
theorem twoFFHom_X :
    twoFFHom h2 hQ hgy (polyToFunctionField (W.veluQuotient2 x₀ y₀).toAffine X) =
      twoXFun W x₀ y₀ := by
  rw [polyToFunctionField_apply, twoFFHom_algebraMap, algebraMap_polynomial_eq_mk_C,
    twoCoordHom_mk, eval₂_C]
  exact Polynomial.aeval_X _

omit [DecidableEq F] in
theorem twoFFHom_Y :
    twoFFHom h2 hQ hgy (yGen (W.veluQuotient2 x₀ y₀).toAffine) = twoYFun W x₀ y₀ := by
  show twoFFHom h2 hQ hgy (algebraMap _ _ (WeierstrassCurve.Affine.CoordinateRing.mk
    (W.veluQuotient2 x₀ y₀).toAffine (Polynomial.X : Polynomial (Polynomial F)))) = _
  rw [twoFFHom_algebraMap, twoCoordHom_mk]
  exact eval₂_X _ _

omit [DecidableEq F] in
theorem isIntegral_X_twoFFHom :
    letI : Algebra (W.veluQuotient2 x₀ y₀).toAffine.FunctionField W.toAffine.FunctionField :=
      (twoFFHom h2 hQ hgy).toRingHom.toAlgebra
    _root_.IsIntegral (W.veluQuotient2 x₀ y₀).toAffine.FunctionField
      (polyToFunctionField W.toAffine X) := by
  letI : Algebra (W.veluQuotient2 x₀ y₀).toAffine.FunctionField W.toAffine.FunctionField :=
    (twoFFHom h2 hQ hgy).toRingHom.toAlgebra
  let V := (W.veluQuotient2 x₀ y₀).toAffine.FunctionField
  let u : V := polyToFunctionField (W.veluQuotient2 x₀ y₀).toAffine X
  have hd : polyToFunctionField W.toAffine X - algebraMap F W.toAffine.FunctionField x₀ ≠ 0 :=
    sub_ne_zero.mpr (polyToFunctionField_X_ne_algebraMap x₀)
  let p : V[X] := X ^ 2 + (C (-(u + algebraMap F V x₀)) * X +
    C (u * algebraMap F V x₀ + algebraMap F V (W.veluGx x₀ y₀)))
  have hu : algebraMap V W.toAffine.FunctionField u = twoXFun W x₀ y₀ := twoFFHom_X h2 hQ hgy
  have hc : ∀ c : F, algebraMap V W.toAffine.FunctionField (algebraMap F V c) =
      algebraMap F W.toAffine.FunctionField c := fun c => (twoFFHom h2 hQ hgy).commutes c
  have e1 : algebraMap V W.toAffine.FunctionField (-(u + algebraMap F V x₀)) =
      -(twoXFun W x₀ y₀ + algebraMap F W.toAffine.FunctionField x₀) := by
    change twoFFHom h2 hQ hgy _ = _
    rw [map_neg, map_add, twoFFHom_X, AlgHom.commutes]
  have e2 : algebraMap V W.toAffine.FunctionField
      (u * algebraMap F V x₀ + algebraMap F V (W.veluGx x₀ y₀)) =
      twoXFun W x₀ y₀ * algebraMap F W.toAffine.FunctionField x₀ +
        algebraMap F W.toAffine.FunctionField (W.veluGx x₀ y₀) := by
    change twoFFHom h2 hQ hgy _ = _
    rw [map_add, map_mul, twoFFHom_X, AlgHom.commutes, AlgHom.commutes]
  have hroot : aeval (polyToFunctionField W.toAffine X) p = 0 := by
    simp only [p, map_add, map_mul, map_pow, aeval_X, aeval_C, e1]
    rw [hu, hc, hc]
    simp only [twoXFun]
    field_simp
    ring
  exact ⟨p, monic_X_pow_add (by exact_mod_cast degree_linear_lt), hroot⟩

omit [DecidableEq F] in
theorem adjoin_X_yGen_eq_top_twoFFHom :
    letI : Algebra (W.veluQuotient2 x₀ y₀).toAffine.FunctionField W.toAffine.FunctionField :=
      (twoFFHom h2 hQ hgy).toRingHom.toAlgebra
    IntermediateField.adjoin (W.veluQuotient2 x₀ y₀).toAffine.FunctionField
        ({polyToFunctionField W.toAffine X, yGen W.toAffine} : Set W.toAffine.FunctionField) =
      ⊤ := by
  letI : Algebra (W.veluQuotient2 x₀ y₀).toAffine.FunctionField W.toAffine.FunctionField :=
    (twoFFHom h2 hQ hgy).toRingHom.toAlgebra
  rw [eq_top_iff]
  rintro z -
  set L := IntermediateField.adjoin (W.veluQuotient2 x₀ y₀).toAffine.FunctionField
    ({polyToFunctionField W.toAffine X, yGen W.toAffine} : Set W.toAffine.FunctionField)
  have hconst : ∀ c : F, algebraMap F W.toAffine.FunctionField c ∈ L := fun c => by
    rw [← (twoFFHom h2 hQ hgy).commutes c]; exact L.algebraMap_mem _
  have hxmem : polyToFunctionField W.toAffine X ∈ L :=
    IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  have hymem : yGen W.toAffine ∈ L :=
    IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)
  have hpoly : ∀ q : F[X], polyToFunctionField W.toAffine q ∈ L := fun q => by
    induction q using Polynomial.induction_on' with
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | monomial n c =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, polyToFunctionField_C]
        exact mul_mem (hconst c) (pow_mem hxmem n)
  have hcr : ∀ r : W.toAffine.CoordinateRing,
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField r ∈ L := fun r => by
    obtain ⟨a, b, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq r
    rw [algebraMap_smul_basis]
    exact add_mem (hpoly a) (mul_mem (hpoly b) hymem)
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective (A := W.toAffine.CoordinateRing) z
  rw [← hab]; exact div_mem (hcr a) (hcr b)

omit [DecidableEq F] in
theorem twoFFHom_finiteAlong : FiniteAlong F (twoFFHom h2 hQ hgy) := by
  letI : Algebra (W.veluQuotient2 x₀ y₀).toAffine.FunctionField W.toAffine.FunctionField :=
    (twoFFHom h2 hQ hgy).toRingHom.toAlgebra
  show Module.Finite (W.veluQuotient2 x₀ y₀).toAffine.FunctionField W.toAffine.FunctionField
  have hxint := isIntegral_X_twoFFHom h2 hQ hgy
  set Lx := IntermediateField.adjoin (W.veluQuotient2 x₀ y₀).toAffine.FunctionField
    ({polyToFunctionField W.toAffine X} : Set W.toAffine.FunctionField) with hLx
  haveI hxfd : FiniteDimensional (W.veluQuotient2 x₀ y₀).toAffine.FunctionField Lx :=
    IntermediateField.adjoin.finiteDimensional hxint
  have hyint : _root_.IsIntegral Lx (yGen W.toAffine) := by
    have hyFx : _root_.IsIntegral F[X] (yGen W.toAffine) := by
      haveI : Module.Finite F[X] W.toAffine.CoordinateRing :=
        Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine)
      show _root_.IsIntegral F[X]
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
            (Polynomial.X : Polynomial (Polynomial F))))
      exact ((Algebra.IsIntegral.of_finite F[X] W.toAffine.CoordinateRing).isIntegral _).map
        (IsScalarTower.toAlgHom F[X] W.toAffine.CoordinateRing W.toAffine.FunctionField)
    have halg : ∀ r : F[X], (algebraMap F[X] W.toAffine.FunctionField) r ∈ Lx := by
      intro r
      induction r using Polynomial.induction_on' with
      | add f g hf hg => rw [map_add]; exact add_mem hf hg
      | monomial n c =>
          rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow,
            show algebraMap F[X] W.toAffine.FunctionField (C c)
              = algebraMap F W.toAffine.FunctionField c from rfl,
            show algebraMap F[X] W.toAffine.FunctionField X
              = polyToFunctionField W.toAffine X from rfl,
            ← (twoFFHom h2 hQ hgy).commutes c]
          exact mul_mem (IntermediateField.algebraMap_mem _ _)
            (pow_mem (IntermediateField.mem_adjoin_simple_self _ _) n)
    obtain ⟨q, hqmon, hq0⟩ := hyFx
    let φ : F[X] →+* Lx :=
      (algebraMap F[X] W.toAffine.FunctionField).codRestrict Lx.toSubring halg
    refine ⟨q.map φ, hqmon.map φ, ?_⟩
    rw [Polynomial.eval₂_map,
      show (algebraMap Lx W.toAffine.FunctionField).comp φ
          = algebraMap F[X] W.toAffine.FunctionField from RingHom.ext fun _ => rfl]
    exact hq0
  have hyint' : _root_.IsIntegral (W.veluQuotient2 x₀ y₀).toAffine.FunctionField
      (yGen W.toAffine) :=
    haveI : Algebra.IsIntegral (W.veluQuotient2 x₀ y₀).toAffine.FunctionField Lx :=
      Algebra.IsIntegral.of_finite (W.veluQuotient2 x₀ y₀).toAffine.FunctionField Lx
    haveI : IsScalarTower (W.veluQuotient2 x₀ y₀).toAffine.FunctionField Lx
        W.toAffine.FunctionField := IntermediateField.isScalarTower_mid' Lx
    isIntegral_trans (R := (W.veluQuotient2 x₀ y₀).toAffine.FunctionField) (A := Lx)
      (yGen W.toAffine) hyint
  have hfd : FiniteDimensional (W.veluQuotient2 x₀ y₀).toAffine.FunctionField
      (IntermediateField.adjoin (W.veluQuotient2 x₀ y₀).toAffine.FunctionField
        ({polyToFunctionField W.toAffine X, yGen W.toAffine}
          : Set W.toAffine.FunctionField)) := by
    refine IntermediateField.finiteDimensional_adjoin fun z hz => ?_
    rcases hz with rfl | rfl
    · exact hxint
    · exact hyint'
  rw [adjoin_X_yGen_eq_top_twoFFHom h2 hQ hgy] at hfd
  exact (IntermediateField.topEquiv (F := (W.veluQuotient2 x₀ y₀).toAffine.FunctionField)
    (E := W.toAffine.FunctionField)).toLinearEquiv.finiteDimensional

omit [DecidableEq F] in
theorem twoFFHom_isIntegral : (twoFFHom h2 hQ hgy).toRingHom.IsIntegral := by
  letI : Algebra (W.veluQuotient2 x₀ y₀).toAffine.FunctionField W.toAffine.FunctionField :=
    (twoFFHom h2 hQ hgy).toRingHom.toAlgebra
  haveI : Module.Finite (W.veluQuotient2 x₀ y₀).toAffine.FunctionField W.toAffine.FunctionField :=
    twoFFHom_finiteAlong h2 hQ hgy
  exact fun z => (Algebra.IsIntegral.of_finite _ _).isIntegral z

end WeierstrassCurve.ModelLevels.ModelGeneric4
