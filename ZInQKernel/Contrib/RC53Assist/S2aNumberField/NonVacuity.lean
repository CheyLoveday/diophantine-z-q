import ZInQKernel.Contrib.RC53Assist.S2aNumberField.S2a
import ZInQKernel.Contrib.RC53Assist.GroupDifferentials.S2a
import ZInQKernel.Contrib.RC53Assist.GroupDifferentials.NonVacuity
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Non-vacuity and consistency of S2a over number fields

* The headline theorem `abVar_projectiveWeierstrassModel_numberField` applies to number fields
  other than `ℚ`, for example the cyclotomic field `ℚ(ζ₃)`.
* The group-scheme part (trivial differential sheaf, relative dimension one, degree-one
  identity place) applies to an actual object over every field of characteristic zero: the
  multiplicative group `Spec K[T, T⁻¹]`.
* The projective-model part (properness, valuation local rings, `K`-linearity of the
  function-field identification, the discrete valuation ring at `O`) applies to an actual
  nonsingular curve, `y² = x³ - x`, over every field of characteristic zero.
* Over `ℚ`, the projective structure morphism, the point `O`, the identity point and the
  function-field identification are definitionally those of the rational development, so the
  new theorem specializes to the existing rational statement
  `GroupDifferentials.abVar_projectiveWeierstrassModel_unconditional`.

No construction of a one-dimensional abelian variety as a group scheme is available in the
library, so the full hypotheses of the headline theorem are not instantiated by a concrete
object here; its conclusion is checked against the rational statement instead.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.S2aNumberField

open AlgebraicGeometry CategoryTheory LaurentPolynomial Polynomial
open ZInQ.Contrib.RC53Assist.AbelianCurve (functionFieldAlgebra abelian_scheme_integral)

section MultiplicativeGroup

variable (K : Type) [Field K]

/-- THEOREM (proved). Laurent polynomials over a field form a smooth algebra: a localization of
the smooth polynomial algebra away from the variable. Locator: Mathlib's
`Algebra.Smooth.of_isLocalization_Away` and `Algebra.Smooth.comp`; the rational version
`GroupDifferentials.laurentPolynomial_smooth`. -/
theorem laurent_smooth : Algebra.Smooth K K[T;T⁻¹] := by
  have : Algebra.Smooth K K[X] := ⟨inferInstance, inferInstance⟩
  have : IsScalarTower K K[X] K[T;T⁻¹] := IsScalarTower.of_algebraMap_eq fun c => by
    rw [LaurentPolynomial.algebraMap_eq_toLaurent, ← Polynomial.C_eq_algebraMap,
      Polynomial.toLaurent_C]
    rfl
  have : Algebra.Smooth K[X] K[T;T⁻¹] := Algebra.Smooth.of_isLocalization_Away (X : K[X])
  exact Algebra.Smooth.comp K K[X] K[T;T⁻¹]

/-- THEOREM (proved). Laurent polynomials over a field of characteristic zero do not form a
field: `T - 1` is nonzero (its value at `2` is `1`) and is killed by evaluation at `1`.
Locator: Mathlib's `LaurentPolynomial.eval₂`. -/
theorem laurent_not_isField [CharZero K] : ¬ IsField K[T;T⁻¹] := by
  intro h
  let φ : K[T;T⁻¹] →+* K := LaurentPolynomial.eval₂ (RingHom.id K) 1
  have hne : (T 1 - 1 : K[T;T⁻¹]) ≠ 0 := by
    intro h0
    have h2 := congrArg
      (LaurentPolynomial.eval₂ (RingHom.id K) (Units.mk0 (2 : K) two_ne_zero)) h0
    simp at h2
    norm_num at h2
  obtain ⟨b, hb⟩ := h.mul_inv_cancel hne
  have h2 := congrArg φ hb
  simp [φ] at h2

/-- THEOREM (proved). Laurent polynomials over a field of characteristic zero have Krull
dimension one. Locator: Mathlib's `Polynomial.ringKrullDim_of_isNoetherianRing`,
`PrimeSpectrum.localization_comap_injective` and `Ring.KrullDimLE.isField_of_isDomain`. -/
theorem laurent_ringKrullDim [CharZero K] : ringKrullDim K[T;T⁻¹] = 1 := by
  apply le_antisymm
  · have h1 : ringKrullDim K[X] = 1 := by
      rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]; rfl
    rw [← h1]
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap K[X] K[T;T⁻¹]))
      (Monotone.strictMono_of_injective (fun p q h ↦ ?_)
        (PrimeSpectrum.localization_comap_injective _ (Submonoid.powers (X : K[X]))))
    exact Ideal.comap_mono h
  · by_contra h
    have h0 : ringKrullDim K[T;T⁻¹] ≤ 0 := Order.le_of_lt_succ (not_le.mp h)
    rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h0
    exact laurent_not_isField K Ring.KrullDimLE.isField_of_isDomain

/-- DEFINITION. The multiplicative group `𝔾_m = Spec K[T, T⁻¹]` over `Spec K`; its group-object
structure is Mathlib's `AlgebraicGeometry.instGrpObjSpecAsOverSpec`. -/
abbrev multiplicativeGroup : Over (Spec (.of K)) :=
  (Spec (CommRingCat.of K[T;T⁻¹])).asOver (Spec (CommRingCat.of K))

/-- INSTANCE (proved). `𝔾_m` is integral. Locator: Mathlib's `IsDomain` instance for Laurent
polynomials over a domain. -/
instance multiplicativeGroup_isIntegral : IsIntegral (multiplicativeGroup K).left := by
  change IsIntegral (Spec (CommRingCat.of K[T;T⁻¹]))
  infer_instance

/-- INSTANCE (proved). `𝔾_m` is smooth over `Spec K`. Locator: `laurent_smooth`. -/
instance multiplicativeGroup_smooth : Smooth (multiplicativeGroup K).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap K K[T;T⁻¹])))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr (laurent_smooth K)

/-- THEOREM (proved). `𝔾_m` over a field of characteristic zero is one-dimensional.
Locator: `laurent_ringKrullDim`; Mathlib, `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`. -/
theorem multiplicativeGroup_dim [CharZero K] :
    topologicalKrullDim (multiplicativeGroup K).left = 1 :=
  (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim K[T;T⁻¹]).trans (laurent_ringKrullDim K)

/-- THEOREM (proved, non-vacuity). Over every field of characteristic zero the group-scheme
part of S2a applies to `𝔾_m`: its differential sheaf is trivial, it is smooth of relative
dimension one, and its identity gives a place of degree one.
Locator: `differentialSheaf_trivial`, `smooth_relativeDimension_one`,
`smoothIdentityPlace_degree`. -/
theorem multiplicativeGroup_groupPart [CharZero K] :
    Nonempty (ZInQ.Contrib.RC53Assist.AbelianCurve.differentialSheaf
        (multiplicativeGroup K).hom ≅
      SheafOfModules.unit (multiplicativeGroup K).left.ringCatSheaf) ∧
    SmoothOfRelativeDimension 1 (multiplicativeGroup K).hom ∧
    (letI := functionFieldAlgebra (multiplicativeGroup K).hom;
      (smoothIdentityPlace (multiplicativeGroup K) (multiplicativeGroup_dim K)).degree = 1) :=
  ⟨differentialSheaf_trivial _ (multiplicativeGroup_dim K),
    smooth_relativeDimension_one _ (multiplicativeGroup_dim K),
    smoothIdentityPlace_degree _ (multiplicativeGroup_dim K)⟩

end MultiplicativeGroup

section Curve

variable (K : Type) [Field K]

/-- DEFINITION. The Weierstrass curve `y² = x³ - x` over `K`. -/
def curveYXX : WeierstrassCurve K := ⟨0, 0, 0, -1, 0⟩

/-- THEOREM (proved). The discriminant of `y² = x³ - x` is `64`.
Locator: Mathlib's `WeierstrassCurve.Δ` and the `b`-invariants. -/
theorem curveYXX_Δ : (curveYXX K).Δ = 64 := by
  simp only [curveYXX, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

/-- INSTANCE (proved). In characteristic zero `y² = x³ - x` is nonsingular. -/
instance curveYXX_isElliptic [CharZero K] : (curveYXX K).IsElliptic :=
  ⟨by rw [curveYXX_Δ]; exact isUnit_iff_ne_zero.mpr (by norm_num)⟩

/-- THEOREM (proved, non-vacuity). The projective-model part of S2a applies to `y² = x³ - x`
over every field of characteristic zero: the model is proper over `K`, every local ring is a
valuation ring, the local ring at `O` is a discrete valuation ring, and the function-field
identification is `K`-linear. Locator: `projectiveStructure_proper`,
`projective_valuation_stalk`, `isDiscreteValuationRing_stalk_pointO`,
`projFunctionFieldEquiv_algebraMap`. -/
theorem curveYXX_projectivePart [CharZero K] :
    IsProper (projectiveStructure (curveYXX K)) ∧
    (∀ P : Proj (curveYXX K).toProjective.grading,
      ValuationRing ((Proj (curveYXX K).toProjective.grading).presheaf.stalk P)) ∧
    IsDiscreteValuationRing
      ((Proj (curveYXX K).toProjective.grading).presheaf.stalk (pointO (curveYXX K))) ∧
    (letI := functionFieldAlgebra (projectiveStructure (curveYXX K));
      ∀ c : K, projFunctionFieldEquiv (curveYXX K)
        (algebraMap K (Proj (curveYXX K).toProjective.grading).functionField c) =
          algebraMap K (curveYXX K).toAffine.FunctionField c) :=
  ⟨projectiveStructure_proper _, projective_valuation_stalk _,
    isDiscreteValuationRing_stalk_pointO _, projFunctionFieldEquiv_algebraMap _⟩

end Curve

/-- THEOREM (proved, non-vacuity). The cyclotomic field `ℚ(ζ₃)` is a number field, so the
headline theorem and both component theorems apply over it. -/
theorem cyclotomic_instances :
    NumberField (CyclotomicField 3 ℚ) ∧
      Nonempty (ZInQ.Contrib.RC53Assist.AbelianCurve.differentialSheaf
          (multiplicativeGroup (CyclotomicField 3 ℚ)).hom ≅
        SheafOfModules.unit (multiplicativeGroup (CyclotomicField 3 ℚ)).left.ringCatSheaf) ∧
      IsProper (projectiveStructure (curveYXX (CyclotomicField 3 ℚ))) :=
  ⟨inferInstance, (multiplicativeGroup_groupPart (CyclotomicField 3 ℚ)).1,
    (curveYXX_projectivePart (CyclotomicField 3 ℚ)).1⟩

/-- THEOREM (proved, non-vacuity). The headline theorem specialized to `ℚ(ζ₃)`. -/
theorem abVar_projectiveWeierstrassModel_cyclotomic
    (A : PkgI3.AbVar (CyclotomicField 3 ℚ)) (hdim : A.dim = 1) :
    letI := abelian_scheme_integral A.X
    letI := functionFieldAlgebra A.X.hom
    ∃ E : WeierstrassCurve (CyclotomicField 3 ℚ), E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[CyclotomicField 3 ℚ] A.X.left.functionField)
        (i : A.X.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = A.X.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint A.X) = pointO E :=
  abVar_projectiveWeierstrassModel_numberField _ A hdim

/-- THEOREM (proved, consistency). Over `ℚ` the structure morphism of the projective model is
the rational one. Locator: `AbelianCurve.projectiveStructure`. -/
theorem projectiveStructure_rat (E : WeierstrassCurve ℚ) :
    projectiveStructure E = ZInQ.Contrib.RC53Assist.AbelianCurve.projectiveStructure E :=
  rfl

/-- THEOREM (proved, consistency). Over `ℚ` the point `O` is the rational one.
Locator: `IsogenyScheme.pointO`. -/
theorem pointO_rat (E : WeierstrassCurve ℚ) :
    pointO E = ZInQ.Contrib.RC53Assist.IsogenyScheme.pointO E :=
  rfl

/-- THEOREM (proved, consistency). Over `ℚ` the identity point is the rational one.
Locator: `AbelianCurve.identityPoint`. -/
theorem identityPoint_rat (G : Over (Spec (.of ℚ))) [GrpObj G] :
    identityPoint G = ZInQ.Contrib.RC53Assist.AbelianCurve.identityPoint G :=
  rfl

/-- THEOREM (proved, consistency). Over `ℚ` the function-field identification of the
projective model is the rational one. Locator: `IsogenyScheme.projFunctionFieldEquiv`. -/
theorem projFunctionFieldEquiv_rat (E : WeierstrassCurve ℚ) :
    projFunctionFieldEquiv E = ZInQ.Contrib.RC53Assist.IsogenyScheme.projFunctionFieldEquiv E :=
  rfl

/-- THEOREM (proved, consistency). Over `ℚ` the new theorem gives the existing rational
statement `GroupDifferentials.abVar_projectiveWeierstrassModel_unconditional`, with the
rational definitions of the structure morphism, the point `O`, the identity point and the
function-field identification. -/
theorem abVar_projectiveWeierstrassModel_rat (A : PkgI3.AbVar ℚ) (hdim : A.dim = 1) :
    letI := abelian_scheme_integral A.X
    letI := functionFieldAlgebra A.X.hom
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[ℚ] A.X.left.functionField)
        (i : A.X.left ≅ Proj E.toProjective.grading),
        i.hom ≫ ZInQ.Contrib.RC53Assist.AbelianCurve.projectiveStructure E = A.X.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp
            (ZInQ.Contrib.RC53Assist.IsogenyScheme.projFunctionFieldEquiv E).toRingHom ∧
        i.hom (ZInQ.Contrib.RC53Assist.AbelianCurve.identityPoint A.X) =
          ZInQ.Contrib.RC53Assist.IsogenyScheme.pointO E :=
  abVar_projectiveWeierstrassModel_numberField ℚ A hdim

end ZInQ.Contrib.RC53Assist.S2aNumberField
