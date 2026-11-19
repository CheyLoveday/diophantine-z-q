import ZInQKernel.Contrib.RC53Assist.G0Prints.Faltings
import ZInQKernel.Contrib.RC53Assist.AbelianCurveInputs.S2aConsequence

/-!
# The canonical differential reading at the rational cusp

The normalization `δψ(μ(f)) = f(z) dz` in Shimura's setting is expressed
using the actual Abel–Jacobi morphism, the actual universal relative
sheaf derivative, restriction to the genuine function field, and its
specified q-expansion embedding. Thus the differential isomorphism `μ`
cannot be replaced by an arbitrary isomorphism permuting eigenforms.

The Euler derivative `q d/dq` is proved to be a derivation of Laurent
series. It induces the differential reading by the universal property
of Kähler differentials. A resulting q-expansion is the coefficient
of `dq/q`. Since `dq/q = 2πi dz`, the normalization reads
`μ(f) ↦ f(q)/(2πi)`.

Locators: Shimura 1973, §1, p. 525, the definition of `μ`;
bibliography `shimura-factors`, TeX lines 11053–11057.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ZInQ.Contrib.RC53Assist.G0Prints

open AlgebraicGeometry CategoryTheory Module
open ZInQ.Contrib.RC53Assist.NewformPeriods
open ZInQ.Contrib.RC53Assist.AbelianCurve
open ZInQ.Contrib.RC53Assist.AbelianCurveInputs
open scoped TensorProduct

/-- **PROVED**, the Euler derivative does not enlarge support.
Locator: the coefficient definition of `q d/dq`, Shimura p. 525. -/
theorem eulerOp_support_subset (x : LaurentSeries ℚ) :
    (eulerOp x).support ⊆ x.support := by
  intro n hn
  exact right_ne_zero_of_mul hn

/-- **PROVED**, the Leibniz law of the actual Euler derivative on Laurent
series. Each coefficient is a finite antidiagonal sum, and `n = i + j`
gives the two derivative terms.
Locator: formal Laurent-series differentiation; Shimura p. 525. -/
theorem eulerOp_mul (x y : LaurentSeries ℚ) :
    eulerOp (x * y) = x * eulerOp y + eulerOp x * y := by
  classical
  ext n
  rw [eulerOp_coeff, HahnSeries.coeff_add, HahnSeries.coeff_mul,
    HahnSeries.coeff_mul_right' y.isPWO_support (eulerOp_support_subset y),
    HahnSeries.coeff_mul_left' x.isPWO_support (eulerOp_support_subset x),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  have heq := (Finset.mem_antidiagonal.mp hij).2.2
  rw [← heq, Int.cast_add, eulerOp_coeff, eulerOp_coeff]
  ring

/-- **DEFINITION WITH PROVED LEIBNIZ LAW**, the actual Euler derivation
on rational Laurent series.
Locator: `q d/dq`; the printed q-coordinate normalization, Shimura p. 525. -/
def eulerDerivation : Derivation ℚ (LaurentSeries ℚ) (LaurentSeries ℚ) where
  toFun := eulerOp
  map_add' x y := by
    ext n
    simp only [eulerOp_coeff, HahnSeries.coeff_add, mul_add]
  map_smul' r x := by
    ext n
    simp only [eulerOp_coeff, Algebra.smul_def, HahnSeries.algebraMap_apply',
      PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
      HahnSeries.coeff_smul, smul_eq_mul]
    ring
  map_one_eq_zero' := by
    ext n
    by_cases hn : n = 0 <;> simp [eulerOp_coeff, hn]
  leibniz' x y := by
    change eulerOp (x * y) = x * eulerOp y + y * eulerOp x
    rw [eulerOp_mul, mul_comm y]


/-- **DEFINITION**, a differential in the actual function field is read
through its specified q-expansion embedding by the universal property
of Kähler differentials. The value is the coefficient of `dq/q`.
Locator: Shimura p. 525, `δψ(μ(f)) = f(z) dz`. -/
def functionFieldEulerReading {K : Type} [Field K] [Algebra ℚ K]
    (κ : K →ₐ[ℚ] LaurentSeries ℚ) :
    KaehlerDifferential ℚ K →ₗ[ℚ] LaurentSeries ℚ := by
  letI : Algebra K (LaurentSeries ℚ) := κ.toRingHom.toAlgebra
  letI : IsScalarTower ℚ K (LaurentSeries ℚ) :=
    IsScalarTower.of_algebraMap_smul (fun r y => by
      change κ (algebraMap ℚ K r) * y = r • y
      rw [κ.commutes, HahnSeries.algebraMap_apply']
      simp only [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.single_zero_mul_eq_smul])
  exact (eulerDerivation.compAlgebraMap K).liftKaehlerDifferential.restrictScalars ℚ

/-- **PROVED**, the reading takes `dx` to the actual Euler derivative
of the q-expansion of `x`, not an independently supplied differential map.
Locator: universal derivation and `functionFieldEulerReading`. -/
theorem functionFieldEulerReading_D {K : Type} [Field K] [Algebra ℚ K]
    (κ : K →ₐ[ℚ] LaurentSeries ℚ) (x : K) :
    functionFieldEulerReading κ (KaehlerDifferential.D ℚ K x) = eulerOp (κ x) := by
  letI : Algebra K (LaurentSeries ℚ) := κ.toRingHom.toAlgebra
  letI : IsScalarTower ℚ K (LaurentSeries ℚ) :=
    IsScalarTower.of_algebraMap_smul (fun r y => by
      change κ (algebraMap ℚ K r) * y = r • y
      rw [κ.commutes, HahnSeries.algebraMap_apply']
      simp only [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.single_zero_mul_eq_smul])
  exact Derivation.liftKaehlerDifferential_comp_D (eulerDerivation.compAlgebraMap K) x

/-- **DEFINITION**, coefficient extension of rational Laurent series to
complex Laurent series, as a rational-linear map.
Locator: the complex q-expansion of a rational differential. -/
def complexLaurentLinear : LaurentSeries ℚ →ₗ[ℚ] LaurentSeries ℂ where
  toFun := toComplexLaurent
  map_add' x y := by
    ext n
    simp only [toComplexLaurent_coeff, HahnSeries.coeff_add, Rat.cast_add]
  map_smul' r x := by
    ext n
    simp only [toComplexLaurent_coeff, HahnSeries.coeff_smul, smul_eq_mul, Rat.cast_mul]
    rfl

/-- **DEFINITION**, the rational reading of a Jacobian differential at a
specified rational cusp. The curve morphism is the actual Abel–Jacobi map.
The successive maps are sheaf pullback, generic restriction, and the Euler
reading of the specified function-field embedding.
Locator: Shimura 1973, p. 525, `ψ` and `δψ`. -/
def jacobianEulerReadingQ (X : Over (Spec (.of ℚ))) [IsIntegral X.left]
    (J : PkgI3.AbVar ℚ) (aj : X ⟶ J.X)
    (κ : letI := functionFieldAlgebra X.hom; X.left.functionField →ₐ[ℚ] LaurentSeries ℚ) :
    letI := globalSectionsModule J.X.hom (differentialSheaf J.X.hom)
    Γ(differentialSheaf J.X.hom, ⊤) →ₗ[ℚ] LaurentSeries ℚ := by
  letI := functionFieldAlgebra X.hom
  letI := globalSectionsModule X.hom (differentialSheaf X.hom)
  letI := globalSectionsModule J.X.hom (differentialSheaf J.X.hom)
  letI := abelian_scheme_integral J.X
  exact functionFieldEulerReading κ ∘ₗ canonicalRationalRestriction X.hom ∘ₗ
    globalDifferentialPullback X.hom J.X.hom aj.left aj.w

/-- **DEFINITION**, the complex reading is the scalar extension of that
actual rational sheaf pullback and function-field differential reading.
Locator: Shimura 1973, p. 525, the differential normalization of `μ`. -/
def jacobianEulerReadingC (X : Over (Spec (.of ℚ))) [IsIntegral X.left]
    (J : PkgI3.AbVar ℚ) (aj : X ⟶ J.X)
    (κ : letI := functionFieldAlgebra X.hom; X.left.functionField →ₐ[ℚ] LaurentSeries ℚ) :
    letI := globalSectionsModule J.X.hom (differentialSheaf J.X.hom)
    (ℂ ⊗[ℚ] Γ(differentialSheaf J.X.hom, ⊤)) →ₗ[ℂ] LaurentSeries ℂ := by
  letI := globalSectionsModule J.X.hom (differentialSheaf J.X.hom)
  exact (complexLaurentLinear ∘ₗ jacobianEulerReadingQ X J aj κ).liftBaseChange ℂ

end ZInQ.Contrib.RC53Assist.G0Prints
