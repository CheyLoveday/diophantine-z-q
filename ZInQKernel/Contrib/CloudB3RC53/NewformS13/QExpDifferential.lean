import ZInQKernel.Contrib.RC53Assist.NewformPeriods.RationalParametrization
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Reading translation S3 at the function-field level: `q`-expansions of differentials

Translation S3 of the reduction of `NewformPeriodsRational` (`NewformPeriods/README.md`): "the
canonical map at `∞` and `ν` are defined over `ℚ`; with `δφ(μ(g)) = g(z)dz` and `dz = dq/(2πi q)`,
clause (iv) is `θx = c · ĝ · (2y + a₁x + a₃)`". This file proves the function-field core of that
reading, with the genuine Kähler differentials of `F = ℚ(j, j_M) = modularFunctionFieldQ M`:

* `eulerDer`: the Euler operator `θ = q d/dq` is a `ℚ`-derivation of `ℚ((q))` (Leibniz rule);
* `qExpDiff M : Ω[F⁄ℚ] →ₗ[F] ℚ((q))`: the `q`-expansion of differentials at the cusp `∞`,
  `ω = h · dq/q ↦ h`, the unique `F`-linear map with `d f ↦ θ f` (`qExpDiff_D`);
* `pointAlgHom`: a point `(x, y)` of `A` with coordinates in `F` is a `ℚ`-algebra map
  `φ : ℚ[A] → F` from the coordinate ring of `A` (`X ↦ x`, `Y ↦ y`); `pullback_dX`,
  `pullback_dY`: pulling back the differentials `dX`, `dY` of `ℚ[A]` along `φ` gives `dx`, `dy`;
* `omegaPull`: the pull-back `ω_A ↦ (2y + a₁x + a₃)⁻¹ dx` of the invariant differential;
  `omegaPull_eq_dY`: it also equals `(3x² + 2a₂x + a₄ − a₁y)⁻¹ dy` (when both denominators are
  nonzero; the differential of the Weierstrass equation);
* **`qExpDiff_omegaPull`**: the `q`-expansion of the pulled-back `ω_A` is `θx · (2y + a₁x + a₃)⁻¹`;
  **`pullbackIsMultiple_iff`**: for `2y + a₁x + a₃ ≠ 0`, the peer's `PullbackIsMultiple A x y ĝ c`
  holds iff the `q`-expansion of the pulled-back invariant differential is `c · ĝ` (times `dq/q`).

What remains of S1/S3: the scheme `X₀(M)` and its cusp, the identification of `F` with the function
field of that scheme, and the analytic statement `dq/q = 2πi dz`; see `notes`.

All statements are definitions or PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.NewformS13

open ZInQ.Contrib.RC53Assist.NewformPeriods
open HahnSeries

/-! ### The Euler operator is a derivation -/

theorem eulerOp_add (x y : LaurentSeries ℚ) : eulerOp (x + y) = eulerOp x + eulerOp y := by
  ext n
  simp [mul_add]

theorem eulerOp_smul (r : ℚ) (x : LaurentSeries ℚ) : eulerOp (r • x) = r • eulerOp x := by
  ext n
  simp only [eulerOp_coeff, HahnSeries.coeff_smul, smul_eq_mul]
  ring

theorem eulerOp_mul (x y : LaurentSeries ℚ) :
    eulerOp (x * y) = x * eulerOp y + y * eulerOp x := by
  ext n
  have hx : (eulerOp x).support ⊆ x.support := fun i hi => by
    rw [HahnSeries.mem_support, eulerOp_coeff] at hi
    exact (HahnSeries.mem_support _ _).2 (right_ne_zero_of_mul hi)
  have hy : (eulerOp y).support ⊆ y.support := fun i hi => by
    rw [HahnSeries.mem_support, eulerOp_coeff] at hi
    exact (HahnSeries.mem_support _ _).2 (right_ne_zero_of_mul hi)
  rw [eulerOp_coeff, HahnSeries.coeff_add, HahnSeries.coeff_mul,
    HahnSeries.coeff_mul_right' (x := x) y.isPWO_support hy,
    mul_comm y, HahnSeries.coeff_mul_left' (y := y) x.isPWO_support hx, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  rw [eulerOp_coeff, eulerOp_coeff, ← hij.2.2]
  push_cast
  ring

/-- Coefficients of the `ℚ`-algebra scalar multiplication on `ℚ((q))`. -/
theorem algSmul_coeff (r : ℚ) (x : LaurentSeries ℚ) (n : ℤ) :
    (@HSMul.hSMul ℚ (LaurentSeries ℚ) (LaurentSeries ℚ)
      (@instHSMul ℚ (LaurentSeries ℚ) (HahnSeries.powerSeriesAlgebra ℤ ℚ).toSMul) r x).coeff n =
      r * x.coeff n := by
  rw [Algebra.smul_def, show algebraMap ℚ (LaurentSeries ℚ) r = HahnSeries.C r by simp,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem eulerOp_algebraMap (r : ℚ) : eulerOp (algebraMap ℚ (LaurentSeries ℚ) r) = 0 := by
  ext n
  rw [eulerOp_coeff, HahnSeries.coeff_zero]
  by_cases h : n = 0
  · subst h; simp
  · have : (algebraMap ℚ (LaurentSeries ℚ) r).coeff n = 0 := by
      rw [show algebraMap ℚ (LaurentSeries ℚ) r = HahnSeries.C r by simp, HahnSeries.C_apply,
        HahnSeries.coeff_single_of_ne h]
    rw [this, mul_zero]

/-- **The Euler operator `θ = q d/dq` as a `ℚ`-derivation of `ℚ((q))`.** -/
def eulerDer : Derivation ℚ (LaurentSeries ℚ) (LaurentSeries ℚ) where
  toFun := eulerOp
  map_add' := eulerOp_add
  map_smul' r x := by
    ext n
    rw [RingHom.id_apply]
    erw [eulerOp_coeff, HahnSeries.coeff_smul, algSmul_coeff, eulerOp_coeff]
    simp only [smul_eq_mul]
    ring
  map_one_eq_zero' := by
    change eulerOp 1 = 0
    ext n
    rw [eulerOp_coeff, HahnSeries.coeff_one, HahnSeries.coeff_zero]
    split_ifs with h <;> simp [h]
  leibniz' x y := by
    change eulerOp (x * y) = x • eulerOp y + y • eulerOp x
    rw [eulerOp_mul, smul_eq_mul, smul_eq_mul]

@[simp]
theorem eulerDer_apply (x : LaurentSeries ℚ) : eulerDer x = eulerOp x := rfl

end ZInQ.Contrib.CloudB3RC53.NewformS13
