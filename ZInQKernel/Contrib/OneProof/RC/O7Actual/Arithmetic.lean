import ZInQKernel.Contrib.OneProof.RC.Eichler.ClassSet
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Coefficients
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-! Integral quadratic generators and the stabilizer calculation for (O.7). -/

noncomputable section

open scoped Quaternion NumberField
open NumberField IsDedekindDomain

namespace ZInQ.Manuscript.RC.O7Actual

open Eichler Visibility

/-- On-the-spot (c), tex 9119–9120: the integral basis generator
`(1 + √d)/2` has parameter `k = (d-1)/4` in `T² - T - k`. -/
theorem quadratic_parameter_le {d k : ℤ} (hd : d < 0) (h8 : d % 8 = 1)
    (hk : d = 4 * k + 1) : k ≤ -2 := by omega

/-- Tex 9119–9120: the norm-one elements in the integral quadratic basis
are exactly the two signs. This calculation uses the split condition at two. -/
theorem quadratic_norm_one {k : ℤ} (hk : k ≤ -2)
    (z : QuadraticAlgebra ℤ k 1) (hz : QuadraticAlgebra.norm z = 1) :
    z = 1 ∨ z = -1 := by
  rw [QuadraticAlgebra.norm_def] at hz
  have hid : (2 * z.re + z.im) ^ 2 + (-4 * k - 1) * z.im ^ 2 = 4 := by
    linear_combination 4 * hz
  have him : z.im = 0 := by
    by_contra hn
    have h₁ : (1 : ℤ) ≤ z.im ^ 2 := by
      have hh : 0 < z.im ^ 2 := sq_pos_of_ne_zero hn
      omega
    have h₂ : (7 : ℤ) ≤ -4 * k - 1 := by omega
    have h₃ := mul_le_mul h₂ h₁ (by omega : (0 : ℤ) ≤ 1) (by omega : 0 ≤ -4 * k - 1)
    nlinarith [sq_nonneg (2 * z.re + z.im)]
  rw [him] at hz
  have hre : z.re = 1 ∨ z.re = -1 := by
    have h : z.re ^ 2 = 1 := by simpa only [pow_two, mul_zero, sub_zero, add_zero] using hz
    exact (sq_eq_one_iff.mp h)
  rcases hre with h | h
  · left
    exact QuadraticAlgebra.ext h him
  · right
    exact QuadraticAlgebra.ext h him

/-- The order of a chosen ideal representative, with its actual group of units. -/
def classOrder {a b : ℚ} {R : Order a b} (ha : a < 0) (hb : b < 0) (z : ClassSet R) :
    Order a b := (Eichler.representative z).val.leftOrder ha hb

/-- If the quadratic integral basis has been identified with the ring of integers,
this is the integral generator condition in tex 9123–9134. -/
def HalfIntegral {a b : ℚ} (R : Order a b) (x : B a b) : Prop :=
  ∃ t : R.ring, 2 * (t : B a b) - 1 = x

/-- On-the-spot (c), tex 9123–9134: the square relation and the order
condition extend the image of the square root to the integral quadratic basis. -/
theorem exists_basisHom {a b : ℚ} (R : Order a b) {k : ℤ} {x : B a b}
    (hx : x * x = algebraMap ℚ (B a b) ((4 * k + 1 : ℤ) : ℚ))
    (h : HalfIntegral R x) :
    ∃ f : QuadraticAlgebra ℤ k 1 →ₐ[ℤ] R.ring,
      2 * (f QuadraticAlgebra.omega : B a b) - 1 = x := by
  obtain ⟨t, rfl⟩ := h
  have ht : t * t = k • 1 + (1 : ℤ) • t := by
    apply Subtype.ext
    change (t : B a b) * t = k • (1 : B a b) + (1 : ℤ) • (t : B a b)
    have hcast : algebraMap ℚ (B a b) ((4 * k + 1 : ℤ) : ℚ) =
        (4 * k + 1 : ℤ) • (1 : B a b) := by
      simp [Algebra.algebraMap_eq_smul_one, ← Int.cast_smul_eq_zsmul ℚ]
    have e2 : (2 : B a b) = (2 : ℚ) • (1 : B a b) := by
      rw [← Algebra.algebraMap_eq_smul_one]
      norm_num
    have hmul : (2 * (t : B a b) - 1) * (2 * (t : B a b) - 1) =
        (4 : ℚ) • ((t : B a b) * t) - (4 : ℚ) • (t : B a b) + 1 := by
      rw [e2]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, sub_mul, mul_sub, mul_one, smul_smul]
      module
    apply (smul_right_injective (B a b) (show (4 : ℚ) ≠ 0 by norm_num))
    calc
      _ = (((4 : ℚ) • ((t : B a b) * t) - (4 : ℚ) • (t : B a b) + 1) +
          (4 : ℚ) • (t : B a b)) - 1 := by module
      _ = _ := by rw [← hmul, hx, hcast]; module
  let f := QuadraticAlgebra.lift ⟨t, ht⟩
  exact ⟨f, by simp [f]⟩

/-- Tex 9123–9134: an integral quadratic basis embedding gives the
half-integrality condition for the image of the square root. -/
theorem halfIntegral_of_basisHom {a b : ℚ} {R : Order a b} {k : ℤ}
    (f : QuadraticAlgebra ℤ k 1 →ₐ[ℤ] R.ring) :
    HalfIntegral R (2 * (f QuadraticAlgebra.omega : B a b) - 1) :=
  ⟨f QuadraticAlgebra.omega, rfl⟩

/-- An element of a quaternion order is integral over the rational integers. -/
theorem order_isIntegral {a b : ℚ} (R : Order a b) (y : R.ring) :
    IsIntegral ℤ (y : B a b) := by
  let : Module.Finite ℤ R.ring := Module.Finite.of_basis R.basis
  exact (Algebra.IsIntegral.isIntegral (R := ℤ) y).map
    (R.ring.subtype.toIntAlgHom)

/-- Tex 9129–9132: optimality is automatic for the maximal quadratic order.
If the image of a field element is in the quaternion order, injectivity
and integrality force the element to be in the ring of integers. -/
theorem optimal_of_maps_integers {a b : ℚ} (R : Order a b)
    {F : Type*} [Field F] [NumberField F] (ι : F →ₐ[ℚ] B a b)
    (hι : ∀ y : 𝓞 F, ι (y : F) ∈ R.ring) (y : F) :
    ι y ∈ R.ring ↔ IsIntegral ℤ y := by
  refine ⟨fun hy => ?_, fun hy => hι ⟨y, hy⟩⟩
  exact (isIntegral_algHom_iff (ι.restrictScalars ℤ) ι.injective).mp
    (order_isIntegral R ⟨ι y, hy⟩)

/-- Tex 9325–9327: products of the root values of the fixed characters
and the local signs remain roots of unity of two-power order. -/
theorem twoPower_mul {O : Type*} [CommRing O] {x y : O}
    (hx : ∃ j : ℕ, x ^ (2 ^ j : ℕ) = 1) (hy : ∃ j : ℕ, y ^ (2 ^ j : ℕ) = 1) :
    ∃ j : ℕ, (x * y) ^ (2 ^ j : ℕ) = 1 := by
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hy
  refine ⟨i + j, ?_⟩
  rw [mul_pow, pow_add, pow_mul, hi, one_pow, one_mul, mul_comm (2 ^ i : ℕ),
    pow_mul, hj, one_pow]

/-- Tex 9325–9327: the phase is a unit as soon as it is a two-power root of unity. -/
theorem unit_of_twoPower {O : Type*} [CommRing O] {x : O}
    (hx : ∃ j : ℕ, x ^ (2 ^ j : ℕ) = 1) : IsUnit x := by
  obtain ⟨j, hj⟩ := hx
  exact isUnit_of_dvd_one (hj ▸ dvd_pow_self x (by positivity))

/-- Contraction at the actual place of the coefficient field over two. -/
theorem ring_two {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (hv : (2 : 𝓞 K) ∈ v.asIdeal) (M : ℕ) (z : ℤ) :
    (2 : LocalWeights.coefficientRing K v) ^ M ∣ (z : LocalWeights.coefficientRing K v) →
      (2 : ℤ) ^ M ∣ z :=
  (LocalWeights.coefficientRing_two K v hv M z).mp

end ZInQ.Manuscript.RC.O7Actual
