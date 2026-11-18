import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic

/-!
# Coefficients of `1 / ((1 − αT)(1 − βT))`

If `1 − aT + bT² = (1 − αT)(1 − βT)` over `ℂ` with `|α|, |β| ≤ r`, the coefficients of the inverse
power series `1 / (1 − aT + bT²)` (Mathlib's `invOfUnit`) are `∑_{i+j=k} αⁱ βʲ`, so they are bounded
by `(k + 1) rᵏ` (`norm_coeff_invOfUnit_le`). For a local factor `1 − a_p T + p T²` with
`a_p² ≤ 4p` one takes `α, β = (a_p ± i√(4p − a_p²))/2`, of absolute value `√p`
(`exists_roots_of_sq_le`).

Classification: PROVED.
-/

noncomputable section

open Polynomial

namespace ZInQ.Contrib.CloudB3RC53.Hasse

/-- The geometric series `∑ αⁿ Tⁿ` inverts `1 − αT`. PROVED. -/
theorem one_sub_mul_geom (α : ℂ) :
    (1 - PowerSeries.C α * PowerSeries.X) * PowerSeries.mk (fun n => α ^ n) = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul]
  rcases n with _ | n
  · simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      PowerSeries.coeff_one, ite_eq_right (Nat.succ_ne_zero n)]
    ring

/-- **The coefficient bound.** PROVED. -/
theorem norm_coeff_invOfUnit_le (a b : ℤ) (α β : ℂ) (hs : α + β = a) (hp : α * β = b) {r : ℝ}
    (hα : ‖α‖ ≤ r) (hβ : ‖β‖ ≤ r) (k : ℕ) :
    ‖((PowerSeries.coeff k (PowerSeries.invOfUnit
        ((1 - C a * X + C b * X ^ 2 : ℤ[X]) : PowerSeries ℤ) 1) : ℤ) : ℂ)‖ ≤ (k + 1) * r ^ k := by
  set P : PowerSeries ℤ := ((1 - C a * X + C b * X ^ 2 : ℤ[X]) : PowerSeries ℤ)
  set Q := PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.invOfUnit P 1)
  set G := PowerSeries.mk (fun n => α ^ n) * PowerSeries.mk (fun n => β ^ n)
  have hP0 : PowerSeries.constantCoeff P = 1 := by
    simp [P]
  have hPℂ : PowerSeries.map (Int.castRingHom ℂ) P =
      (1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X) := by
    simp only [P, Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_pow, map_add, map_sub, map_one, map_mul,
      PowerSeries.map_C, PowerSeries.map_X, map_pow, Int.coe_castRingHom]
    rw [← hs, ← hp]
    simp only [map_add, map_mul]
    ring
  have hQ : Q * PowerSeries.map (Int.castRingHom ℂ) P = 1 := by
    rw [← map_mul, mul_comm, PowerSeries.mul_invOfUnit P 1 (by rw [hP0]; rfl), map_one]
  have hG : G * PowerSeries.map (Int.castRingHom ℂ) P = 1 := by
    rw [hPℂ]
    calc G * ((1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X))
        = ((1 - PowerSeries.C α * PowerSeries.X) * PowerSeries.mk (fun n => α ^ n)) *
            ((1 - PowerSeries.C β * PowerSeries.X) * PowerSeries.mk (fun n => β ^ n)) := by
          simp only [G]; ring
      _ = 1 := by rw [one_sub_mul_geom, one_sub_mul_geom, one_mul]
  have hQG : Q = G := by
    calc Q = Q * (PowerSeries.map (Int.castRingHom ℂ) P * G) := by
          rw [mul_comm (PowerSeries.map _ P) G, hG, mul_one]
      _ = G := by rw [← mul_assoc, hQ, one_mul]
  have hc : ((PowerSeries.coeff k (PowerSeries.invOfUnit P 1) : ℤ) : ℂ) = PowerSeries.coeff k Q := by
    simp [Q]
  rw [hc, hQG, PowerSeries.coeff_mul]
  have hr : 0 ≤ r := (norm_nonneg α).trans hα
  calc ‖∑ x ∈ Finset.antidiagonal k, PowerSeries.coeff x.1 (PowerSeries.mk fun n => α ^ n) *
        PowerSeries.coeff x.2 (PowerSeries.mk fun n => β ^ n)‖
      ≤ ∑ x ∈ Finset.antidiagonal k, ‖PowerSeries.coeff x.1 (PowerSeries.mk fun n => α ^ n) *
        PowerSeries.coeff x.2 (PowerSeries.mk fun n => β ^ n)‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ Finset.antidiagonal k, r ^ k := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [Finset.mem_antidiagonal] at hx
        rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, norm_mul, norm_pow, norm_pow, ← hx, pow_add]
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hα _)
          (pow_le_pow_left₀ (norm_nonneg _) hβ _) (by positivity) (by positivity)
    _ = (k + 1) * r ^ k := by
        rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
        push_cast; ring

/-- **Roots of `1 − aT + bT²` of absolute value `√b` when `a² ≤ 4b`.** PROVED. -/
theorem exists_roots_of_sq_le (a b : ℤ) (h : (a : ℝ) ^ 2 ≤ 4 * b) :
    ∃ α β : ℂ, α + β = a ∧ α * β = b ∧ ‖α‖ ≤ √(b : ℝ) ∧ ‖β‖ ≤ √(b : ℝ) := by
  set δ : ℝ := 4 * b - (a : ℝ) ^ 2
  have hδ : 0 ≤ δ := by simp only [δ]; linarith
  refine ⟨⟨a / 2, √δ / 2⟩, ⟨a / 2, -(√δ / 2)⟩, ?_, ?_, ?_, ?_⟩
  · apply Complex.ext <;> simp
  · apply Complex.ext
    · simp only [Complex.mul_re, Complex.intCast_re]
      have := Real.sq_sqrt hδ
      nlinarith
    · simp only [Complex.mul_im, Complex.intCast_im]; ring
  all_goals
    rw [Complex.norm_def, Complex.normSq_mk]
    apply Real.sqrt_le_sqrt
    have := Real.sq_sqrt hδ
    simp only [δ] at this
    nlinarith

end ZInQ.Contrib.CloudB3RC53.Hasse
