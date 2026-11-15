import Mathlib

/-!
# pb-sanity: the truncated logarithm identity in `ℚ[B][A]` (towards `LogAdditive`)

`F_M = L_M(A + B + AB) - L_M(A) - L_M(B)`, `L_M(Z) = Σ_{1 ≤ j ≤ M} (-1)^{j+1} Z^j / j`.
Claim 1: every monomial `A^i B^s` of `F_M` with `i + s ≤ M` has coefficient 0.
-/

noncomputable section

open Polynomial

namespace PBLogPoly

abbrev R := Polynomial ℚ
abbrev S := Polynomial R

/-- `κ j = (-1)^{j+1}/j`. -/
def κ (j : ℕ) : ℚ := (-1) ^ (j + 1) / j

/-- `L_M(Z) = Σ_{1 ≤ j ≤ M} κ_j Z^j`. -/
def LM (M : ℕ) (Z : S) : S := ∑ j ∈ Finset.Ico 1 (M + 1), C (C (κ j)) * Z ^ j

/-- `c = A(1 + B) + B`, i.e. `(1 + A)(1 + B) - 1`. -/
def cA : S := X * C (1 + X) + C X

/-- `F_M = L_M(c) - L_M(A) - L_M(B)`. -/
def FM (M : ℕ) : S := LM M cA - LM M X - LM M (C X)

theorem derivative_LM (M : ℕ) (Z : S) :
    derivative (LM M Z) = (∑ k ∈ Finset.range M, (-Z) ^ k) * derivative Z := by
  rw [LM, derivative_sum, Finset.sum_Ico_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [derivative_C_mul, derivative_pow]
  have hk : ((1 + k : ℕ) : S) * C (C (κ (1 + k))) = (-1) ^ k := by
    have : ((1 + k : ℕ) : ℚ) * κ (1 + k) = (-1) ^ k := by
      rw [κ]
      have h0 : ((1 + k : ℕ) : ℚ) ≠ 0 := by positivity
      field_simp
      ring
    have := congrArg (fun q : ℚ => (C (C q) : S)) this
    simpa [map_mul, map_pow, map_neg, map_one] using this
  rw [Nat.add_sub_cancel_left]
  calc C (C (κ (1 + k))) * (C ((1 + k : ℕ) : R) * Z ^ k * derivative Z)
      = (((1 + k : ℕ) : S) * C (C (κ (1 + k)))) * Z ^ k * derivative Z := by
        rw [show (C ((1 + k : ℕ) : R) : S) = ((1 + k : ℕ) : S) from map_natCast C _]
        ring
    _ = _ := by rw [hk]; ring

theorem geom_neg (M : ℕ) (z : S) :
    (1 + z) * ∑ k ∈ Finset.range M, (-z) ^ k = 1 - (-z) ^ M := by
  have := geom_sum_mul_neg (-z) M
  rw [mul_comm, ← this]
  ring

theorem key_identity (M : ℕ) :
    (1 + X) * derivative (FM M) = (-X) ^ M - (-cA) ^ M := by
  have hc : derivative cA = C (1 + X) := by
    simp [cA, derivative_mul]
  have h1 : (1 + X : S) * C (1 + X) = 1 + cA := by
    simp only [cA, map_add, map_one]
    ring
  rw [FM, derivative_sub, derivative_sub, derivative_LM, derivative_LM, derivative_LM, hc,
    derivative_X, derivative_C, mul_zero, sub_zero, mul_one, mul_sub]
  rw [show (1 + X : S) * ((∑ k ∈ Finset.range M, (-cA) ^ k) * C (1 + X)) =
    (1 + cA) * ∑ k ∈ Finset.range M, (-cA) ^ k by rw [← h1]; ring]
  rw [geom_neg, geom_neg]
  ring

/-- The coefficients of `c^k` in `A` are divisible by suitable powers of `B`. -/
theorem dvd_coeff_cA_pow (k : ℕ) : ∀ i, (X : R) ^ (k - i) ∣ (cA ^ k).coeff i := by
  induction k with
  | zero =>
    intro i
    rw [Nat.zero_sub, pow_zero]
    exact one_dvd _
  | succ k ih =>
    intro i
    rw [pow_succ, cA, mul_add, ← mul_assoc, coeff_add, coeff_mul_C, coeff_mul_C]
    refine dvd_add ?_ ?_
    · rcases i with _ | i
      · rw [coeff_mul_X_zero, zero_mul]
        exact dvd_zero _
      · rw [coeff_mul_X, show k + 1 - (i + 1) = k - i by omega]
        exact dvd_mul_of_dvd_left (ih i) _
    · have := ih i
      calc (X : R) ^ (k + 1 - i) ∣ (X : R) ^ (k - i) * X := by
            rw [← pow_succ]; exact pow_dvd_pow X (by omega)
        _ ∣ (cA ^ k).coeff i * X := mul_dvd_mul_right this _

theorem eval_zero_LM (M : ℕ) (Z : S) :
    eval 0 (LM M Z) = ∑ j ∈ Finset.Ico 1 (M + 1), C (κ j) * (eval 0 Z) ^ j := by
  simp [LM, eval_finsetSum]

theorem coeff_zero_FM (M : ℕ) : (FM M).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, FM, eval_sub, eval_sub, eval_zero_LM, eval_zero_LM, eval_zero_LM]
  have h1 : eval 0 cA = X := by simp [cA]
  rw [h1, eval_X, eval_C, sub_sub_cancel_left, neg_eq_zero]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [zero_pow (by omega), mul_zero]

theorem dvd_coeff_rhs (M i : ℕ) : (X : R) ^ (M - i) ∣ ((-X) ^ M - (-cA) ^ M : S).coeff i := by
  rcases Nat.lt_or_ge i M with h | h
  · rw [coeff_sub, _root_.neg_pow (X : S), _root_.neg_pow (cA : S),
      show ((-1 : S) ^ M) = C ((-1) ^ M) by simp, coeff_C_mul_X_pow, coeff_C_mul]
    split_ifs with h'
    · omega
    · rw [zero_sub]
      exact (dvd_neg).mpr (dvd_mul_of_dvd_right (dvd_coeff_cA_pow M i) _)
  · rw [show M - i = 0 by omega, pow_zero]
    exact one_dvd _

/-- **Claim 1 (divisibility form).** `B^{M+1-i}` divides the coefficient of `A^i` in `F_M`. -/
theorem dvd_coeff_FM (M : ℕ) : ∀ i, (X : R) ^ (M + 1 - i) ∣ (FM M).coeff i := by
  intro i
  induction i with
  | zero => rw [coeff_zero_FM]; exact dvd_zero _
  | succ i ih =>
    have hid := congrArg (fun P : S => P.coeff i) (key_identity M)
    rw [add_mul, one_mul, coeff_add, coeff_derivative] at hid
    have hX : (X : R) ^ (M - i) ∣ (X * derivative (FM M)).coeff i := by
      rcases i with _ | i
      · rw [coeff_X_mul_zero]; exact dvd_zero _
      · rw [coeff_X_mul, coeff_derivative]
        refine dvd_mul_of_dvd_left ((pow_dvd_pow X (by omega)).trans ih) _
    have h2 : (X : R) ^ (M - i) ∣ (FM M).coeff (i + 1) * ((i : R) + 1) := by
      have : (FM M).coeff (i + 1) * ((i : R) + 1) =
          ((-X) ^ M - (-cA) ^ M : S).coeff i - (X * derivative (FM M)).coeff i := by
        rw [← hid]; ring
      rw [this]
      exact dvd_sub (dvd_coeff_rhs M i) hX
    have hu : IsUnit ((i : R) + 1) := by
      have : ((i : R) + 1) = C ((i : ℚ) + 1) := by simp
      rw [this]
      exact (Polynomial.isUnit_C).mpr (IsUnit.mk0 _ (by positivity))
    rw [show M + 1 - (i + 1) = M - i by omega]
    exact (hu.dvd_mul_right).mp h2

/-- **Claim 1.** The coefficient of `A^i B^s` in `F_M` vanishes for `i + s ≤ M`. -/
theorem coeff_FM_eq_zero (M i s : ℕ) (h : i + s ≤ M) : ((FM M).coeff i).coeff s = 0 := by
  obtain ⟨g, hg⟩ := dvd_coeff_FM M i
  rw [hg, coeff_X_pow_mul']
  split_ifs with h'
  · omega
  · rfl

end PBLogPoly
