/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std

/-!
# Exact bounded precision arithmetic

Natural-number arithmetic for Section 2 of
`outputs/z-in-q-exact-value-bridge-audit.txt` and the `Capped` evaluator in
`outputs/variable-shift-precision.py`. The cap stores every value above `L`
as `L + 1`. These results concern exact natural arithmetic only.
-/

public section

namespace ZInQ.PrecisionArithmetic

/-- A strict natural threshold is an inclusive quotient threshold. -/
theorem mul_lt_iff_le_div_pred (a x D : Nat) (ha : 0 < a) (hD : 0 < D) :
    a * x < D ↔ x ≤ (D - 1) / a := by
  rw [Nat.le_div_iff_mul_le ha, Nat.mul_comm x a]
  omega

/-- The integer comparison used for `4 * epsilon < 4 ^ (-B)`. -/
theorem four_mul_pow_lt_iff (U D B : Nat) (hU : 0 < U) (hD : 0 < D) :
    4 * U * 4 ^ B < D ↔ 4 ^ B ≤ (D - 1) / (4 * U) := by
  apply mul_lt_iff_le_div_pred
  · omega
  · exact hD

/-- Exact representation of a natural number at the finite cap `L`. -/
@[expose] def saturate (L x : Nat) : Nat := min x (L + 1)

theorem saturate_eq_self (L x : Nat) (h : x ≤ L + 1) :
    saturate L x = x := Nat.min_eq_left h

theorem saturate_eq_cap (L x : Nat) (h : L + 1 ≤ x) :
    saturate L x = L + 1 := Nat.min_eq_right h

theorem saturate_le_cap (L x : Nat) : saturate L x ≤ L + 1 :=
  Nat.min_le_right _ _

theorem saturate_le_self (L x : Nat) : saturate L x ≤ x :=
  Nat.min_le_left _ _

@[simp] theorem saturate_zero (L : Nat) : saturate L 0 = 0 := by
  exact saturate_eq_self L 0 (Nat.zero_le _)

@[simp] theorem saturate_one (L : Nat) : saturate L 1 = 1 := by
  apply saturate_eq_self
  omega

@[simp] theorem saturate_saturate (L x : Nat) :
    saturate L (saturate L x) = saturate L x :=
  saturate_eq_self L _ (saturate_le_cap L x)

/-- Testing at the cap gives exactly the original inclusive comparison. -/
theorem saturate_le_iff (L x : Nat) : saturate L x ≤ L ↔ x ≤ L := by
  unfold saturate
  omega

/-- Every comparison with a threshold at most `L` is preserved. -/
theorem saturate_le_iff_of_le (L x k : Nat) (hk : k ≤ L) :
    saturate L x ≤ k ↔ x ≤ k := by
  unfold saturate
  omega

theorem le_saturate_iff_of_le (L x k : Nat) (hk : k ≤ L + 1) :
    k ≤ saturate L x ↔ k ≤ x := by
  unfold saturate
  omega

theorem saturate_lt_iff_of_le (L x k : Nat) (hk : k ≤ L + 1) :
    saturate L x < k ↔ x < k := by
  unfold saturate
  omega

theorem saturate_add (L x y : Nat) :
    saturate L (saturate L x + saturate L y) = saturate L (x + y) := by
  unfold saturate
  omega

theorem saturate_max (L x y : Nat) :
    saturate L (max (saturate L x) (saturate L y)) = saturate L (max x y) := by
  unfold saturate
  omega

private theorem saturate_mul_left (L x y : Nat) :
    saturate L (saturate L x * y) = saturate L (x * y) := by
  by_cases hx : x ≤ L + 1
  · rw [saturate_eq_self L x hx]
  · by_cases hy : y = 0
    · subst y
      simp only [Nat.mul_zero]
    · have hx' : L + 1 ≤ x := by omega
      have hy' : 1 ≤ y := by omega
      have hxy : L + 1 ≤ x * y := by
        have h := Nat.mul_le_mul_left x hy'
        omega
      have hcap : L + 1 ≤ (L + 1) * y := by
        have h := Nat.mul_le_mul_left (L + 1) hy'
        omega
      rw [saturate_eq_cap L x hx', saturate_eq_cap L _ hcap,
        saturate_eq_cap L _ hxy]

theorem saturate_mul (L x y : Nat) :
    saturate L (saturate L x * saturate L y) = saturate L (x * y) := by
  rw [saturate_mul_left, Nat.mul_comm x, saturate_mul_left, Nat.mul_comm y]

/-- Saturating the base preserves every fixed natural power. -/
theorem saturate_pow (L x n : Nat) :
    saturate L (saturate L x ^ n) = saturate L (x ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.pow_succ, Nat.pow_succ]
    calc
      saturate L (saturate L x ^ n * saturate L x) =
          saturate L (saturate L (saturate L x ^ n) * saturate L x) :=
        (saturate_mul_left L _ _).symm
      _ = saturate L (saturate L (x ^ n) * saturate L x) := by rw [ih]
      _ = saturate L (x ^ n * x) := saturate_mul L _ _

private theorem exponent_lt_pow (x n : Nat) (hx : 2 ≤ x) : n < x ^ n := by
  induction n with
  | zero => simp only [Nat.pow_zero]; omega
  | succ n ih =>
    rw [Nat.pow_succ]
    have h := Nat.mul_le_mul_left (x ^ n) hx
    omega

/-- Saturating the exponent is valid at a positive cap, including bases 0 and 1. -/
theorem saturate_pow_saturate_exponent (L x n : Nat) (hL : 1 ≤ L) :
    saturate L (x ^ saturate L n) = saturate L (x ^ n) := by
  by_cases hn : n ≤ L + 1
  · rw [saturate_eq_self L n hn]
  · have hn' : L + 1 ≤ n := by omega
    rw [saturate_eq_cap L n hn']
    by_cases hx0 : x = 0
    · subst x
      have hn0 : 0 < n := by omega
      have hcap0 : 0 < L + 1 :=
        Nat.lt_trans Nat.zero_lt_one (Nat.lt_succ_of_le hL)
      simp only [Nat.zero_pow hn0, Nat.zero_pow hcap0]
    · by_cases hx1 : x = 1
      · subst x
        simp only [Nat.one_pow]
      · have hx : 2 ≤ x := by omega
        have hpow := exponent_lt_pow x n hx
        have hcap := exponent_lt_pow x (L + 1) hx
        have hpow_le : L + 1 ≤ x ^ n := by omega
        have hcap_le : L + 1 ≤ x ^ (L + 1) := by omega
        rw [saturate_eq_cap L (x ^ (L + 1)) hcap_le,
          saturate_eq_cap L (x ^ n) hpow_le]

/-- Both inputs to a power may be saturated when the cap is positive. -/
theorem saturate_pow_saturate (L x n : Nat) (hL : 1 ≤ L) :
    saturate L (saturate L x ^ saturate L n) = saturate L (x ^ n) := by
  rw [saturate_pow, saturate_pow_saturate_exponent L x n hL]

end ZInQ.PrecisionArithmetic
