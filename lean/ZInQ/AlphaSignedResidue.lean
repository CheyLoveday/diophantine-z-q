module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Order.Group.Unbundled.Int

/-!
# Signed-residue recovery helpers for the alpha power characterization

Source: `Exponentiation.thy`, proof of `alpha_equiv_suff`,
equation 3.64 (lines 1170-1184) and equations 3.65-3.67 (lines 1188-1214).

* `eq_of_small_signed_residue`: two nonnegative integers below half of `V` that are congruent
  up to sign modulo `V` are equal.
* `folded_index_recovery`: the folded index `j` of `n = 2*l*m ± j` is recovered from a
  small representative `c` of `n` modulo a divisor `u` of `m`.
-/

public section

namespace ZInQ.AlphaPower

theorem eq_of_small_signed_residue (A z V : Int)
    (hA : 0 ≤ A) (hz : 0 ≤ z) (hAV : 2*A < V) (hzV : 2*z < V)
    (hdiv : V ∣ A-z ∨ V ∣ A+z) : A = z := by
  rcases hdiv with h | h
  · -- `-V < A - z < V`, so the multiple `A - z` of `V` vanishes.
    have h0 : A - z = 0 := Int.eq_zero_of_abs_lt_dvd h (abs_lt.2 ⟨by omega, by omega⟩)
    omega
  · -- `0 ≤ A + z < V`, so the multiple `A + z` of `V` vanishes, forcing `A = z = 0`.
    have h0 : A + z = 0 := Int.eq_zero_of_abs_lt_dvd h (abs_lt.2 ⟨by omega, by omega⟩)
    omega

theorem folded_index_recovery (u m n c l j : Nat)
    (hum : u ∣ m) (hc : 2*c < u) (hj : 2*j < u)
    (hmod : c % u = n % u)
    (hf : n = 2*l*m+j ∨ (n = 2*l*m-j ∧ 0 < j ∧ j < 2*l*m)) : c = j := by
  -- `u` divides the fold length `2*l*m`; abstract it as `N`.
  have hN : u ∣ 2 * l * m := Nat.dvd_mul_left_of_dvd hum (2 * l)
  generalize 2 * l * m = N at hN hf
  -- Integer forms of the congruence `c ≡ n [MOD u]` and of `u ∣ N`.
  have hcn : (u : ℤ) ∣ (n : ℤ) - (c : ℤ) := Nat.modEq_iff_dvd.1 hmod
  have hNz : (u : ℤ) ∣ (N : ℤ) := Int.natCast_dvd_natCast.2 hN
  have key : (u : ℤ) ∣ (c : ℤ) - (j : ℤ) ∨ (u : ℤ) ∣ (c : ℤ) + (j : ℤ) := by
    rcases hf with h | ⟨h, -, hjN⟩
    · -- Direct branch `n = N + j`: `c - j = N - (n - c)`.
      left
      have e : (c : ℤ) - (j : ℤ) = (N : ℤ) - ((n : ℤ) - (c : ℤ)) := by omega
      rw [e]
      exact Int.dvd_sub hNz hcn
    · -- Reflected branch `n = N - j` with `j < N` (Nat subtraction): `c + j = N - (n - c)`.
      right
      have e : (c : ℤ) + (j : ℤ) = (N : ℤ) - ((n : ℤ) - (c : ℤ)) := by omega
      rw [e]
      exact Int.dvd_sub hNz hcn
  have hcj : (c : ℤ) = (j : ℤ) :=
    eq_of_small_signed_residue (c : ℤ) (j : ℤ) (u : ℤ) (by omega) (by omega) (by omega)
      (by omega) key
  exact_mod_cast hcj

end ZInQ.AlphaPower
