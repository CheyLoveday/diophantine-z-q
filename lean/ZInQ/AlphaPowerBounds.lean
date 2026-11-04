/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import ZInQ.AlphaCore

/-!
Literal growth bounds from AFP `Exponentiation.thy`, using the integrated
integer recurrence. These helpers do not establish the power encoding.
-/

public section

namespace ZInQ.AlphaPower

/-- AFP `alpha_exponential_1`, with the natural base kept explicit. -/
theorem pow_le_alphaZ_succ (B n : Nat) (hB : 0 < B) :
    (B : Int) ^ n ≤ alphaZ (B + 1) (n + 1) := by
  have hB2 : 2 ≤ B + 1 := by omega
  induction n with
  | zero =>
      simp only [pow_zero, Nat.zero_add, alphaZ_one, le_refl]
  | succ n ih =>
      change (B : Int) ^ (n + 1) ≤ alphaZ (B + 1) (n + 2)
      have hg := (alphaZ_step (B + 1) hB2 n).2
      calc
        (B : Int) ^ (n + 1) = (B : Int) * (B : Int) ^ n := by
          rw [pow_succ, mul_comm]
        _ ≤ (B : Int) * alphaZ (B + 1) (n + 1) :=
          mul_le_mul_of_nonneg_left ih (Int.natCast_nonneg B)
        _ ≤ alphaZ (B + 1) (n + 2) := by
          rw [alphaZ_add_two]
          simp only [Nat.cast_add, Nat.cast_one]
          nlinarith only [hg]

/-- AFP `alpha_exponential_2`, retaining its strict base hypothesis. -/
theorem alphaZ_succ_le_pow (B n : Nat) (hB : 2 < B) :
    alphaZ B (n + 1) ≤ (B : Int) ^ n := by
  have hB2 : 2 ≤ B := by omega
  induction n with
  | zero =>
      simp only [Nat.zero_add, alphaZ_one, pow_zero, le_refl]
  | succ n ih =>
      change alphaZ B (n + 2) ≤ (B : Int) ^ (n + 1)
      have hn := (alphaZ_step B hB2 n).1
      calc
        alphaZ B (n + 2) =
            (B : Int) * alphaZ B (n + 1) - alphaZ B n :=
          alphaZ_add_two B n
        _ ≤ (B : Int) * alphaZ B (n + 1) := sub_le_self _ hn
        _ ≤ (B : Int) * (B : Int) ^ n :=
          mul_le_mul_of_nonneg_left ih (Int.natCast_nonneg B)
        _ = (B : Int) ^ (n + 1) := by rw [pow_succ, mul_comm]

end ZInQ.AlphaPower
