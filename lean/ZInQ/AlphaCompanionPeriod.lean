module

public import ZInQ.AlphaAddition

/-!
# First sign-changing period of the alpha recurrence

`alphaZ B (m + 1) - alphaZ B (m - 1)` divides `alphaZ B (n + 2 * m) + alphaZ B n`
(AFP `361` with `l = 1`, written as divisibility; `m - 1` is natural subtraction,
so for `m = 0` the modulus is `alphaZ B 1 - alphaZ B 0 = 1`).

This is an internal helper for the later reflected-index argument. It does not
establish the full reflected theorem or the correctness of the alpha encoding.
-/

public section

namespace ZInQ.AlphaPower

/-- Exact companion identity for a positive offset `m = k + 1`:
`alphaZ (n + 2m) + alphaZ n = (alphaZ (m + 1) - alphaZ (m - 1)) * alphaZ (n + m)`. -/
private theorem alphaZ_add_two_mul_succ_add_eq (B k n : Nat) :
    alphaZ B (n + 2 * (k + 1)) + alphaZ B n =
      (alphaZ B (k + 2) - alphaZ B k) * alphaZ B (n + (k + 1)) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      have h := alphaZ_add_succ B (k + 1) k
      have e1 : alphaZ B (0 + 2 * (k + 1)) = alphaZ B (k + 1 + k + 1) :=
        congrArg (alphaZ B) (by omega)
      have e2 : alphaZ B (0 + (k + 1)) = alphaZ B (k + 1) :=
        congrArg (alphaZ B) (by omega)
      have e3 : alphaZ B (k + 1 + 1) = alphaZ B (k + 2) := rfl
      rw [e1, e2, h, e3, alphaZ_zero]
      ring
  | one =>
      have h := alphaZ_add_succ B (k + 1) (k + 1)
      have e1 : alphaZ B (1 + 2 * (k + 1)) = alphaZ B (k + 1 + (k + 1) + 1) :=
        congrArg (alphaZ B) (by omega)
      have e2 : alphaZ B (1 + (k + 1)) = alphaZ B (k + 2) :=
        congrArg (alphaZ B) (by omega)
      have e3 : alphaZ B (k + 1 + 1) = alphaZ B (k + 2) := rfl
      have h2 := alphaZ_add_two B k
      have hc := alphaZ_cassini B k
      rw [e1, e2, h, e3, alphaZ_one]
      linear_combination (alphaZ B k) * h2 - hc
  | more n ih0 ih1 =>
      have e1 : alphaZ B (n + 2 + 2 * (k + 1)) =
          (B : Int) * alphaZ B (n + 1 + 2 * (k + 1)) - alphaZ B (n + 2 * (k + 1)) := by
        rw [show n + 2 + 2 * (k + 1) = n + 2 * (k + 1) + 2 by omega,
          alphaZ_add_two B (n + 2 * (k + 1)),
          show n + 2 * (k + 1) + 1 = n + 1 + 2 * (k + 1) by omega]
      have e2 : alphaZ B (n + 2) = (B : Int) * alphaZ B (n + 1) - alphaZ B n :=
        alphaZ_add_two B n
      have e3 : alphaZ B (n + 2 + (k + 1)) =
          (B : Int) * alphaZ B (n + 1 + (k + 1)) - alphaZ B (n + (k + 1)) := by
        rw [show n + 2 + (k + 1) = n + (k + 1) + 2 by omega,
          alphaZ_add_two B (n + (k + 1)),
          show n + (k + 1) + 1 = n + 1 + (k + 1) by omega]
      rw [e1, e2, e3]
      linear_combination (B : Int) * ih1 - ih0

/-- First sign-changing period (AFP `361` with `l = 1`) as divisibility. -/
theorem companion_dvd_alphaZ_add_two_mul (B m n : Nat) (hB : 2 < B) :
    (alphaZ B (m + 1) - alphaZ B (m - 1)) ∣
      (alphaZ B (n + 2 * m) + alphaZ B n) := by
  cases m with
  | zero =>
      show alphaZ B 1 - alphaZ B 0 ∣ alphaZ B (n + 2 * 0) + alphaZ B n
      rw [alphaZ_one, alphaZ_zero, sub_zero]
      exact one_dvd _
  | succ k =>
      show alphaZ B (k + 2) - alphaZ B k ∣ alphaZ B (n + 2 * (k + 1)) + alphaZ B n
      exact ⟨alphaZ B (n + (k + 1)), alphaZ_add_two_mul_succ_add_eq B k n⟩

end ZInQ.AlphaPower

