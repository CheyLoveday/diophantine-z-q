/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ZInQ.AlphaCore

/-!
# Addition and linear identities for the alpha recurrence

These internal arithmetic consequences use the literal integer recurrence for
all natural parameters. They do not establish the full alpha or power encoding.
-/

public section

namespace ZInQ.AlphaPower

/-- Addition identity for the integer alpha recurrence, including `B = 0` and `B = 1`. -/
theorem alphaZ_add_succ (B m n : Nat) :
    alphaZ B (m + n + 1) =
      alphaZ B (m + 1) * alphaZ B (n + 1) - alphaZ B m * alphaZ B n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simp only [Nat.add_zero, Nat.zero_add, alphaZ_zero, alphaZ_one,
        mul_one, mul_zero, sub_zero]
  | one =>
      change alphaZ B (m + 2) =
        alphaZ B (m + 1) * alphaZ B 2 - alphaZ B m * alphaZ B 1
      rw [alphaZ_add_two, alphaZ_add_two B 0, alphaZ_zero, alphaZ_one]
      ring
  | more n ih0 ih1 =>
      rw [show m + (n + 2) + 1 = (m + n + 1) + 2 by omega,
        alphaZ_add_two,
        show m + n + 1 + 1 = m + (n + 1) + 1 by omega,
        ih1, ih0,
        show n + 2 + 1 = (n + 1) + 2 by omega,
        alphaZ_add_two B (n + 1)]
      rw [alphaZ_add_two B n]
      ring

/-- At parameter two the integer alpha recurrence is the natural index. -/
theorem alphaZ_two_left (n : Nat) : alphaZ 2 n = (n : Int) := by
  induction n using Nat.twoStepInduction with
  | zero => exact alphaZ_zero 2
  | one => exact alphaZ_one 2
  | more n ih0 ih1 =>
      rw [alphaZ_add_two, ih1, ih0]
      push_cast
      ring

end ZInQ.AlphaPower
