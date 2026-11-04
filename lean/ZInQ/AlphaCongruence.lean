/- Copyright (c) 2026. -/
module

public import ZInQ.AlphaCore
import Mathlib.Tactic.LinearCombination

/-!
# The alpha recurrence modulo its parameter minus two

For parameters at least two, this is the divisibility form of AFP
Exponentiation.thy, Equation 3.34 (congruence2). Integer subtraction also
gives a valid recurrence identity at parameters zero and one.
-/

public section

namespace ZInQ.AlphaPower

/-- The literal alpha recurrence agrees with its index modulo B - 2. -/
theorem sub_two_dvd_alphaZ_sub_index (B n : Nat) :
    ((B : Int) - 2) ∣ alphaZ B n - (n : Int) := by
  have consecutive : ∀ k : Nat,
      ((B : Int) - 2) ∣ alphaZ B k - (k : Int) ∧
      ((B : Int) - 2) ∣ alphaZ B (k + 1) - ((k + 1 : Nat) : Int) := by
    intro k
    induction k with
    | zero =>
        constructor
        · simp only [alphaZ_zero, Nat.cast_zero, sub_self, dvd_zero]
        · simp only [Nat.zero_add, alphaZ_one, Nat.cast_one, sub_self, dvd_zero]
    | succ k ih =>
        refine ⟨ih.2, ?_⟩
        rcases ih.1 with ⟨u, hu⟩
        rcases ih.2 with ⟨v, hv⟩
        refine ⟨(B : Int) * v - u + ((k : Int) + 1), ?_⟩
        change alphaZ B (k + 2) - ((k + 2 : Nat) : Int) =
          ((B : Int) - 2) * ((B : Int) * v - u + ((k : Int) + 1))
        rw [alphaZ_add_two]
        push_cast at hu hv ⊢
        linear_combination (B : Int) * hv - hu
  exact (consecutive n).1

end ZInQ.AlphaPower
