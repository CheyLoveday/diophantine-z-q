/- Copyright (c) 2026. -/
module

public import ZInQ.AlphaCore

/-!
# Congruent parameters of the integer alpha recurrence

This is the literal parameter-congruence lemma from the pinned AFP
`Exponentiation.thy`, lines 714-743. No positivity assumption is required.
-/

public section

namespace ZInQ.AlphaPower

theorem alphaZ_emod_eq_of_mod_eq (q B1 B2 n : Nat) (h : B1 % q = B2 % q) :
    alphaZ B1 n % (q : Int) = alphaZ B2 n % (q : Int) := by
  have hB : (B1 : Int) % (q : Int) = (B2 : Int) % (q : Int) := by
    simpa only [Int.natCast_emod] using congrArg (fun a : Nat => (a : Int)) h
  have step (k : Nat)
      (hk : alphaZ B1 k % (q : Int) = alphaZ B2 k % (q : Int))
      (hk1 : alphaZ B1 (k + 1) % (q : Int) = alphaZ B2 (k + 1) % (q : Int)) :
      alphaZ B1 (k + 2) % (q : Int) = alphaZ B2 (k + 2) % (q : Int) := by
    rw [alphaZ_add_two, alphaZ_add_two]
    rw [Int.sub_emod, Int.mul_emod, hB, hk1, hk, ← Int.mul_emod, ← Int.sub_emod]
  have pair (k : Nat) :
      alphaZ B1 k % (q : Int) = alphaZ B2 k % (q : Int) ∧
      alphaZ B1 (k + 1) % (q : Int) = alphaZ B2 (k + 1) % (q : Int) := by
    induction k with
    | zero =>
      constructor
      · rw [alphaZ_zero, alphaZ_zero]
      · rw [alphaZ_one, alphaZ_one]
    | succ k ih => exact ⟨ih.2, step k ih.1 ih.2⟩
  exact (pair n).1

end ZInQ.AlphaPower
