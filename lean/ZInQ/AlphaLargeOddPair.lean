module

public import ZInQ.AlphaParity

/-!
# Large odd consecutive alpha pair

Source: `Exponentiation.thy`, lines 1349–1388 (step `s1` of `alpha_equiv_nec`).
For `3 < B` and every natural `a` there is a positive natural index `k` such that
`alphaZ B k` is odd, exceeds `2 * a`, is strictly below `alphaZ B (k + 1)`, and the
consecutive pair satisfies the Cassini identity in the literal source order
`u ^ 2 - B * u * t + t ^ 2 = 1`.

The proof uses only the supplied parity lemma (`alphaZ_mod_two_eq_one_or_succ`),
core growth (`alphaZ_succ_strict`, `alphaZ_ge_index`) and Cassini (`alphaZ_cassini`).
This is an internal helper only; it does not establish the full alpha relation.
-/

public section

namespace ZInQ.AlphaPower

/-- Source E1349–1388: a large odd consecutive pair of alpha values with the Cassini
identity. The index is `2 * a + 1` or `2 * a + 2`, whichever has an odd alpha value. -/
theorem alphaZ_large_odd_pair (B a : Nat) (hB : 3 < B) :
    ∃ k : Nat, 0 < k ∧ Odd (alphaZ B k) ∧
      2 * (a : Int) < alphaZ B k ∧
      alphaZ B k < alphaZ B (k + 1) ∧
      (alphaZ B k) ^ 2 - (B : Int) * alphaZ B k * alphaZ B (k + 1) +
        (alphaZ B (k + 1)) ^ 2 = 1 := by
  have hB2 : 2 ≤ B := by omega
  -- Every index above `2 * a` carrying an odd alpha value satisfies all conjuncts.
  have key : ∀ k : Nat, 2 * a < k → alphaZ B k % 2 = 1 →
      0 < k ∧ Odd (alphaZ B k) ∧
        2 * (a : Int) < alphaZ B k ∧
        alphaZ B k < alphaZ B (k + 1) ∧
        (alphaZ B k) ^ 2 - (B : Int) * alphaZ B k * alphaZ B (k + 1) +
          (alphaZ B (k + 1)) ^ 2 = 1 := by
    intro k hk hodd
    refine ⟨by omega, Int.odd_iff.mpr hodd, ?_, alphaZ_succ_strict B k hB2, ?_⟩
    · have h1 : (k : Int) ≤ alphaZ B k := alphaZ_ge_index B k hB2
      have h2 : 2 * (a : Int) < (k : Int) := by exact_mod_cast hk
      linarith
    · have h := alphaZ_cassini B k
      linear_combination h
  -- Source `oneodd` at `j = 2 * a + 1` (needs `2 < B`, implied by `3 < B`).
  rcases alphaZ_mod_two_eq_one_or_succ B (2 * a + 1) (by omega) with h | h
  · exact ⟨2 * a + 1, key (2 * a + 1) (by omega) h⟩
  · exact ⟨2 * a + 1 + 1, key (2 * a + 1 + 1) (by omega) h⟩

end ZInQ.AlphaPower
