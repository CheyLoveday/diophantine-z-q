module

public import Mathlib.Data.Nat.ChineseRemainder

/-!
# Builder.alpha witness `w`

Constructs the natural number `w` demanded by the `Builder.alpha` clauses
`2 < w`, `w ≡ 2 [MOD u]` and `w ≡ B [MOD v]`, for any positive coprime moduli
`u` and `v` (modulus `1` is allowed; no assumption `1 < u` or `1 < v` is made).

Route: let `z` be the Chinese-remainder value `Nat.chineseRemainder hcop 2 B`
and take `w = z + 3 * (u * v)`.  Since `1 ≤ u * v` we get `3 ≤ w`, and adding a
multiple of each modulus preserves both residues.
-/

public section

namespace ZInQ.AlphaPower

/-- Adding a multiple of the modulus does not change the residue. -/
private theorem add_mul_modEq_self (z m k : Nat) : Nat.ModEq m (z + m * k) z :=
  Nat.add_mul_mod_self_left z m k

theorem exists_gt_two_modEq_pair (B u v : Nat)
    (hu : 0 < u) (hv : 0 < v) (hcop : Nat.Coprime u v) :
    ∃ w : Nat, 2 < w ∧ Nat.ModEq u w 2 ∧ Nat.ModEq v w B := by
  obtain ⟨z, hz2, hzB⟩ := Nat.chineseRemainder hcop 2 B
  have huv : 0 < u * v := Nat.mul_pos hu hv
  refine ⟨z + 3 * (u * v), ?_, ?_, ?_⟩
  · omega
  · have h : 3 * (u * v) = u * (3 * v) := Nat.mul_left_comm 3 u v
    rw [h]
    exact (add_mul_modEq_self z u (3 * v)).trans hz2
  · have h : 3 * (u * v) = v * (3 * u) := by
      rw [Nat.mul_comm u v]
      exact Nat.mul_left_comm 3 v u
    rw [h]
    exact (add_mul_modEq_self z v (3 * u)).trans hzB

end ZInQ.AlphaPower

