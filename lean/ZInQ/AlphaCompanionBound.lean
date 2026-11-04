module

public import ZInQ.AlphaCore

/-!
# Companion bound for the alpha sequence (AFP Exponentiation, equation 3.63)

For `3 < B`, `0 < m` and `j ≤ m`, we have
`2 * alphaZ B j < alphaZ B (m + 1) - alphaZ B (m - 1)`.

The proof uses only the integrated `ZInQ.AlphaCore` results
(`alphaZ_add_two`, `alphaZ_step`, `alphaZ_succ_strict`); monotonicity is
derived locally (private) from `alphaZ_succ_strict`. No divisibility
result is used.
-/

public section

namespace ZInQ.AlphaPower

/-- Local monotonicity (additive form), from `alphaZ_succ_strict`. -/
private theorem alphaZ_le_add_local (B : Nat) (hB : 2 ≤ B) (j d : Nat) :
    alphaZ B j ≤ alphaZ B (j + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h := alphaZ_succ_strict B (j + d) hB
    have e : j + (d + 1) = j + d + 1 := (Nat.add_assoc j d 1).symm
    rw [e]
    linarith

/-- Local monotonicity, from `alphaZ_succ_strict`. -/
private theorem alphaZ_le_of_le_local (B : Nat) (hB : 2 ≤ B) {j m : Nat} (hjm : j ≤ m) :
    alphaZ B j ≤ alphaZ B m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjm
  exact alphaZ_le_add_local B hB j d

/-- AFP Exponentiation, equation 3.63: with `v = alphaZ B (m+1) - alphaZ B (m-1)`
(equation 3.61), `2 * alphaZ B j < v` whenever `j ≤ m`, `0 < m` and `3 < B`. -/
theorem two_mul_alphaZ_lt_companion (B j m : Nat)
    (hB : 3 < B) (hm : 0 < m) (hjm : j ≤ m) :
    2 * alphaZ B j < alphaZ B (m + 1) - alphaZ B (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hB2 : 2 ≤ B := by omega
  have hBZ : (4 : Int) ≤ (B : Int) := by omega
  -- Recurrence at `m + 1 = k + 2` and the natural predecessor `m - 1 = k`.
  have e1 : alphaZ B (k + 1 + 1) = (B : Int) * alphaZ B (k + 1) - alphaZ B k :=
    alphaZ_add_two B k
  have hk : k + 1 - 1 = k := by omega
  have e2 : alphaZ B (k + 1 - 1) = alphaZ B k := by rw [hk]
  rw [e1, e2]
  -- Monotonicity, strict step, and nonnegativity.
  have hj : alphaZ B j ≤ alphaZ B (k + 1) := alphaZ_le_of_le_local B hB2 hjm
  have hlt : alphaZ B k < alphaZ B (k + 1) := alphaZ_succ_strict B k hB2
  have h0 : 0 ≤ alphaZ B k := (alphaZ_step B hB2 k).1
  have h1 : 0 ≤ alphaZ B (k + 1) := by linarith
  -- `B ≥ 4` gives `4 * alphaZ B (k+1) ≤ B * alphaZ B (k+1)`.
  have hmul : 4 * alphaZ B (k + 1) ≤ (B : Int) * alphaZ B (k + 1) :=
    mul_le_mul_of_nonneg_right hBZ h1
  -- `2 a_j ≤ 2 a_m ≤ (B - 2) a_m < B a_m - 2 a_{m-1}`.
  linarith

end ZInQ.AlphaPower

end

