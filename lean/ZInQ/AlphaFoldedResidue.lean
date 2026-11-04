module

public import ZInQ.AlphaPeriodReflection

/-!
# Folded signed residue for the alpha recurrence (internal interface L05)

AFP `Exponentiation.thy` lines 1145–1148 (equation 3.62.1 and its "more usable version"):
from `a ≡ alphaZ b n (mod v)` with the companion modulus
`v = alphaZ b (m + 1) - alphaZ b (m - 1)` and a folded index
`n = 2lm + j` or `n = 2lm - j` (with `0 < j < 2lm`), conclude
`v ∣ a - alphaZ b j` or `v ∣ a + alphaZ b j`.

All indices are natural numbers, residues and divisibility are over `Int`, and `m - 1`,
`2 * l * m - j` are natural subtraction. No positivity of `m` or `l` is assumed: for `m = 0`
the modulus is `alphaZ b 1 - alphaZ b 0 = 1` and the conclusion holds trivially through the
same argument.

The proof consumes the root-accepted period theorems unchanged:
* `companion_dvd_alphaZ_add_period` (AFP `361`) for the unfolded branch, and
* `companion_dvd_alphaZ_reflection` (AFP `362`) for the reflected branch,
then splits on `(-1)^l = 1 ∨ (-1)^l = -1`, keeping both sign alternatives explicit.

This is an internal helper only. It does not establish the full alpha encoding
(`alpha_equiv_suff`), the bounded recovery steps (L06/L07), or any compiler correctness.
-/

public section

namespace ZInQ.AlphaPower

/-- AFP `3.62.1` (lines 1145–1148) as a two-sided divisibility statement over `Int`. -/
theorem folded_alpha_signed_residue (b a v n m l j : Nat)
    (hb : 2 < b)
    (hv : (v : Int) = alphaZ b (m+1) - alphaZ b (m-1))
    (ha : (a : Int) % (v : Int) = alphaZ b n % (v : Int))
    (hf : n = 2*l*m+j ∨ (n = 2*l*m-j ∧ 0 < j ∧ j < 2*l*m)) :
    ((v : Int) ∣ (a : Int) - alphaZ b j) ∨
      ((v : Int) ∣ (a : Int) + alphaZ b j) := by
  -- AFP 1148 (`mod_eq_dvd_iff`): the `Int` residue hypothesis as `v ∣ a - alphaZ b n`.
  have hres : (v : Int) ∣ (a : Int) - alphaZ b n :=
    Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp ha)
  -- The sign `(-1)^l` is `1` or `-1`.
  have hsign := neg_one_pow_eq_or Int l
  rcases hf with hn | ⟨hn, hj, hjlt⟩
  · -- Unfolded index `n = 2lm + j`: AFP 361 gives `alphaZ n ≡ (-1)^l * alphaZ j (mod v)`.
    have hper := companion_dvd_alphaZ_add_period b m j l hb
    have hidx : j + 2 * l * m = n := by omega
    rw [← hv, hidx] at hper
    -- hence `a ≡ (-1)^l * alphaZ j (mod v)`
    have hkey : (v : Int) ∣ (a : Int) - (-1 : Int) ^ l * alphaZ b j := by
      have e : (a : Int) - (-1 : Int) ^ l * alphaZ b j =
          ((a : Int) - alphaZ b n) + (alphaZ b n - (-1 : Int) ^ l * alphaZ b j) := by
        ring
      rw [e]
      exact dvd_add hres hper
    rcases hsign with hs | hs
    · -- `(-1)^l = 1`: `v ∣ a - alphaZ j`
      left
      have e : (a : Int) - alphaZ b j = (a : Int) - (-1 : Int) ^ l * alphaZ b j := by
        linear_combination (alphaZ b j) * hs
      rw [e]
      exact hkey
    · -- `(-1)^l = -1`: `v ∣ a + alphaZ j`
      right
      have e : (a : Int) + alphaZ b j = (a : Int) - (-1 : Int) ^ l * alphaZ b j := by
        linear_combination (alphaZ b j) * hs
      rw [e]
      exact hkey
  · -- Reflected index `n = 2lm - j`, `0 < j < 2lm`: AFP 362 gives
    -- `alphaZ n ≡ -((-1)^l * alphaZ j) (mod v)`.
    have hrefl := companion_dvd_alphaZ_reflection b m j l hb hj hjlt
    rw [← hv, ← hn] at hrefl
    -- hence `a ≡ -((-1)^l * alphaZ j) (mod v)`
    have hkey : (v : Int) ∣ (a : Int) + (-1 : Int) ^ l * alphaZ b j := by
      have e : (a : Int) + (-1 : Int) ^ l * alphaZ b j =
          ((a : Int) - alphaZ b n) + (alphaZ b n + (-1 : Int) ^ l * alphaZ b j) := by
        ring
      rw [e]
      exact dvd_add hres hrefl
    rcases hsign with hs | hs
    · -- `(-1)^l = 1`: `v ∣ a + alphaZ j`
      right
      have e : (a : Int) + alphaZ b j = (a : Int) + (-1 : Int) ^ l * alphaZ b j := by
        linear_combination (-alphaZ b j) * hs
      rw [e]
      exact hkey
    · -- `(-1)^l = -1`: `v ∣ a - alphaZ j`
      left
      have e : (a : Int) - alphaZ b j = (a : Int) + (-1 : Int) ^ l * alphaZ b j := by
        linear_combination (-alphaZ b j) * hs
      rw [e]
      exact hkey

end ZInQ.AlphaPower
