module

public import ZInQ.AlphaPowerBounds

/-!
AFP `Exponentiation.thy` lemma 89, after substituting its `b` and `m`:
for `0 < q`, `q ^ r < (alphaZ (q + 4) (r + 1) + q ^ 2 + 2) * q - q ^ 2 - 1`
over `Int`. Route: `q ^ r ≤ (q + 3) ^ r ≤ alphaZ (q + 4) (r + 1)` by the
integrated `pow_le_alphaZ_succ` at base `q + 3`; then `alphaZ ≤ alphaZ * q`,
and the remaining margin `q ^ 2 * (q - 1) + 2 * q - 1` is positive.
This bound helper does not establish the power encoding.
-/

public section

namespace ZInQ.AlphaPower

theorem pow_lt_alphaZ_power_modulus (q r : Nat) (hq : 0 < q) :
    (q : Int) ^ r <
      (alphaZ (q + 4) (r + 1) + (q : Int) ^ 2 + 2) * (q : Int) -
        (q : Int) ^ 2 - 1 := by
  -- AFP `alpha_exponential_1` at base `q + 3`.
  have h1 : ((q : Int) + 3) ^ r ≤ alphaZ (q + 4) (r + 1) := by
    have h := pow_le_alphaZ_succ (q + 3) r (by omega)
    rw [show q + 3 + 1 = q + 4 by omega] at h
    push_cast at h
    exact h
  have hq1 : (1 : Int) ≤ (q : Int) := by omega
  -- Monotonicity of `· ^ r` on nonnegative integers.
  have h2 : (q : Int) ^ r ≤ ((q : Int) + 3) ^ r :=
    pow_le_pow_left₀ (Int.natCast_nonneg q) (by linarith) r
  have h3 : (1 : Int) ≤ (q : Int) ^ r := one_le_pow₀ hq1
  have hA : (1 : Int) ≤ alphaZ (q + 4) (r + 1) := by linarith
  -- `alphaZ ≤ alphaZ * q`.
  have h4 : (0 : Int) ≤ alphaZ (q + 4) (r + 1) * ((q : Int) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  -- The margin `q ^ 2 * (q - 1) + 2 * q - 1` is positive.
  have h5 : (0 : Int) ≤ (q : Int) ^ 2 * ((q : Int) - 1) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  linarith

end ZInQ.AlphaPower

end

