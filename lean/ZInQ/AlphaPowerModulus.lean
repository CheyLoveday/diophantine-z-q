module

public import ZInQ.AlphaCore

/-!
# Builder.power: final additive congruence (divisibility form of AFP `860`)

For every natural `B` (including `0`, `1`, `2`), every natural `r` (including `0`) and every
integer `q` (of any sign), the modulus `m = B*q - q*q - 1` (possibly zero or negative) divides
`q * alphaZ B r - (B * alphaZ B r - alphaZ B (r + 1)) - q ^ r`.

Proof: put `E r = q * alphaZ B r - (B * alphaZ B r - alphaZ B (r + 1))`. Then `E 0 = 1 = q ^ 0`
and, from the defining recurrence, `E (r + 1) - q ^ (r + 1) = q * (E r - q ^ r) + m * alphaZ B r`,
so the claim follows by induction on `r` using closure of divisibility under `q * _` and `+`.

This is only the additive congruence used by the power macro; it does not prove the whole
power encoding.
-/

public section

namespace ZInQ.AlphaPower

theorem alphaZ_power_modulus_dvd (B r : Nat) (q : Int) :
    ((B : Int) * q - q * q - 1) ∣
      (q * alphaZ B r - ((B : Int) * alphaZ B r - alphaZ B (r + 1)) - q ^ r) := by
  induction r with
  | zero =>
    -- `E 0 = q * 0 - (B * 0 - 1) = 1 = q ^ 0`, so the difference is `0`.
    simp [alphaZ_zero, alphaZ_one]
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    -- `E (n+1) - q^(n+1) = q * (E n - q^n) + m * alphaZ B n = m * (q * c + alphaZ B n)`.
    refine ⟨q * c + alphaZ B n, ?_⟩
    rw [show n + 1 + 1 = n + 2 from rfl, alphaZ_add_two]
    linear_combination q * hc

end ZInQ.AlphaPower

