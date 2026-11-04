/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ZInQ.PrecisionArithmetic

/-!
# Executable capped multiplication and binary exponentiation

This follows `Capped.mul` and `Capped.power` in
`outputs/variable-shift-precision.py`. The loop keeps the Python order:
check the current base, multiply on an odd bit, return on overflow, halve
the exponent, and square the base only when another iteration is needed.
Natural inputs exclude the Python negative-input error branches. The checked
wrapper implements the constructor's rejection of a zero cap. The two bit
lemmas below identify the source's `& 1` and `>> 1` with the arithmetic
operations used by the recursive definition.
-/

public section

namespace ZInQ.PrecisionAlgorithms

open PrecisionArithmetic

/-- The low-bit test used by the Python loop is reduction modulo two. -/
theorem and_one_eq_mod_two (n : Nat) : n &&& 1 = n % 2 :=
  Nat.and_one_is_mod n

/-- Shifting a natural number right by one is division by two. -/
theorem shiftRight_one_eq_div_two (n : Nat) : n >>> 1 = n / 2 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]

/-- The division-guarded multiplication used by `Capped.mul`. -/
@[expose] def cappedMul (L a b : Nat) : Nat :=
  if a = 0 ∨ b = 0 then 0
  else if a > L / b then L + 1 else a * b

theorem cappedMul_eq_saturate (L a b : Nat) :
    cappedMul L a b = saturate L (a * b) := by
  unfold cappedMul
  by_cases hz : a = 0 ∨ b = 0
  · rw [ite_eq_left hz]
    rcases hz with ha | hb
    · subst a
      simp only [Nat.zero_mul, saturate_zero]
    · subst b
      simp only [Nat.mul_zero, saturate_zero]
  · rw [ite_eq_right hz]
    have hb : 0 < b := by omega
    by_cases h : a > L / b
    · rw [ite_eq_left h]
      have hp : L + 1 ≤ a * b := by
        have hn : ¬ a * b ≤ L := by
          intro hab
          exact (Nat.not_le_of_gt h) ((Nat.le_div_iff_mul_le hb).2 hab)
        omega
      exact (saturate_eq_cap L _ hp).symm
    · rw [ite_eq_right h]
      have hp : a * b ≤ L := (Nat.le_div_iff_mul_le hb).1 (by omega)
      exact (saturate_eq_self L _ (by omega)).symm

/-- Tail-recursive translation of the body of the Python `while exponent`. -/
@[expose] def cappedPowerLoop (L base exponent result : Nat) : Nat :=
  if exponent = 0 then result
  else if base > L then L + 1
  else
    let next := if exponent % 2 = 1 then cappedMul L result base else result
    if exponent % 2 = 1 ∧ next = L + 1 then next
    else if exponent / 2 = 0 then next
    else cappedPowerLoop L (cappedMul L base base) (exponent / 2) next
termination_by exponent
 decreasing_by
  apply Nat.div_lt_self
  · omega
  · decide

/-- Natural-input translation of `Capped.power`, including its initial cases. -/
@[expose] def cappedPower (L base exponent : Nat) : Nat :=
  if exponent = 0 then 1
  else if base ≤ 1 then base
  else cappedPowerLoop L base exponent 1

/-- `Capped` rejects cap zero before its power routine can be called. -/
@[expose] def checkedCappedPower (L base exponent : Nat) : Option Nat :=
  if L = 0 then none else some (cappedPower L base exponent)

private theorem saturate_mul_left (L a b : Nat) :
    saturate L (saturate L a * b) = saturate L (a * b) := by
  calc
    saturate L (saturate L a * b) =
        saturate L (saturate L (saturate L a) * saturate L b) :=
      (saturate_mul L (saturate L a) b).symm
    _ = saturate L (a * b) := by
      rw [saturate_saturate, saturate_mul]

private theorem saturate_mul_right (L a b : Nat) :
    saturate L (a * saturate L b) = saturate L (a * b) := by
  rw [Nat.mul_comm a, saturate_mul_left, Nat.mul_comm b]

private theorem saturate_mul_pow (L a b n : Nat) :
    saturate L (a * saturate L b ^ n) = saturate L (a * b ^ n) := by
  calc
    saturate L (a * saturate L b ^ n) =
        saturate L (a * saturate L (saturate L b ^ n)) :=
      (saturate_mul_right L a _).symm
    _ = saturate L (a * saturate L (b ^ n)) := by rw [saturate_pow]
    _ = saturate L (a * b ^ n) := saturate_mul_right L a _

private theorem power_split_bit (base n : Nat) :
    base ^ n = (if n % 2 = 1 then base else 1) * (base * base) ^ (n / 2) := by
  have hm : n % 2 < 2 := Nat.mod_lt n (by decide)
  have hn := Nat.mod_add_div n 2
  by_cases hbit : n % 2 = 1
  · rw [ite_eq_left hbit]
    calc
      base ^ n = base ^ (1 + 2 * (n / 2)) := by congr 1; omega
      _ = base * (base * base) ^ (n / 2) := by
        rw [Nat.pow_add, Nat.pow_mul]
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  · rw [ite_eq_right hbit]
    have hzero : n % 2 = 0 := by omega
    calc
      base ^ n = base ^ (2 * (n / 2)) := by congr 1; omega
      _ = 1 * (base * base) ^ (n / 2) := by
        rw [Nat.pow_mul]
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]

private theorem advance_correct (L base n result : Nat) :
    saturate L
      ((if n % 2 = 1 then cappedMul L result base else result) *
        cappedMul L base base ^ (n / 2)) =
      saturate L (result * base ^ n) := by
  rw [cappedMul_eq_saturate L base base, saturate_mul_pow, power_split_bit base n]
  by_cases hbit : n % 2 = 1
  · rw [ite_eq_left hbit, ite_eq_left hbit, cappedMul_eq_saturate,
      saturate_mul_left, Nat.mul_assoc]
  · rw [ite_eq_right hbit, ite_eq_right hbit, Nat.one_mul]

private theorem cappedMul_pos (L a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ cappedMul L a b := by
  rw [cappedMul_eq_saturate]
  have hp := Nat.mul_pos (show 0 < a by omega) (show 0 < b by omega)
  unfold saturate
  omega

private theorem saturate_cap_mul (L a : Nat) (ha : 1 ≤ a) :
    saturate L ((L + 1) * a) = L + 1 := by
  apply saturate_eq_cap
  have h := Nat.mul_le_mul_left (L + 1) ha
  omega

/-- The accumulator invariant for every reachable loop state. -/
theorem cappedPowerLoop_eq_saturate (L base exponent result : Nat)
    (hbase : 1 ≤ base) (hresult : 1 ≤ result) (hcap : result ≤ L + 1) :
    cappedPowerLoop L base exponent result = saturate L (result * base ^ exponent) := by
  induction exponent using Nat.strongRecOn generalizing base result with
  | ind exponent ih =>
    by_cases hz : exponent = 0
    · subst exponent
      rw [cappedPowerLoop, ite_eq_left rfl]
      simp only [Nat.pow_zero, Nat.mul_one]
      exact (saturate_eq_self L result hcap).symm
    · rw [cappedPowerLoop, ite_eq_right hz]
      by_cases hover : base > L
      · rw [ite_eq_left hover]
        have hpow : base ≤ base ^ exponent := by
          have h := Nat.pow_le_pow_right (show 0 < base by omega)
            (show 1 ≤ exponent by omega)
          simpa only [Nat.pow_one] using h
        have hprod : base ^ exponent ≤ result * base ^ exponent := by
          have h := Nat.mul_le_mul_right (base ^ exponent) hresult
          simpa only [Nat.one_mul] using h
        exact (saturate_eq_cap L _ (by omega)).symm
      · rw [ite_eq_right hover]
        let next := if exponent % 2 = 1 then cappedMul L result base else result
        have hnpos : 1 ≤ next := by
          dsimp [next]
          split
          · exact cappedMul_pos L result base hresult hbase
          · exact hresult
        have hncap : next ≤ L + 1 := by
          dsimp [next]
          split
          · rw [cappedMul_eq_saturate]
            exact saturate_le_cap L _
          · exact hcap
        have hspos : 1 ≤ cappedMul L base base := cappedMul_pos L base base hbase hbase
        have hstep := advance_correct L base exponent result
        change saturate L (next * cappedMul L base base ^ (exponent / 2)) =
          saturate L (result * base ^ exponent) at hstep
        change (if exponent % 2 = 1 ∧ next = L + 1 then next
          else if exponent / 2 = 0 then next
          else cappedPowerLoop L (cappedMul L base base) (exponent / 2) next) = _
        by_cases hstop : exponent % 2 = 1 ∧ next = L + 1
        · rw [ite_eq_left hstop]
          have hp : 1 ≤ cappedMul L base base ^ (exponent / 2) :=
            Nat.one_le_pow _ _ (by omega)
          rw [hstop.2, saturate_cap_mul L _ hp] at hstep
          exact hstop.2.trans hstep
        · rw [ite_eq_right hstop]
          by_cases hhalf : exponent / 2 = 0
          · rw [ite_eq_left hhalf]
            rw [hhalf, Nat.pow_zero, Nat.mul_one,
              saturate_eq_self L next hncap] at hstep
            exact hstep
          · rw [ite_eq_right hhalf]
            rw [ih (exponent / 2) (Nat.div_lt_self (by omega) (by decide))
              (cappedMul L base base) next hspos hnpos hncap]
            exact hstep

/-- The Python binary-power algorithm returns the exact capped power. -/
theorem cappedPower_eq_saturate (L base exponent : Nat) :
    cappedPower L base exponent = saturate L (base ^ exponent) := by
  unfold cappedPower
  by_cases hz : exponent = 0
  · rw [ite_eq_left hz, hz, Nat.pow_zero, saturate_one]
  · rw [ite_eq_right hz]
    by_cases hb : base ≤ 1
    · rw [ite_eq_left hb]
      have hcases : base = 0 ∨ base = 1 := by omega
      rcases hcases with hzero | hone
      · subst base
        rw [Nat.zero_pow (by omega), saturate_zero]
      · subst base
        rw [Nat.one_pow, saturate_one]
    · rw [ite_eq_right hb, cappedPowerLoop_eq_saturate L base exponent 1
        (by omega) (by decide) (by omega), Nat.one_mul]

/-- A zero cap is rejected; every positive cap has the exact source result. -/
theorem checkedCappedPower_eq (L base exponent : Nat) :
    checkedCappedPower L base exponent =
      if L = 0 then none else some (saturate L (base ^ exponent)) := by
  unfold checkedCappedPower
  rw [cappedPower_eq_saturate]

theorem checkedCappedPower_zero_cap (base exponent : Nat) :
    checkedCappedPower 0 base exponent = none := rfl

/-- The result compares to the cap exactly when the ordinary power does. -/
theorem cappedPower_le_iff (L base exponent : Nat) :
    cappedPower L base exponent ≤ L ↔ base ^ exponent ≤ L := by
  rw [cappedPower_eq_saturate, saturate_le_iff]

end ZInQ.PrecisionAlgorithms
