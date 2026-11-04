/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ZInQ.PrecisionAlgorithms
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Exact capped evaluation of the fixed six-contact height constant

The definitions follow `Capped.factorial` and `height_constant_capped` in
`outputs/variable-shift-precision.py`. All constants and operation ordering
are retained. The uncapped definition uses the genuine natural factorial
and powers; the evaluator uses the previously verified binary-power algorithm.
-/

public section

namespace ZInQ.HeightConstantAlgorithm

open PrecisionArithmetic PrecisionAlgorithms

/-- The ascending factorial loop, including its early overflow break. -/
@[expose] def cappedFactorialLoop (L factor count result : Nat) : Nat :=
  match count with
  | 0 => result
  | count + 1 =>
    let next := cappedMul L result factor
    if next = L + 1 then next
    else cappedFactorialLoop L (factor + 1) count next
termination_by count

/-- Python's range(2,n+1) has n-1 iterations on natural inputs. -/
@[expose] def cappedFactorial (L n : Nat) : Nat :=
  cappedFactorialLoop L 2 (n - 1) 1

/-- The two-argument use of Capped.add. -/
@[expose] def cappedAdd (L a b : Nat) : Nat := saturate L (a + b)

/-- The three-argument use of Capped.add. -/
@[expose] def cappedAddThree (L a b c : Nat) : Nat := saturate L (a + b + c)

/-- The literal H6 straight-line expression after its factorial stage. -/
@[expose] def heightBody (d0 : Nat) : Nat :=
  let d := d0 * 3 ^ (256 * d0 ^ 4)
  let g0 := 116064000000
  let e0 := 10 * (d * g0) ^ 2
  let r := max (max d 317) (10 ^ 12)
  let q0 := r ^ (r * e0)
  let dSquared := d ^ 2
  let bCm := dSquared * 3 ^ (21000 * dSquared) + 1
  let cCm := 2 * bCm + 4096 * (1028 + 5 * d + 84000 * dSquared)
  2 * 10 ^ 13 * max (max 1 cCm) (q0 ^ 17)

/-- The genuine fixed H6(primes <= 324), without any saturation. -/
@[expose] def heightConstant : Nat := heightBody (Nat.factorial 324)

/-- The source's straight-line capped computation after its factorial stage. -/
@[expose] def cappedHeightBody (L d0 : Nat) : Nat :=
  let d := cappedMul L d0 (cappedPower L 3 (cappedMul L 256 (cappedPower L d0 4)))
  let g0 := saturate L 116064000000
  let e0 := cappedMul L 10 (cappedPower L (cappedMul L d g0) 2)
  let r := max (max d (saturate L 317)) (saturate L (10 ^ 12))
  let q0 := cappedPower L r (cappedMul L r e0)
  let dSquared := cappedPower L d 2
  let bCm := cappedAdd L
    (cappedMul L dSquared (cappedPower L 3 (cappedMul L 21000 dSquared))) 1
  let cCm := cappedAdd L (cappedMul L 2 bCm)
    (cappedMul L 4096 (cappedAddThree L 1028 (cappedMul L 5 d)
      (cappedMul L 84000 dSquared)))
  cappedMul L (2 * 10 ^ 13) (max (max 1 cCm) (cappedPower L q0 17))

/-- The literal capped height program, including its cap-zero branch. -/
@[expose] def heightConstantCapped (L : Nat) : Nat :=
  if L = 0 then 1 else cappedHeightBody L (cappedFactorial L 324)

private theorem saturate_mul_left (L a b : Nat) :
    saturate L (saturate L a * b) = saturate L (a * b) := by
  calc
    saturate L (saturate L a * b) =
        saturate L (saturate L (saturate L a) * saturate L b) :=
      (saturate_mul L (saturate L a) b).symm
    _ = saturate L (a * b) := by rw [saturate_saturate, saturate_mul]

private theorem saturate_mul_right (L a b : Nat) :
    saturate L (a * saturate L b) = saturate L (a * b) := by
  rw [Nat.mul_comm a, saturate_mul_left, Nat.mul_comm b]

private theorem saturate_add_left (L a b : Nat) :
    saturate L (saturate L a + b) = saturate L (a + b) := by
  unfold saturate
  omega

private theorem saturate_add_right (L a b : Nat) :
    saturate L (a + saturate L b) = saturate L (a + b) := by
  unfold saturate
  omega

private theorem saturate_add_middle (L a b c : Nat) :
    saturate L (a + saturate L b + c) = saturate L (a + b + c) := by
  unfold saturate
  omega

private theorem max_saturate (L a b : Nat) :
    max (saturate L a) (saturate L b) = saturate L (max a b) := by
  unfold saturate
  omega

private theorem max_one_saturate (L a : Nat) :
    max 1 (saturate L a) = saturate L (max 1 a) := by
  unfold saturate
  omega

private theorem ascFactorial_front (factor count : Nat) :
    factor.ascFactorial (count + 1) =
      factor * (factor + 1).ascFactorial count := by
  rw [Nat.ascFactorial_succ, Nat.succ_ascFactorial]

private theorem saturate_cap_mul (L a : Nat) (ha : 1 ≤ a) :
    saturate L ((L + 1) * a) = L + 1 := by
  apply saturate_eq_cap
  have h := Nat.mul_le_mul_left (L + 1) ha
  omega

/-- Exact invariant for the ascending loop; no partial product is assumed. -/
theorem cappedFactorialLoop_eq_saturate (L factor count result : Nat)
    (hcap : result ≤ L + 1) :
    cappedFactorialLoop L factor count result =
      saturate L (result * factor.ascFactorial count) := by
  induction count generalizing factor result with
  | zero =>
    rw [cappedFactorialLoop, Nat.ascFactorial_zero, Nat.mul_one]
    exact (saturate_eq_self L result hcap).symm
  | succ count ih =>
    rw [cappedFactorialLoop]
    let next := cappedMul L result factor
    have hncap : next ≤ L + 1 := by
      dsimp only [next]
      rw [cappedMul_eq_saturate]
      exact saturate_le_cap L _
    have hstep : saturate L (next * (factor + 1).ascFactorial count) =
        saturate L (result * factor.ascFactorial (count + 1)) := by
      dsimp only [next]
      rw [cappedMul_eq_saturate, saturate_mul_left, ascFactorial_front,
        Nat.mul_assoc]
    change (if next = L + 1 then next
      else cappedFactorialLoop L (factor + 1) count next) = _
    by_cases hstop : next = L + 1
    · rw [ite_eq_left hstop]
      have hp : 1 ≤ (factor + 1).ascFactorial count :=
        Nat.ascFactorial_pos factor count
      rw [hstop, saturate_cap_mul L _ hp] at hstep
      exact hstop.trans hstep
    · rw [ite_eq_right hstop, ih (factor + 1) next hncap]
      exact hstep

/-- The implemented factorial has its full mathematical value up to saturation. -/
theorem cappedFactorial_eq_saturate (L n : Nat) :
    cappedFactorial L n = saturate L (Nat.factorial n) := by
  unfold cappedFactorial
  rw [cappedFactorialLoop_eq_saturate L 2 (n - 1) 1 (by omega), Nat.one_mul]
  by_cases hn : n = 0
  · subst n
    rw [Nat.zero_sub, Nat.ascFactorial_zero, Nat.factorial_zero]
  · have h := Nat.factorial_mul_ascFactorial 1 (n - 1)
    simp only [Nat.factorial_one, Nat.one_mul] at h
    have heq : 1 + (n - 1) = n := by omega
    rw [heq] at h
    rw [h]

theorem heightBody_pos (d0 : Nat) : 0 < heightBody d0 := by
  unfold heightBody
  dsimp only
  apply Nat.mul_pos
  · decide
  · exact Nat.lt_of_lt_of_le Nat.zero_lt_one
      (Nat.le_trans (Nat.le_max_left 1 _) (Nat.le_max_left _ _))

theorem heightConstant_pos : 0 < heightConstant :=
  heightBody_pos (Nat.factorial 324)

/-- Every straight-line capped operation preserves the exact capped value. -/
theorem cappedHeightBody_eq_saturate (L d0 : Nat) (hL : 1 ≤ L) :
    cappedHeightBody L (saturate L d0) = saturate L (heightBody d0) := by
  have hp (a n : Nat) :
      saturate L (a ^ saturate L n) = saturate L (a ^ n) :=
    saturate_pow_saturate_exponent L a n hL
  unfold cappedHeightBody heightBody
  dsimp only
  simp only [cappedMul_eq_saturate, cappedPower_eq_saturate, cappedAdd,
    cappedAddThree, saturate_mul_left, saturate_mul_right, saturate_add_left,
    saturate_add_right, saturate_add_middle, saturate_pow, hp, max_saturate,
    max_one_saturate]

/-- The full literal program evaluates H6 exactly below the cap. -/
theorem heightConstantCapped_eq_saturate (L : Nat) :
    heightConstantCapped L = saturate L heightConstant := by
  by_cases hzero : L = 0
  · subst L
    rw [heightConstantCapped, ite_eq_left rfl]
    exact (saturate_eq_cap 0 heightConstant heightConstant_pos).symm
  · rw [heightConstantCapped, ite_eq_right hzero, cappedFactorial_eq_saturate]
    exact cappedHeightBody_eq_saturate L (Nat.factorial 324) (by omega)

/-- The requested explicit minimum specification, valid also at cap zero. -/
theorem heightConstantCapped_eq_min (L : Nat) :
    heightConstantCapped L = min heightConstant (L + 1) :=
  heightConstantCapped_eq_saturate L

theorem heightConstantCapped_zero : heightConstantCapped 0 = 1 := rfl

/-- The capped height test is an exact comparison with the uncapped integer. -/
theorem heightConstantCapped_le_iff (L : Nat) :
    heightConstantCapped L ≤ L ↔ heightConstant ≤ L := by
  rw [heightConstantCapped_eq_saturate, saturate_le_iff]

end ZInQ.HeightConstantAlgorithm
