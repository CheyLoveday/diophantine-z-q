module

public import ZInQ.NumericalTowerBounds
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
Literal arithmetic bound for the closed cutoff expression in section 5 of
`outputs/z-in-q-explicit-cutoff-bound.txt`.

This helper does not identify that expression with the candidate's selector
cutoff. It does not assert any property of the candidate polynomial.
-/

public section

namespace ZInQ.ExplicitCutoffBounds

/-- The source's F = 324!. -/
@[expose] def factorialBase : Nat := Nat.factorial 324

/-- The source's D, with the factorial and power parentheses preserved. -/
@[expose] def d : Nat := factorialBase * 3 ^ (256 * factorialBase ^ 4)

/-- The source's fixed G0. -/
@[expose] def g0 : Nat := 116064000000

/-- The closed T expression in section 5, before any numerical bounding. -/
@[expose] def t : Nat :=
  (96 * 10 ^ 13) ^ 13 * d ^ (2210 * g0 ^ 2 * d ^ 3)

private theorem d_def : d = factorialBase * 3 ^ (256 * factorialBase ^ 4) := by
  let F := factorialBase
  have h : d = F * 3 ^ (256 * F ^ 4) := rfl
  exact h

private theorem t_def : t = (96 * 10 ^ 13) ^ 13 * d ^ (2210 * g0 ^ 2 * d ^ 3) := by
  let D := d
  let G := g0
  have h : t = (96 * 10 ^ 13) ^ 13 * D ^ (2210 * G ^ 2 * D ^ 3) := rfl
  exact h

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 2250 in
private theorem factorial_bounds :
    2 ^ 2000 < factorialBase ∧ factorialBase < 2 ^ 2250 := by
  decide

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 650 in
private theorem prefactor_bound : (96 * 10 ^ 13 : Nat) ^ 13 < 2 ^ 650 := by
  decide

private theorem exponent_coefficient_bound : 2210 * g0 ^ 2 < 2 ^ 100 := by
  decide

set_option exponentiation.threshold 2250 in
private theorem arithmetic_bound (F G a : Nat)
    (hF : 2 ^ 2000 < F ∧ F < 2 ^ a)
    (hG : 2210 * G ^ 2 < 2 ^ 100) (hGp : 0 < G) :
    (96 * 10 ^ 13) ^ 13 *
      (F * 3 ^ (256 * F ^ 4)) ^ (2210 * G ^ 2 * (F * 3 ^ (256 * F ^ 4)) ^ 3) <
      ZInQ.NumericalTowerBounds.triplePower (a * 4 + 13) := by
  let D := F * 3 ^ (256 * F ^ 4)
  have d_lower : 2 ^ 2000 < D :=
    hF.1.trans_le (Nat.le_mul_of_pos_right _
      (by positivity : 0 < 3 ^ (256 * F ^ 4)))

  have d_upper : D < 2 ^ (2 ^ (a * 4 + 10)) := by
    have hF4 : F ^ 4 < 2 ^ (a * 4) := by
      have h := Nat.pow_lt_pow_left hF.2 (by decide : 4 ≠ 0)
      calc
        F ^ 4 < (2 ^ a) ^ 4 := h
        _ = 2 ^ (a * 4) := by rw [← Nat.pow_mul]
    have hE : 256 * F ^ 4 < 2 ^ (a * 4 + 8) := by
      calc
        256 * F ^ 4 < 256 * 2 ^ (a * 4) :=
          Nat.mul_lt_mul_of_pos_left hF4 (by decide)
        _ = 2 ^ (a * 4 + 8) := by
          rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_add]
          congr 1
          omega
    have h2E : 2 * (256 * F ^ 4) < 2 ^ (a * 4 + 9) := by
      calc
        2 * (256 * F ^ 4) < 2 * 2 ^ (a * 4 + 8) :=
          Nat.mul_lt_mul_of_pos_left hE (by decide)
        _ = 2 ^ (a * 4 + 9) := by rw [Nat.mul_comm, ← Nat.pow_succ]
    have hPow : 3 ^ (256 * F ^ 4) < 2 ^ (2 ^ (a * 4 + 9)) := by
      calc
        3 ^ (256 * F ^ 4) < 4 ^ (256 * F ^ 4) :=
          Nat.pow_lt_pow_left (by decide) (by
            have h : 0 < F := Nat.zero_lt_of_lt hF.1
            positivity)
        _ = 2 ^ (2 * (256 * F ^ 4)) := by
          rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul]
        _ < 2 ^ (2 ^ (a * 4 + 9)) := Nat.pow_lt_pow_right (by decide) h2E
    have ha : a < 2 ^ (a * 4 + 9) :=
      Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) (by omega : a ≤ a * 4 + 9))
    have hSum : a + 2 ^ (a * 4 + 9) < 2 ^ (a * 4 + 10) := by
      calc
        a + 2 ^ (a * 4 + 9) < 2 ^ (a * 4 + 9) + 2 ^ (a * 4 + 9) := Nat.add_lt_add_right ha _
        _ = 2 ^ (a * 4 + 10) := by rw [← Nat.mul_two, ← Nat.pow_succ]
    calc
      D < 2 ^ a * 2 ^ (2 ^ (a * 4 + 9)) :=
        Nat.mul_lt_mul_of_lt_of_lt hF.2 hPow
      _ = 2 ^ (a + 2 ^ (a * 4 + 9)) := (Nat.pow_add 2 a (2 ^ (a * 4 + 9))).symm
      _ < 2 ^ (2 ^ (a * 4 + 10)) := Nat.pow_lt_pow_right (by decide) hSum

  have t_lt_two_pow_d_eight : (96 * 10 ^ 13) ^ 13 * D ^ (2210 * G ^ 2 * D ^ 3) < 2 ^ (D ^ 8) := by
    have hd3 : 3 ≤ D := by
      set_option exponentiation.threshold 2000 in
        exact le_trans (le_trans (by decide : 3 ≤ 2 ^ 2)
          (Nat.pow_le_pow_right (n := 2) (i := 2) (j := 2000) (by decide) (by decide)))
          (Nat.le_of_lt d_lower)
    have hd0 : 0 < D := lt_of_lt_of_le (by decide : 0 < 3) hd3
    have hd650 : 650 < D :=
      (Nat.lt_two_pow_self.trans_le
        (Nat.pow_le_pow_right (n := 2) (i := 650) (j := 2000) (by decide) (by decide))).trans d_lower
    have hC : 2210 * G ^ 2 < D :=
      hG.trans
        ((Nat.pow_lt_pow_right (by decide) (by decide : 100 < 2000)).trans d_lower)
    have hE : 2210 * G ^ 2 * D ^ 3 < D ^ 4 := by
      calc
        2210 * G ^ 2 * D ^ 3 < D * D ^ 3 :=
          Nat.mul_lt_mul_of_pos_right hC (by positivity)
        _ = D ^ 4 := by ring
    have hDE : D * (2210 * G ^ 2 * D ^ 3) < D ^ 5 := by
      calc
        D * (2210 * G ^ 2 * D ^ 3) < D * D ^ 4 :=
          Nat.mul_lt_mul_of_pos_left hE hd0
        _ = D ^ 5 := by ring
    have hDP : D ^ (2210 * G ^ 2 * D ^ 3) < 2 ^ (D ^ 5) := by
      calc
        D ^ (2210 * G ^ 2 * D ^ 3) < (2 ^ D) ^ (2210 * G ^ 2 * D ^ 3) :=
          Nat.pow_lt_pow_left Nat.lt_two_pow_self (by
            positivity)
        _ = 2 ^ (D * (2210 * G ^ 2 * D ^ 3)) := (Nat.pow_mul 2 D (2210 * G ^ 2 * D ^ 3)).symm
        _ < 2 ^ (D ^ 5) := Nat.pow_lt_pow_right (by decide) hDE
    have hSmall : 650 + D ^ 5 < D ^ 8 := by
      calc
        650 + D ^ 5 < D + D ^ 5 := Nat.add_lt_add_right hd650 _
        _ ≤ D ^ 5 + D ^ 5 := Nat.add_le_add_right
          (by simpa only [pow_one] using Nat.pow_le_pow_right hd0 (by decide : 1 ≤ 5)) _
        _ = 2 * D ^ 5 := by ring
        _ < D * D ^ 5 := Nat.mul_lt_mul_of_pos_right
          (lt_of_lt_of_le (by decide : 2 < 3) hd3) (by positivity)
        _ = D ^ 6 := by ring
        _ ≤ D ^ 8 := Nat.pow_le_pow_right hd0 (by decide)
    calc
      (96 * 10 ^ 13) ^ 13 * D ^ (2210 * G ^ 2 * D ^ 3) < 2 ^ 650 * 2 ^ (D ^ 5) :=
        Nat.mul_lt_mul_of_lt_of_lt prefactor_bound hDP
      _ = 2 ^ (650 + D ^ 5) := (Nat.pow_add 2 650 (D ^ 5)).symm
      _ < 2 ^ (D ^ 8) := Nat.pow_lt_pow_right (by decide) hSmall

  have hD8 : D ^ 8 < 2 ^ (2 ^ (a * 4 + 13)) := by
    calc
      D ^ 8 < (2 ^ (2 ^ (a * 4 + 10))) ^ 8 :=
        Nat.pow_lt_pow_left d_upper (by decide)
      _ = 2 ^ ((2 ^ (a * 4 + 10)) * 8) := (Nat.pow_mul 2 (2 ^ (a * 4 + 10)) 8).symm
      _ = 2 ^ (2 ^ (a * 4 + 13)) := by
        rw [show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.pow_add]
  exact t_lt_two_pow_d_eight.trans (Nat.pow_lt_pow_right (by decide) hD8)


/-- The literal closed cutoff is below three powers of two with bottom 9013. -/
theorem t_lt_triplePower :
    t < ZInQ.NumericalTowerBounds.triplePower 9013 := by
  have h := arithmetic_bound factorialBase g0 2250 factorial_bounds exponent_coefficient_bound (by decide)
  have hdEq := congrArg
    (fun x : Nat => (96 * 10 ^ 13) ^ 13 * x ^ (2210 * g0 ^ 2 * x ^ 3) <
      ZInQ.NumericalTowerBounds.triplePower (2250 * 4 + 13)) d_def
  have hD := Eq.mpr hdEq h
  have htEq := congrArg
    (fun x : Nat => x < ZInQ.NumericalTowerBounds.triplePower (2250 * 4 + 13)) t_def
  have hT := Eq.mpr htEq hD
  have he : ZInQ.NumericalTowerBounds.triplePower (2250 * 4 + 13) =
      ZInQ.NumericalTowerBounds.triplePower 9013 :=
    congrArg ZInQ.NumericalTowerBounds.triplePower (by decide : (2250 : Nat) * 4 + 13 = 9013)
  exact hT.trans_eq he

end ZInQ.ExplicitCutoffBounds
