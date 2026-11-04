module

public import ZInQ.PoleValuation
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
The literal integer-coefficient pole polynomial on the fixed coordinate order
B, b0, b1, b2, b3, b4, b5, e, z, r1, r2, w.
The JavaScript library root has one additional outer square.
-/

public section

namespace ZInQ.PolePolynomial

open ZInQ.ValuationObstruction

/-- The coordinate of Boolean bit i in the twelve-coordinate polynomial. -/
@[expose] def bitIndex (i : Fin 6) : Fin 12 :=
  (Fin.castAdd 5 i).succ

/-- Read the eleven witness coordinates in their actual JavaScript order. -/
@[expose] def witnessOfCoordinates (x : Fin 12 → Rat) : PoleWitness where
  bit i := x (bitIndex i)
  e := x 7
  z := x 8
  r1 := x 9
  r2 := x 10
  w := x 11

/-- Insert B before the six bits and the five remaining witness coordinates. -/
@[expose] def coordinates (B : Rat) (v : PoleWitness) : Fin 12 → Rat :=
  Fin.cons B (Fin.append v.bit
    (Fin.cons v.e (Fin.cons v.z (Fin.cons v.r1
      (Fin.cons v.r2 (Fin.cons v.w Fin.elim0))))))

noncomputable section

/-- The polynomial Q_pole displayed in explicit-pole-predicate.txt, equation (1). -/
@[expose] def polePolynomial : MvPolynomial (Fin 12) Int :=
  let X : Fin 12 → MvPolynomial (Fin 12) Int := MvPolynomial.X
  let m := (1 - 2 * X 1) * (1 + X 2) * (1 + 2 * X 3) *
    (1 + 4 * X 4) * (1 + 6 * X 5) * (1 + 12 * X 6)
  let A := m * X 0
  let H := A * (A - X 0 ^ 2)
  let T1 := A * (A - X 7) * (A + 3 * X 7)
  let T2 := A * (A * X 8 ^ 2 - X 7 * H) *
    (A * X 8 ^ 2 + 3 * X 7 * H)
  X 0 * (Finset.univ.sum (fun i : Fin 6 =>
      (X (bitIndex i) ^ 2 - X (bitIndex i)) ^ 2) +
    (X 7 * H * X 8 * X 11 - 1) ^ 2 +
    (X 9 ^ 2 - T1) ^ 2 + (X 10 ^ 2 - T2) ^ 2)

/-- The actual pole template root after RationalBuilder's singleton conjunction. -/
@[expose] def compiledPolePolynomial : MvPolynomial (Fin 12) Int :=
  polePolynomial ^ 2

end

end ZInQ.PolePolynomial


end

public section

namespace ZInQ.PolePolynomial
open ZInQ.ValuationObstruction

private theorem coordinates_bit (B : Rat) (v : PoleWitness) (i : Fin 6) :
    coordinates B v (bitIndex i) = v.bit i := by
  fin_cases i <;> rfl

theorem witnessOfCoordinates_coordinates (B : Rat) (v : PoleWitness) :
    witnessOfCoordinates (coordinates B v) = v := by
  cases v with
  | mk bit e z r1 r2 w =>
    change PoleWitness.mk
        (fun i => coordinates B ⟨bit, e, z, r1, r2, w⟩ (bitIndex i)) e z r1 r2 w =
      PoleWitness.mk bit e z r1 r2 w
    exact congrArg (fun f => PoleWitness.mk f e z r1 r2 w)
      (funext (coordinates_bit B ⟨bit, e, z, r1, r2, w⟩))

theorem coordinates_witnessOfCoordinates (x : Fin 12 → Rat) :
    coordinates (x 0) (witnessOfCoordinates x) = x := by
  funext i
  fin_cases i <;> rfl

theorem eval_polePolynomial (B : Rat) (v : PoleWitness) :
    MvPolynomial.eval₂ (Int.castRingHom Rat) (coordinates B v) polePolynomial =
    B * (Finset.univ.sum (fun i : Fin 6 => ((v.bit i) ^ 2 - v.bit i) ^ 2) +
      (v.e * poleH B v * v.z * v.w - 1) ^ 2 +
      (v.r1 ^ 2 - poleA B v * (poleA B v - v.e) * (poleA B v + 3 * v.e)) ^ 2 +
      (v.r2 ^ 2 - poleA B v * (poleA B v * v.z ^ 2 - v.e * poleH B v) *
        (poleA B v * v.z ^ 2 + 3 * v.e * poleH B v)) ^ 2) := by
  simp only [polePolynomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_ofNat, MvPolynomial.eval₂_one,
    coordinates_bit]
  rfl

private theorem sum_squares_zero_iff (f : Fin 6 → Rat) (a b c : Rat) :
    (Finset.univ.sum (fun i => (f i) ^ 2)) + a ^ 2 + b ^ 2 + c ^ 2 = 0 ↔
      (∀ i, f i = 0) ∧ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    have hs : 0 ≤ Finset.univ.sum (fun i => (f i) ^ 2) :=
      Finset.sum_nonneg (fun i _ => sq_nonneg (f i))
    have ha : a ^ 2 = 0 := by linarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have hb : b ^ 2 = 0 := by linarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have hc : c ^ 2 = 0 := by linarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    have hf : Finset.univ.sum (fun i => (f i) ^ 2) = 0 := by linarith
    refine ⟨?_, sq_eq_zero_iff.mp ha, sq_eq_zero_iff.mp hb, sq_eq_zero_iff.mp hc⟩
    exact fun i => (Finset.sum_sq_eq_zero_iff Finset.univ f).mp hf i (Finset.mem_univ i)
  · rintro ⟨hf, rfl, rfl, rfl⟩
    simp only [hf, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, add_zero]

theorem eval_polePolynomial_eq_zero_iff (x : Fin 12 → Rat) :
    MvPolynomial.eval₂ (Int.castRingHom Rat) x polePolynomial = 0 ↔
      x 0 = 0 ∨ poleSystem (x 0) (witnessOfCoordinates x) := by
  have heval := eval_polePolynomial (x 0) (witnessOfCoordinates x)
  rw [coordinates_witnessOfCoordinates x] at heval
  rw [heval, mul_eq_zero, sum_squares_zero_iff]
  simp only [poleSystem, sub_eq_zero]

theorem eval_compiledPolePolynomial_eq_zero_iff (x : Fin 12 → Rat) :
    MvPolynomial.eval₂ (Int.castRingHom Rat) x compiledPolePolynomial = 0 ↔
      x 0 = 0 ∨ poleSystem (x 0) (witnessOfCoordinates x) := by
  rw [compiledPolePolynomial, MvPolynomial.eval₂_pow, sq_eq_zero_iff]
  exact eval_polePolynomial_eq_zero_iff x

theorem exists_compiledPolePolynomial_eq_zero_iff (B : Rat) :
    (∃ w : Fin 11 → Rat,
      MvPolynomial.eval₂ (Int.castRingHom Rat) (Fin.cons B w) compiledPolePolynomial = 0) ↔
      B = 0 ∨ ∃ v : PoleWitness, poleSystem B v := by
  constructor
  · rintro ⟨w, hw⟩
    have h := (eval_compiledPolePolynomial_eq_zero_iff (Fin.cons B w)).mp hw
    simp only [Fin.cons_zero] at h
    rcases h with hb | hs
    · exact Or.inl hb
    · exact Or.inr ⟨_, hs⟩
  · rintro (hb | ⟨v, hv⟩)
    · refine ⟨fun _ => 0, (eval_compiledPolePolynomial_eq_zero_iff _).mpr ?_⟩
      exact Or.inl (by simpa only [Fin.cons_zero] using hb)
    · refine ⟨Fin.tail (coordinates B v), ?_⟩
      have hc : Fin.cons B (Fin.tail (coordinates B v)) = coordinates B v := by
        simpa only [show coordinates B v 0 = B from rfl] using
          (Fin.cons_self_tail (coordinates B v))
      rw [hc]
      apply (eval_compiledPolePolynomial_eq_zero_iff _).mpr
      right
      simpa only [show coordinates B v 0 = B from rfl,
        witnessOfCoordinates_coordinates] using hv

theorem no_negative_odd_valuation_of_compiled_pole_root
    (B : Rat) (w : Fin 11 → Rat) (hB : B ≠ 0)
    (hroot : MvPolynomial.eval₂ (Int.castRingHom Rat)
      (Fin.cons B w) compiledPolePolynomial = 0)
    (p : Nat) (hp : p.Prime) (hpout : ¬ p ∣ 2730) :
    ¬ (padicValRat p B < 0 ∧ Odd (padicValRat p B)) := by
  have h := (eval_compiledPolePolynomial_eq_zero_iff (Fin.cons B w)).mp hroot
  simp only [Fin.cons_zero] at h
  rcases h with hb | hs
  · exact False.elim (hB hb)
  · exact poleSystem_no_negative_odd_valuation B _ hB hs p hp hpout

end ZInQ.PolePolynomial
