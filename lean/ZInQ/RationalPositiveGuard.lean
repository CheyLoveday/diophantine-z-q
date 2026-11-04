module

public import Mathlib.NumberTheory.SumFourSquares
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Rational positivity guard via four squares

Mathematical rational positive guard only (review TR-G, positivity clause):
a rational `x` is positive exactly when `x` times some sum of four rational
squares equals `1`.  The forward direction applies Mathlib's Lagrange theorem
`Nat.sum_four_squares` to `num * den` of the positive reciprocal `x⁻¹`; the
reverse direction uses nonnegativity of sums of squares, which excludes `x = 0`
and every negative `x`.

No identification with any emitted primitive polynomial or with the absent
rational builder implementation is claimed.
-/

public section

namespace ZInQ.RationalGuards

theorem rational_pos_iff_four_squares_inverse (x : ℚ) :
    0 < x ↔ ∃ s : Fin 4 → ℚ, x * ∑ i, s i ^ 2 = 1 := by
  constructor
  · intro hx
    -- The reciprocal `x⁻¹` is a positive rational, so its numerator is positive.
    have hy : 0 < x⁻¹ := inv_pos.mpr hx
    have hnum : 0 < (x⁻¹).num := Rat.num_pos.mpr hy
    -- Lagrange's four-square theorem for the natural number `num * den`.
    obtain ⟨a, b, c, d, habcd⟩ :=
      Nat.sum_four_squares ((x⁻¹).num.toNat * (x⁻¹).den)
    have hden : ((x⁻¹).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (x⁻¹).den_nz
    have hnumcast : (((x⁻¹).num.toNat : ℕ) : ℚ) = ((x⁻¹).num : ℚ) := by
      have h := Int.toNat_of_nonneg hnum.le
      exact_mod_cast h
    have hsq : (a : ℚ) ^ 2 + (b : ℚ) ^ 2 + (c : ℚ) ^ 2 + (d : ℚ) ^ 2
        = ((x⁻¹).num : ℚ) * ((x⁻¹).den : ℚ) := by
      rw [← hnumcast]
      exact_mod_cast habcd
    refine ⟨![(a : ℚ) / (x⁻¹).den, (b : ℚ) / (x⁻¹).den, (c : ℚ) / (x⁻¹).den,
      (d : ℚ) / (x⁻¹).den], ?_⟩
    rw [Fin.sum_univ_four]
    show x * (((a : ℚ) / (x⁻¹).den) ^ 2 + ((b : ℚ) / (x⁻¹).den) ^ 2
      + ((c : ℚ) / (x⁻¹).den) ^ 2 + ((d : ℚ) / (x⁻¹).den) ^ 2) = 1
    have h1 : ((a : ℚ) / (x⁻¹).den) ^ 2 + ((b : ℚ) / (x⁻¹).den) ^ 2
        + ((c : ℚ) / (x⁻¹).den) ^ 2 + ((d : ℚ) / (x⁻¹).den) ^ 2
        = ((a : ℚ) ^ 2 + (b : ℚ) ^ 2 + (c : ℚ) ^ 2 + (d : ℚ) ^ 2)
          / (((x⁻¹).den : ℚ) * ((x⁻¹).den : ℚ)) := by
      ring
    rw [h1, hsq, mul_div_mul_right _ _ hden, Rat.num_div_den, mul_inv_cancel₀ hx.ne']
  · rintro ⟨s, hs⟩
    -- A sum of squares is nonnegative, so `x ≤ 0` would force `x * ∑ ≤ 0 < 1`.
    have hS : 0 ≤ ∑ i, s i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (s i))
    by_contra hneg
    have hx : x ≤ 0 := not_lt.mp hneg
    have hprod : x * ∑ i, s i ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx hS
    rw [hs] at hprod
    exact absurd hprod (by norm_num)

end ZInQ.RationalGuards
