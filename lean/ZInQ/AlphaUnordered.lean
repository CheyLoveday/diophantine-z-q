/- Copyright (c) 2026. -/
module

public import ZInQ.AlphaCore

/-!
Unordered nonnegative solutions of the alpha quadratic equation.
This is the literal AFP `alpha_char_eq2` helper.
-/

public section

namespace ZInQ.AlphaPower

/-- Each coordinate of a nonnegative quadratic solution is an alpha value. -/
theorem exists_eq_alphaZ_of_quadratic (B x y : Nat) (hB : 2 < B)
    (hEq : x * x + y * y = 1 + B * x * y) :
    ∃ n : Nat, (x : Int) = alphaZ B n := by
  have hne : x ≠ y := by
    intro hxy
    subst y
    have hmul : 2 * (x * x) ≤ B * (x * x) :=
      Nat.mul_le_mul_right (x * x) (Nat.le_of_lt hB)
    nlinarith only [hEq, hmul]
  by_cases hlt : x < y
  · have hordered : 1 + B * y * x = y * y + x * x := by
      nlinarith only [hEq]
    obtain ⟨n, hx, _⟩ := alphaZ_descent B x y hlt hordered
    exact ⟨n, hx⟩
  · have hgt : y < x := by omega
    obtain ⟨n, _, hx⟩ := alphaZ_descent B y x hgt hEq.symm
    exact ⟨n + 1, hx⟩

end ZInQ.AlphaPower
