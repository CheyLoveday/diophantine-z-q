import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.ZMod.Basic

namespace CCLUnitIndexCheck

/-- Modulo eight excludes -3, but does not exclude -4. -/
theorem neg_four_square_mod_eight : (2 : ZMod 8) ^ 2 = -4 := by decide

/-- Squares modulo sixteen cannot represent either exceptional fundamental discriminant. -/
theorem square_mod_sixteen (b : ZMod 16) : b ^ 2 ≠ -3 ∧ b ^ 2 ≠ -4 := by decide +revert

/-- The Heegner form congruence excludes the exceptional fields at a level divisible by four. -/
theorem exceptional_disc_of_level {N : ℕ} {A B C : ℤ}
    (hN : 4 ∣ N) (hA : (N : ℤ) ∣ A) :
    B ^ 2 - 4 * A * C ≠ -3 ∧ B ^ 2 - 4 * A * C ≠ -4 := by
  have hA4 : (4 : ℤ) ∣ A :=
    (Int.natCast_dvd.mpr hN : ((4 : ℕ) : ℤ) ∣ (N : ℤ)).trans hA
  obtain ⟨k, rfl⟩ := hA4
  have hmod := square_mod_sixteen (B : ZMod 16)
  have h16 : (4 : ZMod 16) * 4 = 0 := by decide
  constructor
  · intro h
    apply hmod.1
    have hc := congrArg (fun x : ℤ => (x : ZMod 16)) h
    push_cast at hc
    simpa only [← mul_assoc, h16, zero_mul, sub_zero] using hc
  · intro h
    apply hmod.2
    have hc := congrArg (fun x : ℤ => (x : ZMod 16)) h
    push_cast at hc
    simpa only [← mul_assoc, h16, zero_mul, sub_zero] using hc

/-- The prime divisor already present at each stage gives the desired lower bound. -/
theorem chain_conductor_gt_one {r f d di : ℕ} (hr : r.Prime)
    (hrf : r ∣ f) (hfd : f ∣ d) (hdi : d ∣ di) (hi : 0 < di) : 1 < di :=
  hr.one_lt.trans_le (Nat.le_of_dvd hi (hrf.trans (hfd.trans hdi)))

/-- The integer premises of admissibility and the Heegner form can hold at conductor one even with
exceptional discriminant. The prime 5 splits in the field of discriminant -4. -/
theorem exceptional_admissible_example :
    0 < (1 : ℕ) ∧ Nat.Coprime 1 (2 * 37 * 4) ∧ Nat.Prime 5 ∧ ¬ 5 ∣ 6 * 1 * 37 * 4 ∧
    jacobiSym (-4) 5 = 1 ∧ 0 < (37 : ℤ) ∧ (37 : ℤ) ∣ 37 ∧
    (12 : ℤ) ^ 2 - 4 * 37 * 1 = -4 ∧ Int.gcd (Int.gcd 37 12) 1 = 1 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, by decide, by decide,
    by decide, by decide⟩
  exact (jacobiSym.mod_left' (a₁ := -4) (a₂ := 1) (b := 5) (by decide)).trans
    (jacobiSym.one_left 5)

/-- A weighted equality of sums does not algebraically imply the unweighted equality. -/
theorem weighted_does_not_cancel : ∃ x y : ℤ, 2 • x = y ∧ x ≠ y :=
  ⟨1, 2, by decide, by decide⟩

end CCLUnitIndexCheck

#print axioms CCLUnitIndexCheck.neg_four_square_mod_eight
#print axioms CCLUnitIndexCheck.square_mod_sixteen
#print axioms CCLUnitIndexCheck.exceptional_disc_of_level
#print axioms CCLUnitIndexCheck.chain_conductor_gt_one
#print axioms CCLUnitIndexCheck.exceptional_admissible_example
#print axioms CCLUnitIndexCheck.weighted_does_not_cancel
