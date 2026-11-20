import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.ModularForms.Cusps

/-!
# The cuspidal subgroup in Elkik's theorem

Only the algebraic conclusion used at `diophantine_zq.tex` 2937–2942 is recorded here.
-/

namespace ZInQ.Manuscript.RC.ElkikMD

/-- **Printed-form leaf, GLUE (unread in this lane).** R. Elkik, *Le théorème de
Manin–Drinfeld*, Astérisque 183 (1990), Théorème, p. 59 (locator from tex 11158–11160;
exact wording and hypotheses UNVERIFIED against the page). The existing transcript in
`RC/PrintsArith/Heegner.lean` gives torsion of degree-zero divisors supported on the cusps of
`X_Γ` for a congruence subgroup `Γ`. Here `Γ = Γ₀(N)`, `N > 0`: the classes of degree-zero
cuspidal divisors generate a finite subgroup of `J₀(N)(ℚ̄)` (the form used in the manuscript).

`J` stands for `J₀(N)(ℚ̄)` and `cuspClass r` stands for `[c(r)] − [∞]`, with `c(r)` the cusp
of `X₀(N)` represented by `r ∈ ℙ¹(ℚ)`. Taking all rational representatives is redundant and
gives the same subgroup. These are parameters for the geometric objects; this proposition
is not quantified over arbitrary Jacobians or arbitrary class maps as a theorem. It contains
no comparison with path integrals, periods, or central values. -/
def ManinDrinfeld (N : ℕ) [NeZero N] {J : Type*} [AddCommGroup J]
    (cuspClass : OnePoint ℚ → J) : Prop :=
  Finite (AddSubgroup.closure (Set.range cuspClass))

/-- A positive integer kills the image of every cusp class in any additive quotient.
This is the finite-group deduction at tex 2941–2942. -/
theorem cuspidalImage_annihilator {N : ℕ} [NeZero N] {J A : Type*}
    [AddCommGroup J] [AddCommGroup A] {cuspClass : OnePoint ℚ → J}
    (h : ManinDrinfeld N cuspClass) (φ : J →+ A) :
    ∃ m : ℕ, 0 < m ∧ ∀ r, m • φ (cuspClass r) = 0 := by
  let C := AddSubgroup.closure (Set.range cuspClass)
  let : Finite C := h
  refine ⟨Nat.card C, Nat.card_pos, fun r => ?_⟩
  let x : C := ⟨cuspClass r, AddSubgroup.subset_closure (Set.mem_range_self r)⟩
  change Nat.card C • φ (C.subtype x) = 0
  simpa only [map_nsmul, map_zero, AddMonoidHom.comp_apply] using
    congrArg (φ.comp C.subtype) (card_nsmul_eq_zero' (x := x))


end ZInQ.Manuscript.RC.ElkikMD
