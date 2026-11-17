import Mathlib

/-!
# Manuscript pole completeness (PC)

Theorem 5.2 (`hyp:PC`) of the 11/5 manuscript, for the curves
`y² = x(x - ℓ)(x + 3ℓ)`. PC is an explicit hypothesis of the current headline.
The manuscript derives it from its restricted converse (Theorem 5.3); that
argument is not formalized here. Route K used a different polynomial and is
retired from the active build (fork issue #74).
-/

namespace ZInQ

open scoped BigOperators

/-- The exceptional primes `S₀ = {2, 3, 5, 7, 13}` of the pole predicate. -/
def poleS0 : Finset ℕ := {2, 3, 5, 7, 13}

/-- The manuscript's `Q_pole`, with input `B` and eleven witnesses
`b₀, …, b₅, e, z, r₁, r₂, w`. The curve factors are `A + 3e` and `Az² + 3eH`. -/
def polePoly (B : ℚ) (b : Fin 6 → ℚ) (e z r₁ r₂ w : ℚ) : ℚ :=
  let m := (1 - 2 * b 0) * (1 + b 1) * (1 + 2 * b 2) * (1 + 4 * b 3) * (1 + 6 * b 4) *
    (1 + 12 * b 5)
  let A := m * B
  let H := A * (A - B ^ 2)
  let T₁ := A * (A - e) * (A + 3 * e)
  let T₂ := A * (A * z ^ 2 - e * H) * (A * z ^ 2 + 3 * e * H)
  B * ((∑ i, (b i ^ 2 - b i) ^ 2) + (e * H * z * w - 1) ^ 2 + (r₁ ^ 2 - T₁) ^ 2 +
    (r₂ ^ 2 - T₂) ^ 2)

/-- `Φ(B)`: the manuscript's pole polynomial has a rational zero with input `B`. -/
def PoleSoluble (B : ℚ) : Prop :=
  ∃ (b : Fin 6 → ℚ) (e z r₁ r₂ w : ℚ), polePoly B b e z r₁ r₂ w = 0

/-- **PC (Theorem 5.2).** For square reduced denominator, `0 < B < 1/2` and
`v_p(B) ≥ 4` at every `p ∈ S₀`, the manuscript's `Φ(B)` holds.
This is the manuscript's own unrefereed claim, retained as a hypothesis. -/
def PoleCompleteness : Prop :=
  ∀ B : ℚ, IsSquare B.den → 0 < B → B < 1 / 2 → (∀ p ∈ poleS0, 4 ≤ padicValRat p B) →
    PoleSoluble B

end ZInQ
