import Mathlib
import ZInQKernel.Hypotheses.Pole

/-!
# The manuscript's pole predicate: Theorem 5.2 and Theorem 5.3 as statements

Target statements for the lane of fork issue #74: the 11/5 manuscript's own pole polynomial
(`diophantine_zq.tex`, lines 973–1011), in place of the Route K polynomial of
`ZInQKernel/Hypotheses/Pole.lean`.

This file only states. Nothing here is used by the main theorem yet, nothing is assumed, and no
existing declaration is changed.

* `Manuscript.polePoly`, `Manuscript.PoleSoluble`: the manuscript's `Q_pole` and `Φ`, with the
  curves `y² = x(x - ℓ)(x + 3ℓ)`. They differ from `ZInQ.polePoly` only in the factors `A + 3e`
  and `Az² + 3eH`, where Route K has `A + e` and `Az² + eH`.
* `Manuscript.PoleCompleteness`: **Theorem 5.2** (`hyp:PC`). This is the input PC of the
  manuscript's assembly (Lemma 1.2), and the hypothesis the manuscript-faithful headline is to
  take.
* `Manuscript.curve`, `Manuscript.AnalyticRankOne`, `Manuscript.RestrictedConverse`:
  **Theorem 5.3** (`hyp:RC`), the restricted converse from which the manuscript proves
  Theorem 5.2. Its Selmer condition is a parameter here, because this repository has no
  definition of the `2`-power Selmer group of an elliptic curve; see `RestrictedConverse`.
-/

namespace ZInQ.Manuscript

open scoped BigOperators

/-- The manuscript's pole polynomial `Q_pole` (Section 5, lines 979–986), evaluated at the input
`B` and its eleven witnesses `b₀, …, b₅, e, z, r₁, r₂, w`:
`T₁ = A(A - e)(A + 3e)` and `T₂ = A(Az² - eH)(Az² + 3eH)`, so that `(A, r₁)` lies on
`E_e` and `(Az², zr₂)` on `E_{eH}`, where `E_ℓ : y² = x(x - ℓ)(x + 3ℓ)`. -/
def polePoly (B : ℚ) (b : Fin 6 → ℚ) (e z r₁ r₂ w : ℚ) : ℚ :=
  let m := (1 - 2 * b 0) * (1 + b 1) * (1 + 2 * b 2) * (1 + 4 * b 3) * (1 + 6 * b 4) *
    (1 + 12 * b 5)
  let A := m * B
  let H := A * (A - B ^ 2)
  let T₁ := A * (A - e) * (A + 3 * e)
  let T₂ := A * (A * z ^ 2 - e * H) * (A * z ^ 2 + 3 * e * H)
  B * ((∑ i, (b i ^ 2 - b i) ^ 2) + (e * H * z * w - 1) ^ 2 + (r₁ ^ 2 - T₁) ^ 2 +
    (r₂ ^ 2 - T₂) ^ 2)

/-- The manuscript's `Φ(B)`: its pole polynomial has a rational zero with input `B`. -/
def PoleSoluble (B : ℚ) : Prop :=
  ∃ (b : Fin 6 → ℚ) (e z r₁ r₂ w : ℚ), polePoly B b e z r₁ r₂ w = 0

/-- **Theorem 5.2 of the 11/5 manuscript (pole completeness, `hyp:PC`), for the manuscript's
polynomial.** Every rational `B` with square reduced denominator, `0 < B < 1/2` and
`v_p(B) ≥ 4` for every `p ∈ S₀ = {2, 3, 5, 7, 13}` satisfies `Φ(B)`.

The statement has the same shape as `ZInQ.PoleCompleteness`; only the polynomial differs. -/
def PoleCompleteness : Prop :=
  ∀ B : ℚ, IsSquare B.den → 0 < B → B < 1 / 2 → (∀ p ∈ poleS0, 4 ≤ padicValRat p B) →
    PoleSoluble B

/-- The manuscript's curve `E_ℓ : y² = x(x - ℓ)(x + 3ℓ) = x³ + 2ℓx² - 3ℓ²x`. -/
def curve (ℓ : ℚ) : WeierstrassCurve ℚ := ⟨0, 2 * ℓ, 0, -3 * ℓ ^ 2, 0⟩

/-- `c₄(E_ℓ) = 208ℓ²`, as the manuscript states after Theorem 5.3. -/
theorem curve_c₄ (ℓ : ℚ) : (curve ℓ).c₄ = 208 * ℓ ^ 2 := by
  simp only [curve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]; ring

/-- `Δ(E_ℓ) = 2304ℓ⁶`, as the manuscript states after Theorem 5.3. -/
theorem curve_Δ (ℓ : ℚ) : (curve ℓ).Δ = 2304 * ℓ ^ 6 := by
  simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]; ring

/-- `ord_{s=1} L(E, s) = 1`: some entire function agrees with Mathlib's L-series of `E` on
`Re s > 3/2` and vanishes to order exactly one at `s = 1`. This is the convention of
`ZInQKernel/Hypotheses/CR3Literature.lean` (`IsLContinuation` with `analyticOrderAt`), written
out so that this file needs only Mathlib. -/
def AnalyticRankOne (E : WeierstrassCurve ℚ) : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) ∧
    analyticOrderAt F 1 = 1

/-- **Theorem 5.3 of the 11/5 manuscript (restricted converse, `hyp:RC`), with its Selmer
condition as a parameter.** For every positive squarefree `ℓ ≡ 11 (mod 12)`,
`corank_{ℤ₂} Sel_{2^∞}(E_ℓ/ℚ) = 1` implies `ord_{s=1} L(E_ℓ, s) = 1`.

**This is a statement schema, not yet the theorem.** `SelmerCorankOne E` stands for
`corank_{ℤ₂} Sel_{2^∞}(E/ℚ) = 1`. The repository has no definition of the `2`-power Selmer group
of an elliptic curve over `ℚ` (Route K's `Sel₂` is the explicit `2`-Selmer system of the
congruent number curves, a different object), so the condition cannot be written over a genuine
definition today. `RestrictedConverse P` is Theorem 5.3 only for that one predicate `P`; it must
not be taken as a hypothesis at any other instance. The lane of issue #74 does not use it: the
headline takes `PoleCompleteness`. -/
def RestrictedConverse (SelmerCorankOne : WeierstrassCurve ℚ → Prop) : Prop :=
  ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 →
    SelmerCorankOne (curve ℓ) → AnalyticRankOne (curve ℓ)

end ZInQ.Manuscript
