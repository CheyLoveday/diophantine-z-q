import Mathlib
import ZInQKernel.Hypotheses.Pole

/-!
# Manuscript names and the restricted-converse schema

The manuscript pole names are abbreviations of the active kernel definitions:
there is one polynomial and one completeness predicate. The restricted converse
below is retained as a statement schema only; the headline takes PC directly.
-/

namespace ZInQ.Manuscript

/-- The active manuscript polynomial. -/
abbrev polePoly := ZInQ.polePoly

/-- The active manuscript solubility predicate. -/
abbrev PoleSoluble := ZInQ.PoleSoluble

/-- Theorem 5.2, the explicit pole-completeness hypothesis. -/
abbrev PoleCompleteness := ZInQ.PoleCompleteness

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
