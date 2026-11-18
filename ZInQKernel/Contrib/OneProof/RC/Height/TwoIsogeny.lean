import ZInQKernel.Contrib.OneProof.RC.Height.Transfer
import ZInQKernel.Contrib.OneProof.RC.Height.FieldVelu
import ZInQKernel.Hypotheses.PoleManuscript

/-!
# Lane RC19 (height): functoriality for the 2-isogenies of `y² = x(x² + a x + b)`

For the curve `E : y² = x(x² + a x + b)` (`b ≠ 0`) the 2-isogeny with kernel `{O, (0, 0)}` onto
`E' : Y² = X(X² − 2aX + a² − 4b)` is `(x, y) ↦ (y²/x², y(b − x²)/x²)` (Silverman, *The Arithmetic
of Elliptic Curves*, 2nd ed., Chapter III, §4; textbook reference, locator UNVERIFIED); its
`x`-coordinate is
`X = y²/x² = (x² + a x + b)/x`, a rational map of degree two.

The curve of Theorem 5.3, `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)` (`ZInQ.Manuscript.curve ℓ`), is of this form
with `a = 2ℓ`, `b = −3ℓ²`; its other two rational 2-isogenies are obtained after the translation
`x ↦ x + ℓ` or `x ↦ x − 3ℓ`, which preserves heights (`canonicalHeight_addEquivVariableChange`).

This file proves `ĥ_{E'}(φ P) = 2 ĥ_E(P)` (functoriality in degree two) for **any** additive map `φ`
whose `x`-coordinate is the Vélu map above; the naïve-height estimate
`|h((x² + a x + b)/x) − 2 h(x)| ≤ C` is `abs_logHeight₁_velu_sub_le'` (`FieldVelu.lean`). The
construction of the 2-isogeny as an additive map on points is the textbook formula and is not
redone here (the statement takes `φ` as data; it is used nowhere in the steps of this lane's tex
lines, see the report).

Every declaration in this file is PROVED.

* `canonicalHeight_velu`: `ĥ(φ P) = 2 ĥ(P)`.
* `neronTatePairing_velu`: `⟨φ P, φ Q⟩ = 2 ⟨P, Q⟩`.
* `canonicalHeight_velu_curve`: the case of `E_ℓ`, `a = 2ℓ`, `b = −3ℓ²`.
-/

open Height

namespace ZInQ.Manuscript.RC.Height

open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] [AdmissibleAbsValues F] [DecidableEq F]
  {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **Functoriality of the canonical height for a 2-isogeny with kernel `{O, (0,0)}`**: if the
additive map `φ` sends an affine point `(x, y)` with `x ≠ 0` to a point with `x`-coordinate
`(x² + a x + b)/x` and kills the points with `x = 0`, then `ĥ(φ P) = 2 ĥ(P)` (`b ≠ 0`). PROVED. -/
theorem canonicalHeight_velu (a b : F) (hb : b ≠ 0)
    (φ : W₁.toAffine.Point →+ W₂.toAffine.Point)
    (hφ : ∀ (x y : F) (h : W₁.toAffine.Nonsingular x y), x ≠ 0 →
      (φ (Point.some x y h)).xRep = ![(x ^ 2 + a * x + b) / x, 1])
    (hφ0 : ∀ (y : F) (h : W₁.toAffine.Nonsingular 0 y), φ (Point.some 0 y h) = 0)
    (P : W₁.toAffine.Point) :
    (φ P).canonicalHeight = 2 * P.canonicalHeight := by
  obtain ⟨C, hC⟩ := abs_logHeight₁_velu_sub_le' a b hb
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine canonicalHeight_map_eq_of_abs_naiveHeight_sub_le φ 2 C (fun Q => ?_) P
  rcases Q with _ | ⟨x, y, h⟩
  · simpa [← Point.zero_def] using hC0
  · by_cases hx : x = 0
    · subst hx
      rw [hφ0 y h, Point.naiveHeight_zero, naiveHeight_some, logHeight₁_zero, mul_zero,
        sub_zero, abs_zero]
      exact hC0
    · rw [Point.naiveHeight_eq_logHeight, hφ x y h hx, naiveHeight_some,
        ← logHeight₁_eq_logHeight]
      exact hC x

/-- **The polarized form**: `⟨φ P, φ Q⟩ = 2 ⟨P, Q⟩`. PROVED. -/
theorem neronTatePairing_velu (a b : F) (hb : b ≠ 0)
    (φ : W₁.toAffine.Point →+ W₂.toAffine.Point)
    (hφ : ∀ (x y : F) (h : W₁.toAffine.Nonsingular x y), x ≠ 0 →
      (φ (Point.some x y h)).xRep = ![(x ^ 2 + a * x + b) / x, 1])
    (hφ0 : ∀ (y : F) (h : W₁.toAffine.Nonsingular 0 y), φ (Point.some 0 y h) = 0)
    (P Q : W₁.toAffine.Point) :
    W₂.toAffine.neronTatePairing (φ P) (φ Q) = 2 * W₁.toAffine.neronTatePairing P Q :=
  neronTatePairing_map_eq_of_canonicalHeight φ 2 (canonicalHeight_velu a b hb φ hφ hφ0) P Q

/-- **The case of `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)`** (`a = 2ℓ`, `b = −3ℓ²`, `ℓ ≠ 0`): any additive map
of rational points onto an elliptic curve with the Vélu `x`-coordinate doubles canonical heights.
PROVED. -/
theorem canonicalHeight_velu_curve (ℓ : ℚ) (hℓ : ℓ ≠ 0) [(ZInQ.Manuscript.curve ℓ).IsElliptic]
    {W₂ : WeierstrassCurve ℚ} [W₂.IsElliptic]
    (φ : (ZInQ.Manuscript.curve ℓ).toAffine.Point →+ W₂.toAffine.Point)
    (hφ : ∀ (x y : ℚ) (h : (ZInQ.Manuscript.curve ℓ).toAffine.Nonsingular x y), x ≠ 0 →
      (φ (Point.some x y h)).xRep = ![(x ^ 2 + 2 * ℓ * x + (-3 * ℓ ^ 2)) / x, 1])
    (hφ0 : ∀ (y : ℚ) (h : (ZInQ.Manuscript.curve ℓ).toAffine.Nonsingular 0 y),
      φ (Point.some 0 y h) = 0)
    (P : (ZInQ.Manuscript.curve ℓ).toAffine.Point) :
    (φ P).canonicalHeight = 2 * P.canonicalHeight :=
  canonicalHeight_velu (2 * ℓ) (-3 * ℓ ^ 2) (by simpa using hℓ) φ hφ hφ0 P

end ZInQ.Manuscript.RC.Height
