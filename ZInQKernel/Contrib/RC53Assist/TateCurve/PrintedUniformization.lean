import ZInQKernel.Contrib.RC53Assist.TateCurve.KummerUniformization

/-!
# Tate's uniformization theorem in its printed form

The manuscript bibitem `silverman` is J. H. Silverman, *The Arithmetic of
Elliptic Curves*, second edition, Springer, 2009. The locator is Appendix C,
§14, Theorem C.14.1 (Tate). The page and theorem body have not been checked;
this is a mathematical transcription, not a checked verbatim quotation.

For `0 < |q| < 1`, the Tate equation is
`y² + xy = x³ - 5 s₃(q) x - (5 s₃(q) + 7 s₅(q))/12`, where
`s_k(q) = ∑_{n≥1} n^k q^n/(1-q^n)`. Tate's theorem supplies a
Galois-equivariant multiplicative uniformization with kernel `q^ℤ`.
For an elliptic curve with `|j| > 1`, the admissible parameter with its
`j`-invariant is unique. The curve is isomorphic to the Tate curve over the
base field exactly in the split multiplicative case. The quadratic descent
character, its ramification, and the Tate-module columns are derived in
separate proofs and are not clauses of this print.

The qualification on the extension matters. For multiplicative reduction the
non-split splitting extension is unramified quadratic. For additive
potentially multiplicative reduction it is ramified quadratic. The blanket
claim that every curve with `|j| > 1` splits over the unramified quadratic
extension is not included here. Neither a Tate-module basis nor a Kummer
cocycle nor any inertia reading is a clause of the print below.
-/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.TateCurve

open Module
open scoped Classical WithZero

section TateEquation

variable {K : Type*} [Field K] [TopologicalSpace K]

/-- **DEFINITION**: the coefficient series in the Tate equation.
Locator: Silverman, Appendix C, §14; page not checked. -/
def tateCoefficientSeries (k : ℕ) (q : K) : K :=
  ∑' n : ℕ, ((n + 1 : K) ^ k * q ^ (n + 1)) / (1 - q ^ (n + 1))

/-- **DEFINITION**: the Tate Weierstrass equation attached to a parameter.
Locator: Silverman, Appendix C, §14; page not checked. Convergence and
ellipticity are not asserted for inadmissible parameters. -/
def tateEquation (q : Kˣ) : WeierstrassCurve K :=
  ⟨1, 0, 0, -5 * tateCoefficientSeries 3 (q : K),
    -(5 * tateCoefficientSeries 3 (q : K) + 7 * tateCoefficientSeries 5 (q : K)) / 12⟩

end TateEquation

section LocalField

variable {K : Type*} [Field K] [CharZero K] [Valued K ℤᵐ⁰]

/-- **DEFINITION**: the parameter in the algebraic closure.
Locator: extension of scalars on the multiplicative group. -/
def closureParameter (q : Kˣ) : (AlgebraicClosure K)ˣ :=
  Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom q

/-- **DEFINITION**: pointwise Galois equivariance of Tate uniformization.
Locator: the equivariance clause of Tate's theorem, C.14.1. -/
structure EquivariantTateUniformization (q : Kˣ) where
  uniformization : MultiplicativeUniformization
    (P := ((tateEquation q).baseChange (AlgebraicClosure K)).toAffine.Point)
    (closureParameter q)
  equivariant : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : (AlgebraicClosure K)ˣ),
    WeierstrassCurve.Affine.Point.map (W' := tateEquation q) σ.toAlgHom
        (uniformization.map (Additive.ofMul x)) =
      uniformization.map (Additive.ofMul (Units.map σ.toAlgHom.toMonoidHom x))

/-- **GLUE (a reading of a printed theorem)**: Tate's theorem, in uniformization, unique-parameter,
and splitting form; not certified as a literal page-checked statement. Locator: Silverman, AEC,
second edition, Appendix C, §14, Theorem C.14.1. Section-level locator; page and theorem body not
checked. The coefficient equation is the one defined immediately before the theorem. This is a
proposition, not an axiom. No derived Tate-module or inertia assertion is packaged into it. -/
def SilvermanC141TateUniformizationPrint : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [Valued K ℤᵐ⁰] [CompleteSpace K]
    [IsDiscreteValuationRing (Valued.v.valuationSubring : ValuationSubring K)]
    [Finite (IsLocalRing.ResidueField
      (Valued.v.valuationSubring : ValuationSubring K))],
    (∀ q : Kˣ, Valued.v (q : K) < 1 →
      (tateEquation q).IsElliptic ∧ Nonempty (EquivariantTateUniformization q)) ∧
    (∀ (E : WeierstrassCurve K) [E.IsElliptic], 1 < Valued.v E.j →
      ∃! q : Kˣ, ∃ hqE : (tateEquation q).IsElliptic, letI := hqE;
        Valued.v (q : K) < 1 ∧ (tateEquation q).j = E.j ∧
        ((∃ C : WeierstrassCurve.VariableChange K, C • E = tateEquation q) ↔
          WeierstrassCurve.HasSplitMultiplicativeReduction
            (Valued.v.valuationSubring : ValuationSubring K)
            (E.minimal (Valued.v.valuationSubring : ValuationSubring K))))

end LocalField

end ZInQ.Contrib.RC53Assist.TateCurve
