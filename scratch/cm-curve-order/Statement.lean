import ZInQKernel.Contrib.OneProof.CMCurveOrder

namespace HDec.CMBranch.FibreSplit

/-- **Glue (on-the-spot; manuscript L584-586, "an elliptic curve `E/L` with complex multiplication", "the
full geometric endomorphism order of `E`").** Let `A/L` be an abelian surface over a number field with
`End⁰(A_Ω) ≅ M₂(ℚ(√d))`, `d < 0`, and let `E/L` be an elliptic curve with homomorphisms `i : E → A`,
`h : A → E`, `h ∘ i = [n]`, `n ≥ 1` (an isogeny factor of `A`, e.g. the image of `n e₁₁`). Then the geometric
endomorphism ring of `E` is an order `R` of an imaginary quadratic field `k`. *Sketch:* `g ↦ i g h` embeds
`End⁰(E_Ω)` as the corner `e End⁰(A_Ω) e`, `e = (1/n) i h` a nonzero idempotent which is not `1` (`dim E = 1
< 2`), so of rank one in `M₂(k)`, whose corner is `k`; `End(E)` is a finitely generated subring, an order;
`End(E_{L̄}) ≅ End(E_Ω)` because both are algebraic closures of `L` (rigidity). -/
def PinnedStatement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A : PkgI3.AbVar L)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra L Ω] [Algebra.IsAlgebraic L Ω] (d : ℚ), d < 0 →
    Nonempty (PkgI3.AbVar.End0 (A.baseChange Ω) ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (Kd d)) →
    ∀ (E : ZInQ.DefFaltings.AbVar L), E.dim = 1 →
    ∀ (i : PkgI3.AbVar.Hom E A) (h : PkgI3.AbVar.Hom A E) (n : ℕ), 0 < n →
      cmp i h = (n : PkgI3.AbVar.End E) →
      ∃ (k : Type) (_ : Field k) (_ : NumberField k) (R : Subring k),
        IsImagQuadOrder k R ∧ IsCMBy E k R

example : PinnedStatement ↔ CMCurveOrder324 := Iff.rfl

example (hHF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC) : PinnedStatement :=
  cmCurveOrder324_of hHF

end HDec.CMBranch.FibreSplit
