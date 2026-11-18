import ZInQKernel.Contrib.OneProof.CMCurveOrder

namespace HDec.CMBranch.FibreSplit

/-- Original CM order glue at 324f0655a, copied verbatim; manuscript `thm:height` L582–586. -/
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

#print axioms HDec.CMBranch.FibreSplit.cmCurveOrder324_of
#print axioms HDec.CMBranch.FibreSplit.cmFibreSplit_of_curveOrder324
