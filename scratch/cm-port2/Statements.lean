import ZInQKernel.Contrib.OneProof.CMCurveOrder.R6U

/-! Verbatim Prop bodies and definitional equality to the three unchanged contracts. -/

namespace HDec.CMBranch.FibreSplit.Port2Statement

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight HDec.LeafQM.AV HDec.ZInQ.DefFaltings
open HSyn HSyn.G0Split
open _root_.CMBranch
open scoped Quaternion TensorProduct

def CMFibreSplit : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet → ¬ NoCMAt Y Φ π u →
    ∃ (L : GlueAssembly.NF) (A E Pr : ZInQ.DefFaltings.AbVar L.K) (k : Type) (_ : Field k)
      (_ : NumberField k) (R : Subring k),
      FibreOver Y Φ π u L A ∧ Module.finrank ℚ L.K ≤ heightD ∧ E.dim = 1 ∧
      Pr.dim = (2 : ℕ) ∧ IsProductOf Pr.X E.X E.X ∧ (∃ φ : Pr.X ⟶ A.X, IsIsogeny φ) ∧
      IsImagQuadOrder k R ∧ IsCMBy E k R

def CMHomFieldModel : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 LeafQM.AV.Qbar), G0ModField.FibreCtx Y Φ π u P →
    ∃ (L : G0ModField.IF) (_ : FiniteDimensional ℚ L), Module.finrank ℚ L ≤ heightD ∧
      ∃ (A : PkgI3.AbVar L) (θ : PkgI3.AbVar.Hom (A.baseChange LeafQM.AV.Qbar) P.A)
        (θ' : PkgI3.AbVar.Hom P.A (A.baseChange LeafQM.AV.Qbar)),
        θ.hom ≫ θ'.hom = 𝟙 _ ∧ θ'.hom ≫ θ.hom = 𝟙 _ ∧
        Function.Surjective (G0ModField.KernelField.endBC A LeafQM.AV.Qbar)

def CMCurveOrder324 : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A : PkgI3.AbVar L)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra L Ω] [Algebra.IsAlgebraic L Ω] (d : ℚ), d < 0 →
    Nonempty (PkgI3.AbVar.End0 (A.baseChange Ω) ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (Kd d)) →
    ∀ (E : ZInQ.DefFaltings.AbVar L), E.dim = 1 →
    ∀ (i : PkgI3.AbVar.Hom E A) (h : PkgI3.AbVar.Hom A E) (n : ℕ), 0 < n →
      cmp i h = (n : PkgI3.AbVar.End E) →
      ∃ (k : Type) (_ : Field k) (_ : NumberField k) (R : Subring k),
        IsImagQuadOrder k R ∧ IsCMBy E k R

example : CMFibreSplit ↔ HDec.CMBranch.CMFibreSplit := Iff.rfl
example : CMHomFieldModel ↔ FibreSplit.CMHomFieldModel := Iff.rfl
example : CMCurveOrder324 ↔ FibreSplit.CMCurveOrder324 := Iff.rfl

#print axioms HDec.CMBranch.FibreSplit.cmHomFieldModel_of_R6U
#print axioms HDec.CMBranch.FibreSplit.cmCurveOrder324_of
#print axioms HDec.CMBranch.FibreSplit.cmMatrixUnitSplit_of
#print axioms HDec.CMBranch.FibreSplit.cmFibreSplit_of_curveOrder324_R6U

end HDec.CMBranch.FibreSplit.Port2Statement
