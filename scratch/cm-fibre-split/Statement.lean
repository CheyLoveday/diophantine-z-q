import ZInQKernel.Contrib.OneProof.CMFibreSplit

/-! cm-fibre-split: verbatim copy of `HDec.CMBranch.CMFibreSplit` (ZInQKernel/Contrib/OneProof/CMBranch.lean) and the
check that the deliverable proves exactly it. -/

namespace HDec
namespace CMBranch
namespace FibreSplitCheck

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight HDec.LeafQM.AV HDec.ZInQ.DefFaltings
open HSyn HSyn.G0Split
open _root_.CMBranch

/-- **Glue (manuscript A8, L520-562, for a CM fibre, and L583-586).** If some point over `J(u)` has
CM, the fibre surface has a model `A` over a number field `L` with `[L:ℚ] ≤ D` over which every
geometric endomorphism is defined (A8; its proof does not use the case split), and the matrix units of
`End⁰(A) = M₂(k)` give an elliptic curve `E/L` with `End(E_{L̄})` an order `R` of `k`, the product
`E² = E × E` and an `L`-isogeny `E² → A`. -/
def CMFibreSplitCopy : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet → ¬ NoCMAt Y Φ π u →
    ∃ (L : GlueAssembly.NF) (A E Pr : ZInQ.DefFaltings.AbVar L.K) (k : Type) (_ : Field k)
      (_ : NumberField k) (R : Subring k),
      FibreOver Y Φ π u L A ∧ Module.finrank ℚ L.K ≤ heightD ∧ E.dim = 1 ∧
      Pr.dim = (2 : ℕ) ∧ IsProductOf Pr.X E.X E.X ∧ (∃ φ : Pr.X ⟶ A.X, IsIsogeny φ) ∧
      IsImagQuadOrder k R ∧ IsCMBy E k R


example : CMFibreSplitCopy ↔ CMBranch.CMFibreSplit := Iff.rfl

example (hYu : QMLattice.YuB6Alg) (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hCover : G0ModField.FibreCoverExists) (hNOS : PkgI2.NeronOggShafarevich.{0})
    (hRay : PkgI2.RaynaudCriterionNF.{0}) (hTors : PkgI2.TorsionStructure.{0}) : CMFibreSplitCopy :=
  FibreSplit.cmFibreSplit_of_leaves hYu hHFF hCover hNOS hRay hTors

end FibreSplitCheck
end CMBranch
end HDec
