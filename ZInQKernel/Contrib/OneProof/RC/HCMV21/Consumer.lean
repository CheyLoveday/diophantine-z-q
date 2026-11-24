import ZInQKernel.Contrib.OneProof.RC.HCMV21.Correspondence
import ZInQKernel.Contrib.OneProof.RC.PMGeometry.Heegner

/-! Pointwise replacement for the use of the preprint in the comparison at
tex 9265–9295. The parametrization square stays an independent input. -/

namespace ZInQ.Manuscript.RC.HCMV21

open Eichler PMGeometry
open scoped WeierstrassCurve

/-- Forget the labels after computing the class on the oriented target. The
chosen reference is one actual reduction; the dictionary for the target
orbit deals only with the already constructed supersingular points. -/
noncomputable def inputsAtDatum_of_orientedCorrespondence
    {a b : ℚ} {R : Order a b} {ell N : ℕ} [Fact ell.Prime]
    {A : Adelic (ell := ell) (N := N) R}
    {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
    {Ebar : WeierstrassCurve (ZMod ell)} {ap : ℕ → ℤ}
    {Cl X Y T : Type*} [Group Cl] [MulAction Cl X] [MulAction Cl T] [AddCommGroup Y]
    {red : Y →+ PM.ReducedPoints (K := K) Ebar}
    {y : Cl → Y} {z : Cl → ClassSet R}
    (model : GeometricInput A K Ebar ap)
    (reduceLabelled : X → T) (x₀ : X) (z₀ : T) (h₀ : reduceLabelled x₀ = z₀)
    (h : OrientedCorrespondence (C := Cl) reduceLabelled)
    (forgetLabels : T → model.Point)
    (hclass : ∀ c : Cl, forgetLabels (c • z₀) = (model.classes (z c)).val)
    (hπ : ∀ c : Cl, model.specialize (forgetLabels (reduceLabelled (c • x₀))) = red (y c)) :
    InputsAtDatum A ap red y z where
  model := model
  reduceCM c := forgetLabels (reduceLabelled (c • x₀))
  cm_class c := by rw [h.2, h₀, hclass]
  pi_commutes := hπ

/-- The pointwise equality consumed by the detector, using only
equivariance at the chosen orientation and the separate square. -/
theorem point_reduction_of_orientedCorrespondence
    {a b : ℚ} {R : Order a b} {ell N : ℕ} [Fact ell.Prime]
    {A : Adelic (ell := ell) (N := N) R}
    {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
    {Ebar : WeierstrassCurve (ZMod ell)} {ap : ℕ → ℤ}
    {Cl X Y T : Type*} [Group Cl] [MulAction Cl X] [MulAction Cl T] [AddCommGroup Y]
    {red : Y →+ PM.ReducedPoints (K := K) Ebar}
    {y : Cl → Y} {z : Cl → ClassSet R}
    (model : GeometricInput A K Ebar ap)
    (reduceLabelled : X → T) (x₀ : X) (z₀ : T) (h₀ : reduceLabelled x₀ = z₀)
    (h : OrientedCorrespondence (C := Cl) reduceLabelled)
    (forgetLabels : T → model.Point)
    (hclass : ∀ c : Cl, forgetLabels (c • z₀) = (model.classes (z c)).val)
    (hπ : ∀ c : Cl, model.specialize (forgetLabels (reduceLabelled (c • x₀))) = red (y c))
    (c : Cl) : model.geometry.pi (z c) = red (y c) :=
  (inputsAtDatum_of_orientedCorrespondence model reduceLabelled x₀ z₀ h₀ h
    forgetLabels hclass hπ).point_reduction c

end ZInQ.Manuscript.RC.HCMV21
