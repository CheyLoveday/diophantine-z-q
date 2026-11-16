import ZInQKernel.Contrib.OneProof.JavanpeykarDict
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # javanpeykar-dict: the function field of a base change (draft) -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace JavanpeykarDict

open CategoryTheory AlgebraicGeometry Limits

variable {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K))) (L : Type) [Field L] [Algebra K L]

/-- The projection `X_L → X`. -/
def pr : (baseChangeCurve X L).left ⟶ X.left :=
  pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))

theorem isPullback_pr : IsPullback (pr X L) (baseChangeCurve X L).hom X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  IsPullback.of_hasPullback _ _

theorem surjective_specMap_algebraMap :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  have : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Spec (.of L)) := inferInstanceAs (Nonempty (PrimeSpectrum L))
  exact ⟨fun _ ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩

theorem surjective_pr : Surjective (pr X L) :=
  MorphismProperty.of_isPullback (P := @Surjective) (isPullback_pr X L).flip
    (surjective_specMap_algebraMap L)

theorem pr_genericPoint [IsIntegral X.left] [IsIntegral (baseChangeCurve X L).left] :
    pr X L (genericPoint (baseChangeCurve X L).left) = genericPoint X.left := by
  have h := (genericPoint_spec (baseChangeCurve X L).left).image (pr X L).continuous
  rw [Set.top_eq_univ, Set.image_univ_of_surjective (surjective_pr X L).surj, closure_univ] at h
  exact h.eq (genericPoint_spec X.left)

/-- The map of function fields `K(X) → L(X_L)` induced by the projection. -/
def ffMap [IsIntegral X.left] [IsIntegral (baseChangeCurve X L).left] :
    X.left.functionField ⟶ (baseChangeCurve X L).left.functionField :=
  X.left.presheaf.stalkSpecializes (pr_genericPoint X L).specializes ≫
    (pr X L).stalkMap (genericPoint (baseChangeCurve X L).left)

theorem germ_ffMap [IsIntegral X.left] [IsIntegral (baseChangeCurve X L).left] (U : X.left.Opens)
    (hU : genericPoint X.left ∈ U) (hV : genericPoint (baseChangeCurve X L).left ∈ (pr X L) ⁻¹ᵁ U) :
    X.left.presheaf.germ U _ hU ≫ ffMap X L =
      (pr X L).app U ≫ (baseChangeCurve X L).left.presheaf.germ ((pr X L) ⁻¹ᵁ U) _ hV := by
  rw [ffMap, TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

end JavanpeykarDict
