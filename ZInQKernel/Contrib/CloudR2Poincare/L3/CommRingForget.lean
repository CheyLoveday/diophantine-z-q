import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-! Preservation of sheafification and inverse-image Kan extensions by the
forgetful functor from commutative rings to rings. Pointwise Kan preservation
is assembled from filtered indexing categories and filtered-colimit preservation. -/

open CategoryTheory TopologicalSpace CategoryTheory.Limits

namespace ZInQ.Contrib.CloudR2Poincare.L3
#cloudR2LocalInstances

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Forgetting commutativity preserves sheafification on a topological space. -/
theorem commRingForget_preservesSheafification (X : TopCat.{u}) :
    (Opens.grothendieckTopology X).PreservesSheafification
      (forget₂ CommRingCat.{u} RingCat.{u}) := by
  exact GrothendieckTopology.instPreservesSheafification
    (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})

/-- The index category of the pointwise inverse-image Kan extension is filtered:
preimages preserve finite intersections, and the top open gives an object. -/
private theorem commRingForget_kanIndex_filtered {X Y : TopCat.{u}} (f : X ⟶ Y)
    (U : (Opens X)ᵒᵖ) : IsFiltered (CostructuredArrow (Opens.map f).op U) := by
  letI : RepresentablyFlat (Opens.map f) := inferInstanceAs (RepresentablyFlat (Opens.map f))
  letI : RepresentablyCoflat (Opens.map f).op :=
    (representablyCoflat_op_iff (Opens.map f)).2 inferInstance
  exact RepresentablyCoflat.filtered U

/-- Forgetting commutativity preserves the particular filtered diagram at each
open, using the named filtered-colimit instance rather than a Kan-instance search. -/
private theorem commRingForget_kanDiagram_preserved {X Y : TopCat.{u}} (f : X ⟶ Y)
    (F : (Opens Y)ᵒᵖ ⥤ CommRingCat.{u}) (U : (Opens X)ᵒᵖ) :
    PreservesColimit (CostructuredArrow.proj (Opens.map f).op U ⋙ F)
      (forget₂ CommRingCat.{u} RingCat.{u}) := by
  letI : IsFiltered (CostructuredArrow (Opens.map f).op U) :=
    commRingForget_kanIndex_filtered f U
  letI : PreservesFilteredColimits (forget₂ CommRingCat.{u} RingCat.{u}) :=
    CommRingCat.FilteredColimits.forget₂Ring_preservesFilteredColimits
  letI : PreservesColimitsOfShape (CostructuredArrow (Opens.map f).op U)
      (forget₂ CommRingCat.{u} RingCat.{u}) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits _
  exact PreservesColimitsOfShape.preservesColimit

/-- Forgetting commutativity preserves the filtered Kan extension defining
presheaf inverse image on topological spaces. -/
theorem commRingForget_preservesLeftKanExtension {X Y : TopCat.{u}} (f : X ⟶ Y) :
    ∀ (F : (Opens Y)ᵒᵖ ⥤ CommRingCat.{u}),
      (forget₂ CommRingCat.{u} RingCat.{u}).PreservesLeftKanExtension F (Opens.map f).op := by
  intro F
  letI : HasColimits CommRingCat.{u} := inferInstance
  letI : (Opens.map f).op.HasPointwiseLeftKanExtension F := fun U =>
    inferInstanceAs (HasColimit (CostructuredArrow.proj (Opens.map f).op U ⋙ F))
  letI : (forget₂ CommRingCat.{u} RingCat.{u}).PreservesPointwiseLeftKanExtension
      F (Opens.map f).op := fun U => by
    letI : PreservesColimit (CostructuredArrow.proj (Opens.map f).op U ⋙ F)
        (forget₂ CommRingCat.{u} RingCat.{u}) := commRingForget_kanDiagram_preserved f F U
    exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit
      (forget₂ CommRingCat.{u} RingCat.{u}) F (Opens.map f).op U
  exact Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise
    (forget₂ CommRingCat.{u} RingCat.{u}) F (Opens.map f).op

end ZInQ.Contrib.CloudR2Poincare.L3
