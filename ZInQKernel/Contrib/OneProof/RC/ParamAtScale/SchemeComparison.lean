import ZInQKernel.Contrib.OneProof.RC.ParamAtScale.Algebraization
import ZInQKernel.Contrib.OneProof.RC.X0Model.Specialization

/-! Compare regular sections of the target after pullback. This is the scheme
calculation behind the chart comparison at tex 1785–1786 (provenance (c)). -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace ZInQ.Manuscript.RC.ParamAtScale

open PreparedParam

/-- Pullback and specialization of a regular section commute at a field-valued point. -/
theorem evalSection_comp {X Y : Scheme.{0}} {p : X ⟶ Spec (.of ℚ)} {q : Y ⟶ Spec (.of ℚ)}
    {F : Type} [Field F] [Algebra ℚ F] (u : FieldPoint p F) (π : X ⟶ Y) (hQ : π ≫ q = p)
    (V : Y.Opens) (hV : (u.comp π hQ).val default ∈ V) (a : Γ(Y, V)) :
    (u.comp π hQ).evalSection V hV a =
      u.evalSection (π ⁻¹ᵁ V) (show u.val default ∈ π ⁻¹ᵁ V from hV) (π.app V a) := by
  unfold FieldPoint.evalSection
  simp only [FieldPoint.comp, Scheme.Hom.comp_appLE, CommRingCat.comp_apply]

private theorem sectionMap_stalk {X : Scheme.{0}} {A : Type} [CommRing A] [IsLocalRing A]
    (u : Spec (.of A) ⟶ X) (U : X.Opens) (hu : ⊤ ≤ u ⁻¹ᵁ U) :
    X0Model.sectionMap u U hu =
      X.presheaf.germ U _ (hu (show IsLocalRing.closedPoint A ∈ ⊤ from trivial)) ≫
        Scheme.stalkClosedPointTo u := by
  symm
  rw [Scheme.germ_stalkClosedPointTo]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, X0Model.sectionMap,
    Scheme.Hom.appLE, Category.assoc]
  rfl

private theorem sectionMap_fromSpecFunctionField {X : Scheme.{0}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] (hu : ⊤ ≤ X.fromSpecFunctionField ⁻¹ᵁ U) :
    X0Model.sectionMap X.fromSpecFunctionField U hu = X.germToFunctionField U := by
  rw [sectionMap_stalk (A := X.functionField)]
  rw [Scheme.stalkClosedPointTo_fromSpecStalk]
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes]

private theorem top_preimage_generic {X : Scheme.{0}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] : ⊤ ≤ X.fromSpecFunctionField ⁻¹ᵁ U := by
  apply (Scheme.preimage_eq_top_of_closedPoint_mem _ _).ge
  rw [Scheme.fromSpecStalk_closedPoint]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

/-- The generic map determines the pullback of every regular section as an element
of the source function field. -/
theorem germToFunctionField_pullback {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (π : X ⟶ Y) (a : Y.functionField →+* X.functionField)
    (hgen : X.fromSpecFunctionField ≫ π =
      Spec.map (CommRingCat.ofHom a) ≫ Y.fromSpecFunctionField)
    (V : Y.Opens) [Nonempty V] [Nonempty (π ⁻¹ᵁ V)] (r : Γ(Y, V)) :
    X.germToFunctionField (π ⁻¹ᵁ V) (π.app V r) = a (Y.germToFunctionField V r) := by
  have hX := top_preimage_generic (X := X) (π ⁻¹ᵁ V)
  have hY := top_preimage_generic V
  have he : ⊤ ≤ (Spec.map (CommRingCat.ofHom a) ≫ Y.fromSpecFunctionField) ⁻¹ᵁ V := by
    intro x _
    exact hY (show Spec.map (CommRingCat.ofHom a) x ∈ ⊤ from trivial)
  have hd (g : Spec X.functionField ⟶ Y) (h : ⊤ ≤ g ⁻¹ᵁ V)
      (e : g = Spec.map (CommRingCat.ofHom a) ≫ Y.fromSpecFunctionField) :
      X0Model.sectionMap g V h =
        X0Model.sectionMap (Spec.map (CommRingCat.ofHom a) ≫ Y.fromSpecFunctionField) V he := by
    subst g
    rfl
  have hh := hd (X.fromSpecFunctionField ≫ π) hX hgen
  rw [X0Model.sectionMap_comp _ a V hY he, sectionMap_fromSpecFunctionField] at hh
  have ht :
      X0Model.sectionMap (X.fromSpecFunctionField ≫ π) V hX =
        π.app V ≫ X0Model.sectionMap X.fromSpecFunctionField (π ⁻¹ᵁ V) hX := by
    unfold X0Model.sectionMap
    rw [Scheme.Hom.comp_appLE, Category.assoc]
  rw [ht, sectionMap_fromSpecFunctionField] at hh
  exact congrArg (fun m : Γ(Y, V) ⟶ X.functionField => m r) hh

#print axioms evalSection_comp
#print axioms sectionMap_stalk
#print axioms sectionMap_fromSpecFunctionField
#print axioms top_preimage_generic
#print axioms germToFunctionField_pullback

end ZInQ.Manuscript.RC.ParamAtScale
