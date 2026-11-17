import ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Birational.ValuativeExtension
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Dimension

/-! # isj1-dict, part 3: a smooth proper curve over `ℚ` is determined by its function field -/

noncomputable section

namespace ISJ1Curve

open CategoryTheory Limits AlgebraicGeometry LeafModCurves

/-- Verbatim copy of the dictionary leaf. -/
def CurveIsoOfFunctionFieldIso : Prop :=
  ∀ (X X' : Over SpecQ) [IsIntegral X.left] [IsIntegral X'.left], IsCurve X → IsCurve X' →
    Nonempty (X.left.functionField ≃+* X'.left.functionField) → Nonempty (X ≅ X')

/-- Any two morphisms `Spec K → Spec ℚ` agree. -/
theorem spec_to_specQ_eq {K : Type} [Field K] (a b : Spec (CommRingCat.of K) ⟶ SpecQ) : a = b := by
  rw [← Spec.map_preimage a, ← Spec.map_preimage b]
  congr 1
  ext1
  exact RingHom.ext_rat _ _

/-- The generic point is dense: `Spec K(X) → X` is dominant. -/
theorem isDominant_fromSpecFunctionField (X : Scheme) [IsIntegral X] :
    IsDominant X.fromSpecFunctionField := by
  constructor
  rw [DenseRange, dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  have h : genericPoint X ∈ Set.range X.fromSpecFunctionField :=
    ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
  have := closure_mono (Set.singleton_subset_iff.mpr h)
  rw [(genericPoint_spec X).def] at this
  exact this

/-- A scheme proper over `Spec ℚ` is separated. -/
theorem isSeparated_of_over (Y : Scheme) (f : Y ⟶ SpecQ) [IsSeparated f] : Y.IsSeparated := by
  constructor
  rw [show terminal.from Y = f ≫ terminal.from SpecQ from (terminal.hom_ext _ _)]
  infer_instance

/-- The morphism `X → X'` extending a function-field isomorphism (vendored
`exists_hom_of_valuationRing_stalk`). -/
theorem exists_hom (X X' : Over SpecQ) [IsIntegral X.left] [IsIntegral X'.left] (hX : IsCurve X)
    (hX' : IsCurve X') (φ : X'.left.functionField →+* X.left.functionField) :
    ∃ f : X ⟶ X', X.left.fromSpecFunctionField ≫ f.left =
      Spec.map (CommRingCat.ofHom φ) ≫ X'.left.fromSpecFunctionField := by
  have : IsProper X'.hom := hX'.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  let _ : X.left.Over SpecQ := ⟨X.hom⟩
  let _ : X'.left.Over SpecQ := ⟨X'.hom⟩
  have : IsProper (X'.left ↘ SpecQ) := inferInstanceAs (IsProper X'.hom)
  have : X'.left.IsSeparated := isSeparated_of_over X'.left X'.hom
  have hval : ∀ x : X.left, ValuationRing (X.left.presheaf.stalk x) := fun x =>
    AlgebraicGeometry.Scheme.valuationRing_stalk X.hom x
  obtain ⟨f, hfo, hf⟩ := Scheme.exists_hom_of_valuationRing_stalk (base := SpecQ) hval
    (Spec.map (CommRingCat.ofHom φ) ≫ X'.left.fromSpecFunctionField) (spec_to_specQ_eq _ _)
  exact ⟨Over.homMk f hfo.comp_over, hf⟩

theorem curveIsoOfFunctionFieldIso_proof : CurveIsoOfFunctionFieldIso := by
  intro X X' _ _ hX hX' ⟨e⟩
  obtain ⟨f, hf⟩ := exists_hom X X' hX hX' e.symm.toRingHom
  obtain ⟨g, hg⟩ := exists_hom X' X hX' hX e.toRingHom
  have : IsProper X.hom := hX.proper
  have : IsProper X'.hom := hX'.proper
  let _ : X.left.Over SpecQ := ⟨X.hom⟩
  let _ : X'.left.Over SpecQ := ⟨X'.hom⟩
  have : IsSeparated (X.left ↘ SpecQ) := inferInstanceAs (IsSeparated X.hom)
  have : IsSeparated (X'.left ↘ SpecQ) := inferInstanceAs (IsSeparated X'.hom)
  have : IsDominant X.left.fromSpecFunctionField := isDominant_fromSpecFunctionField X.left
  have : IsDominant X'.left.fromSpecFunctionField := isDominant_fromSpecFunctionField X'.left
  have hfg : f ≫ g = 𝟙 X := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.id_left]
    have : f.left.IsOver SpecQ := ⟨Over.w f⟩
    have : g.left.IsOver SpecQ := ⟨Over.w g⟩
    refine ext_of_isDominant_of_isSeparated' SpecQ X.left.fromSpecFunctionField ?_
    rw [← Category.assoc, hf, Category.assoc, hg, ← Category.assoc,
      ← Spec.map_comp, Category.comp_id]
    conv_rhs => rw [← Category.id_comp X.left.fromSpecFunctionField]
    congr 1
    rw [← Spec.map_id]
    congr 1
    ext x
    simp
    rfl
  have hgf : g ≫ f = 𝟙 X' := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.id_left]
    have : g.left.IsOver SpecQ := ⟨Over.w g⟩
    have : f.left.IsOver SpecQ := ⟨Over.w f⟩
    refine ext_of_isDominant_of_isSeparated' SpecQ X'.left.fromSpecFunctionField ?_
    rw [← Category.assoc, hg, Category.assoc, hf, ← Category.assoc,
      ← Spec.map_comp, Category.comp_id]
    conv_rhs => rw [← Category.id_comp X'.left.fromSpecFunctionField]
    congr 1
    rw [← Spec.map_id]
    congr 1
    ext x
    simp
    rfl
  exact ⟨⟨f, g, hfg, hgf⟩⟩

end ISJ1Curve

#print axioms ISJ1Curve.curveIsoOfFunctionFieldIso_proof
