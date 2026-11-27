import ZInQKernel.Contrib.OneProof.RC.PreparedParam.Parametrization
import ZInQKernel.Contrib.OneProof.RC.X0Model.Rational
import ZInQKernel.Contrib.RC53Assist.AbelianCurve.SmoothCurve
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Birational.ValuativeExtension

/-! Turning the function field map in tex 1785–1786 into an everywhere defined
morphism. This construction is on-the-spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve TopologicalSpace
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.RC53Assist.AbelianCurve
  ZInQ.Contrib.RC53Assist.IsogenyScheme ModularCurve

namespace ZInQ.Manuscript.RC.ParamAtScale

open PreparedParam

/-- Any supplied model has dimension one: its function field is isomorphic to that of
the normalization of the j-line already constructed in `RC/X0Model`. -/
theorem model_dimension {N : ℕ} [NeZero N] (X : X0Model N) :
    topologicalKrullDim X.X = 1 := by
  let := X.integral
  let := X.proper
  let := X0Model.jAlgebra N
  let := X0Model.finite_jAlgebra N
  let := X0Model.integral N
  have hproper : IsProper (X0Model.overQ N) := X0Model.proper N
  have : LocallyOfFiniteType (X0Model.overQ N) := hproper.toLocallyOfFiniteType
  let := functionFieldAlgebra X.overQ
  let := functionFieldAlgebra (X0Model.overQ N)
  let e : X.X.functionField ≃ₐ[ℚ] (X0Model.curve N).functionField :=
    { __ := X.functionField.trans (X0Model.functionField N).symm
      commutes' := fun q => DFunLike.congr_fun
        (Subsingleton.elim
          (((X.functionField.trans (X0Model.functionField N).symm).toRingHom).comp
            (algebraMap ℚ X.X.functionField))
          (algebraMap ℚ (X0Model.curve N).functionField)) q }
  calc
    _ = ((Algebra.trdeg ℚ X.X.functionField).toENat : WithBot ℕ∞) :=
      dimension_eq_trdeg X.overQ
    _ = ((Algebra.trdeg ℚ (X0Model.curve N).functionField).toENat : WithBot ℕ∞) := by
      rw [e.trdeg_eq]
    _ = topologicalKrullDim (X0Model.curve N) := (dimension_eq_trdeg (X0Model.overQ N)).symm
    _ = 1 := ZInQ.Contrib.CloudW07JacobiansCurves.NormalModel.topologicalKrullDim_Xn (modularFunctionField N)

private theorem spec_over_rat {F : Type} [Field F] (u v : Spec (.of F) ⟶ Spec (.of ℚ)) :
    u = v := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective u
  obtain ⟨b, rfl⟩ := Spec.map_surjective v
  exact congrArg Spec.map (CommRingCat.hom_ext (Subsingleton.elim a.hom b.hom))

/-- An embedding of the elliptic function field into the rational modular function field
gives a dominant morphism over `ℚ`, with that specified generic map.
This is independent of the choice of analytic scale. -/
theorem morphism_of_functionField {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {N : ℕ} [NeZero N] (X : X0Model N)
    (ι : E.toAffine.FunctionField →+* modularFunctionField N) :
    letI := X.integral
    ∃ (π : X.X ⟶ Proj E.toProjective.grading),
      π ≫ projectiveOverQ E = X.overQ ∧ IsDominant π ∧
      X.X.fromSpecFunctionField ≫ π =
        Spec.map (CommRingCat.ofHom (X.functionField.symm.toRingHom.comp
          (ι.comp (projFunctionFieldEquiv E).toRingHom))) ≫
            (Proj E.toProjective.grading).fromSpecFunctionField := by
  let := X.integral
  let := X.smooth
  let Y := Proj E.toProjective.grading
  let : X.X.Over (Spec (.of ℚ)) := ⟨X.overQ⟩
  let : Y.Over (Spec (.of ℚ)) := ⟨projectiveOverQ E⟩
  have : IsProper (Y ↘ Spec (.of ℚ)) := by
    change IsProper (projectiveOverQ E)
    unfold projectiveOverQ
    have := isProper_proj E
    infer_instance
  have : Y.IsSeparated :=
    ⟨by rw [← terminal.comp_from (Y ↘ Spec (.of ℚ))]; infer_instance⟩
  let a : Y.functionField →+* X.X.functionField :=
    X.functionField.symm.toRingHom.comp (ι.comp (projFunctionFieldEquiv E).toRingHom)
  let g := Spec.map (CommRingCat.ofHom a) ≫ Y.fromSpecFunctionField
  have hg : g ≫ (Y ↘ Spec (.of ℚ)) = X.X.fromSpecFunctionField ≫ X.overQ :=
    spec_over_rat _ _
  obtain ⟨π, hQ, hgen⟩ := Scheme.exists_hom_of_valuationRing_stalk
    (base := Spec (.of ℚ)) (smooth_curve_valuation_stalk X.overQ (model_dimension X)) g hg
  have hη : π (genericPoint X.X) = genericPoint Y := by
    have h := congrArg (fun t : Spec X.X.functionField ⟶ Y =>
      t (IsLocalRing.closedPoint X.X.functionField)) hgen
    change π (X.X.fromSpecFunctionField (IsLocalRing.closedPoint X.X.functionField)) =
      Y.fromSpecFunctionField (Spec.map (CommRingCat.ofHom a)
        (IsLocalRing.closedPoint X.X.functionField)) at h
    rw [Subsingleton.elim (Spec.map (CommRingCat.ofHom a)
      (IsLocalRing.closedPoint X.X.functionField)) (IsLocalRing.closedPoint Y.functionField),
      Scheme.fromSpecStalk_closedPoint, Scheme.fromSpecStalk_closedPoint] at h
    exact h
  refine ⟨π, hQ.1, ?_, hgen⟩
  rw [isDominant_iff, denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_spec Y]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint X.X, hη⟩)


end ZInQ.Manuscript.RC.ParamAtScale
