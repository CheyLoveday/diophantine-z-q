import ZInQKernel.Contrib.OneProof.RC.PreparedParam.Consumers

/-! The same rational morphism at the existing prepared and Heegner interfaces
(tex 2411–2416, 2915–2917 and 8213–8217). The interface wiring is provenance (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve NumberField
  ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.SelmerTwoPower
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
  TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields

namespace ZInQ.Manuscript.RC.ParamAtScale

open PreparedParam

/-- The genus selector and the stage selector take the same family of values.
The stage clause uses the setup's given witness. -/
theorem prepared_and_missing_at_scale {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W}
    {L : ℕ} [NeZero (newformLevel (Ecurve ℓ))]
    {X : X0Model (newformLevel (Ecurve ℓ))} (s : StageKummer.Setup I L)
    (hCM : CMFieldOfDefinition X)
    (hπ : letI := s.eE; AlgebraicParametrizationAtScale (Ecurve ℓ) X I.f I.Lat I.κ) :
    (∀ h (hp : Prepared (Ecurve ℓ) W.hstar h),
      StageSelector.PreparedParamValue (Ecurve ℓ) I.f I.Lat I.κ
        (StageKummer.positiveLevel s) I.hgp hp) ∧ StageKummer.MissingParamValues s := by
  let := s.eE
  exact ⟨preparedParamValues hCM hπ (StageKummer.positiveLevel s) I.hgp,
    missingParamValues s hCM hπ⟩

open Classical in
/-- For already chosen CM representatives over their class fields, there is one
rational morphism whose values after the specified embeddings are the fixed
analytic values at every conductor. This accommodates the compatible choices
used for the CCL trace theorem. -/
theorem oriented_cm_values_at_scale {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [NeZero (newformLevel E)] {X : X0Model (newformLevel E)}
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} (hπ : AlgebraicParametrizationAtScale E X f Lat κ)
    {K : Type} [Field K] [NumberField K]
    (O : ℕ → NumberFieldOrder K)
    (ι : ∀ m, ringClassField (O m) →ₐ[ℚ] ℂ)
    (x : ∀ m, FieldPoint X.overQ (ringClassField (O m)))
    (A B : ℕ → ℤ)
    (hx : ∀ m, (x m).map (ι m) = X.complexPoint (cmPoint (A m) (B m) (O m).discr)) :
    ∃ (π : X.X ⟶ Proj E.toProjective.grading) (hQ : π ≫ projectiveOverQ E = X.overQ),
      IsDominant π ∧
      ∀ m, Affine.Point.map (W' := E.toAffine) (ι m)
          (projectiveValue ((x m).comp π hQ).val) =
        phiAn E f Lat κ (cmPoint (A m) (B m) (O m).discr) := by
  obtain ⟨π, hQ, hdom, hcompat⟩ := hπ
  refine ⟨π, hQ, hdom, fun m => ?_⟩
  let u := ((x m).comp π hQ).val
  calc
    _ = projectiveValue (Spec.map (CommRingCat.ofHom (ι m).toRingHom) ≫ u) :=
      projectiveValue_map (ι m) u
    _ = projectiveValue (((x m).map (ι m)).comp π hQ).val := by
      simp only [u, FieldPoint.comp, FieldPoint.map, Category.assoc]
    _ = _ := (congrArg (fun v : FieldPoint X.overQ ℂ =>
      projectiveValue (v.comp π hQ).val) (hx m)).trans (hcompat _)


end ZInQ.Manuscript.RC.ParamAtScale
