import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.Classification
import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.ProjectiveIdentity
import ZInQKernel.Contrib.OneProof.RC.ModFnField.FunctionField
import ZInQKernel.Contrib.OneProof.RC.ParamAtScale.Consumers

/-! Rational algebraization at the prescribed analytic scale, and the
three consumers of its values (tex 1785–1787, 2411–2416, 2915–2917,
8213–8217). The field route and interface comparison are provenance (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory UpperHalfPlane WeierstrassCurve NumberField
open ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.Manuscript.RC.PreparedParam ZInQ.Manuscript.RC.ParamAtScale
open ZInQ.Manuscript.RC.ModFnField

namespace ZInQ.Manuscript.RC.ModFnClassify

/-- The matching dominant rational morphism for a supplied modular model
and the already fixed scale, given a rational representative of that scale. -/
theorem algebraicParametrizationAtScale (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [NeZero (newformLevel E)] (X : X0Model (newformLevel E))
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf E Lat)
    {κ : ℂ} (hκ : IsParamScale (newformLevel E) f Lat κ)
    (hr : ∃ c : ℚ, (c : ℂ) = κ) :
    AlgebraicParametrizationAtScale E X f Lat κ := by
  obtain ⟨c, rfl⟩ := hr
  have hc : c ≠ 0 := fun h => hκ.1 (by simp [h])
  obtain ⟨ι, π, hQ, hdom, hgen, hx, hy⟩ :=
    dominant_morphism_of_classification E X (complexCuspClassification _) f hf hLat hκ
  exact ⟨π, hQ, hdom, projective_value_of_expansions E X f hf hLat hc π hQ ι hgen hx hy⟩

/-- Specialization to the actual curve and the analytic data already used
by its genus and stage selectors. -/
theorem curve_algebraicParametrizationAtScale {ℓ : ℕ} {W : WData ℓ}
    (I : GenusOddInstance W) [NeZero (newformLevel (Ecurve ℓ))]
    (X : X0Model (newformLevel (Ecurve ℓ))) (hr : ∃ c : ℚ, (c : ℂ) = I.κ) :
    letI := I.hE
    AlgebraicParametrizationAtScale (Ecurve ℓ) X I.f I.Lat I.κ := by
  let := I.hE
  exact algebraicParametrizationAtScale _ X I.f I.hf I.hLat I.hκ hr

theorem prepared_values {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W}
    {L : ℕ} [NeZero (newformLevel (Ecurve ℓ))]
    {X : X0Model (newformLevel (Ecurve ℓ))} (s : StageKummer.Setup I L)
    (hr : ∃ c : ℚ, (c : ℂ) = I.κ) (hCM : CMFieldOfDefinition X) :
    ∀ h (hp : Prepared (Ecurve ℓ) W.hstar h),
      StageSelector.PreparedParamValue (Ecurve ℓ) I.f I.Lat I.κ
        (StageKummer.positiveLevel s) I.hgp hp :=
  (prepared_and_missing_at_scale s hCM (curve_algebraicParametrizationAtScale I X hr)).1

theorem missing_values {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W}
    {L : ℕ} [NeZero (newformLevel (Ecurve ℓ))]
    {X : X0Model (newformLevel (Ecurve ℓ))} (s : StageKummer.Setup I L)
    (hr : ∃ c : ℚ, (c : ℂ) = I.κ) (hCM : CMFieldOfDefinition X) :
    StageKummer.MissingParamValues s :=
  (prepared_and_missing_at_scale s hCM (curve_algebraicParametrizationAtScale I X hr)).2

open Classical in
theorem oriented_cm_values {ℓ : ℕ} {W : WData ℓ} (I : GenusOddInstance W)
    [NeZero (newformLevel (Ecurve ℓ))]
    {X : X0Model (newformLevel (Ecurve ℓ))} (hr : ∃ c : ℚ, (c : ℂ) = I.κ)
    {K : Type} [Field K] [NumberField K]
    (O : ℕ → NumberFieldOrder K)
    (ι : ∀ m, ringClassField (O m) →ₐ[ℚ] ℂ)
    (x : ∀ m, FieldPoint X.overQ (ringClassField (O m)))
    (A B : ℕ → ℤ)
    (hx : ∀ m, (x m).map (ι m) = X.complexPoint (cmPoint (A m) (B m) (O m).discr)) :
    letI := I.hE
    ∃ (π : X.X ⟶ Proj (Ecurve ℓ).toProjective.grading) (hQ : π ≫ projectiveOverQ (Ecurve ℓ) = X.overQ),
      IsDominant π ∧
      ∀ m, Affine.Point.map (W' := (Ecurve ℓ).toAffine) (ι m)
          (projectiveValue ((x m).comp π hQ).val) =
        phiAn (Ecurve ℓ) I.f I.Lat I.κ (cmPoint (A m) (B m) (O m).discr) := by
  let := I.hE
  exact oriented_cm_values_at_scale (curve_algebraicParametrizationAtScale I X hr) O ι x A B hx

#print axioms algebraicParametrizationAtScale
#print axioms curve_algebraicParametrizationAtScale
#print axioms prepared_values
#print axioms missing_values
#print axioms oriented_cm_values

end ZInQ.Manuscript.RC.ModFnClassify
