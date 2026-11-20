import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.AtScale
import ZInQKernel.Contrib.OneProof.RC.X0Branch.Model

/-! The fixed-scale parametrization and the prepared and stage selectors on the
constructed modular curve (tex 1785–1787, 2411–2412, 8213–8217; provenance (c)). -/

noncomputable section

open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.PreparedParam
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.ParamJoin

/-- The actual curve's parametrization at the given scale, on the constructed chart. -/
theorem algebraicParametrizationAtScale {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]
    [NeZero (newformLevel (Ecurve ℓ))]
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat)
    {κ : ℂ} (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ)
    (hr : ∃ c : ℚ, (c : ℂ) = κ) :
    AlgebraicParametrizationAtScale (Ecurve ℓ) (X0Branch.model (newformLevel (Ecurve ℓ))) f Lat κ :=
  ModFnClassify.algebraicParametrizationAtScale _ _ f hf hLat hκ hr

/-- The existing stage setup provides positive level and the prepared selector's inputs. -/
theorem prepared_values {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W}
    {L : ℕ} (s : StageKummer.Setup I L) (hr : ∃ c : ℚ, (c : ℂ) = I.κ)
    (hCM : letI : NeZero (newformLevel (Ecurve ℓ)) := ⟨(StageKummer.positiveLevel s).ne'⟩
           CMFieldOfDefinition (X0Branch.model (newformLevel (Ecurve ℓ)))) :
    ∀ h (hp : Prepared (Ecurve ℓ) W.hstar h),
      StageSelector.PreparedParamValue (Ecurve ℓ) I.f I.Lat I.κ
        (StageKummer.positiveLevel s) I.hgp hp := by
  let _ : NeZero (newformLevel (Ecurve ℓ)) := ⟨(StageKummer.positiveLevel s).ne'⟩
  exact ModFnClassify.prepared_values s hr hCM

/-- The selector can fill admissible holes using the same chart and fixed scale. -/
theorem missing_values {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W}
    {L : ℕ} (s : StageKummer.Setup I L) (hr : ∃ c : ℚ, (c : ℂ) = I.κ)
    (hCM : letI : NeZero (newformLevel (Ecurve ℓ)) := ⟨(StageKummer.positiveLevel s).ne'⟩
           CMFieldOfDefinition (X0Branch.model (newformLevel (Ecurve ℓ)))) :
    StageKummer.MissingParamValues s := by
  let _ : NeZero (newformLevel (Ecurve ℓ)) := ⟨(StageKummer.positiveLevel s).ne'⟩
  exact ModFnClassify.missing_values s hr hCM

#print axioms algebraicParametrizationAtScale
#print axioms prepared_values
#print axioms missing_values

end ZInQ.Manuscript.RC.ParamJoin
