import ZInQKernel.Contrib.OneProof.RC.X0Model2.BranchLabels
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous

/-! The local modular group action near an upper half-plane parameter
(tex 2915–2919, on the spot, provenance (c)). -/

noncomputable section

open Filter Matrix
open scoped Topology MatrixGroups

namespace ZInQ.Manuscript.RC.X0Model2

private def modularRange (s : SL(2, ℤ)) : 𝒮ℒ :=
  ⟨SpecialLinearGroup.mapGL ℝ s, ⟨s, rfl⟩⟩

private theorem modularRange_smul (s : SL(2, ℤ)) (w : UpperHalfPlane) :
    modularRange s • w = s • w := rfl

private theorem modularRange_injective : Function.Injective modularRange := by
  intro s t h
  apply Subtype.ext
  ext i j
  have hh := congrArg (fun g : 𝒮ℒ => (g.1 : GL (Fin 2) ℝ).val i j) h
  change (s i j : ℝ) = (t i j : ℝ) at hh
  exact_mod_cast hh

/-- There are only finitely many elements of the full integral modular
group fixing a center in the upper half-plane. -/
theorem finite_sl_stabilizer (τ : UpperHalfPlane) :
    {s : SL(2, ℤ) | s • τ = τ}.Finite := by
  simpa only [Set.preimage_ofPred_eq, modularRange_smul] using
    (ProperlyDiscontinuousSMul.finite_stabilizer' 𝒮ℒ τ).preimage modularRange_injective.injOn

/-- Shrink about the center so that every local equality of the first
coordinate comes from its stabilizer. This works also at (i) and (ho). -/
theorem exists_nhds_local_j_orbit (τ : UpperHalfPlane) :
    ∃ U ∈ 𝓝 τ, ∀ v ∈ U, ∀ w ∈ U, X0Model.analyticJ v = X0Model.analyticJ w →
      ∃ s : SL(2, ℤ), s • τ = τ ∧ s • v = w := by
  obtain ⟨U, hU, hproper⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self 𝒮ℒ τ
  refine ⟨U, hU, ?_⟩
  intro v hv w hw hj
  obtain ⟨s, rfl⟩ := (analyticJ_eq_iff v w).mp hj
  refine ⟨s, ?_, rfl⟩
  simpa only [modularRange_smul] using
    hproper (modularRange s) ⟨s • v, ⟨v, hv, modularRange_smul s v⟩, hw⟩

private abbrev sheet (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) : ℂ → ℂ :=
  fun w => X0Model.analyticJN N (γ • UpperHalfPlane.ofComplex w)

private theorem analyticAt_sheet (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    AnalyticAt ℂ (sheet N γ) (τ : ℂ) := by
  have hm : AnalyticAt ℂ (slMoebius γ) (τ : ℂ) := by
    apply AnalyticAt.div (by fun_prop) (by fun_prop)
    exact UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ
  have hj := X0Model.analyticOn_jN N ((γ • τ : UpperHalfPlane) : ℂ) (γ • τ : UpperHalfPlane).im_pos
  rw [coe_sl_smul] at hj
  apply (hj.comp hm).congr
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
  let w : UpperHalfPlane := ⟨z, hz⟩
  change X0Model.analyticJN N (UpperHalfPlane.ofComplex (slMoebius γ (w : ℂ))) =
    X0Model.analyticJN N (γ • UpperHalfPlane.ofComplex (w : ℂ))
  rw [← coe_sl_smul, UpperHalfPlane.ofComplex_apply, UpperHalfPlane.ofComplex_apply]

/-- Punctured overlap of the plane parametrizations, with both parameters
near the center, implies equality of the corresponding germs after an
element of the center stabilizer. A single equality at the center does
not give this conclusion. -/
theorem exists_nhds_germ_match_of_overlap (N : ℕ) [NeZero N] (τ : UpperHalfPlane)
    (γ₁ γ₂ : SL(2, ℤ)) :
    ∃ U ∈ 𝓝 τ, (∃ᶠ z in 𝓝[≠] (τ : ℂ), ∃ w ∈ U,
      X0Model.analyticJ (UpperHalfPlane.ofComplex z) = X0Model.analyticJ w ∧
      sheet N γ₁ z = X0Model.analyticJN N (γ₂ • w)) →
      ∃ s : SL(2, ℤ), s • τ = τ ∧ sheet N γ₁ =ᶠ[𝓝[≠] (τ : ℂ)] sheet N (γ₂ * s) := by
  obtain ⟨U, hU, hl⟩ := exists_nhds_local_j_orbit τ
  refine ⟨U, hU, fun h => ?_⟩
  have hmem : ((↑) : UpperHalfPlane → ℂ) '' U ∈ 𝓝 (τ : ℂ) := by
    rw [← UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq]
    exact image_mem_map hU
  have hp : ∃ᶠ z in 𝓝[≠] (τ : ℂ), ∃ s ∈ {s : SL(2, ℤ) | s • τ = τ},
      sheet N γ₁ z = sheet N (γ₂ * s) z := by
    refine (h.and_eventually (mem_nhdsWithin_of_mem_nhds hmem)).mono ?_
    rintro z ⟨⟨w, hw, hj, hjN⟩, ⟨v, hv, rfl⟩⟩
    rw [UpperHalfPlane.ofComplex_apply] at hj
    obtain ⟨s, hs, rfl⟩ := hl v hv w hw hj
    refine ⟨s, hs, ?_⟩
    simpa only [sheet, UpperHalfPlane.ofComplex_apply, mul_smul] using hjN
  obtain ⟨s, hs, he⟩ := ((finite_sl_stabilizer τ).frequently_exists).mp hp
  exact ⟨s, hs, ((analyticAt_sheet N γ₁ τ).frequently_eq_iff_eventually_eq
    (analyticAt_sheet N (γ₂ * s) τ) |>.mp he).filter_mono nhdsWithin_le_nhds⟩


end ZInQ.Manuscript.RC.X0Model2
