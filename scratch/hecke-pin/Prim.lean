import ZInQKernel.Contrib.OneProof.HeckePin

noncomputable section
namespace AfTateLam.HeckePin
open PkgI4 (CF coeff)
open Function UpperHalfPlane Real
local notation "𝕢" => Function.Periodic.qParam
local notation "Iℂ" => Complex.I

theorem eichlerPrimitive : EichlerPrimitive := by
  intro N f
  have hΓ : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [CongruenceSubgroup.strictPeriods_Gamma1]
  have : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  set c := UpperHalfPlane.cuspFunction 1 (⇑f) with hcdef
  have hdiff : DifferentiableOn ℂ c (Metric.ball 0 1) :=
    differentiableOn_cuspFunction_ball one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)
  have hds : DifferentiableOn ℂ (dslope c 0) (Metric.ball 0 1) :=
    (Complex.differentiableOn_dslope (Metric.ball_mem_nhds 0 one_pos)).2 hdiff
  obtain ⟨G, hG⟩ := hds.isExactOn_ball
  refine ⟨fun τ => G (𝕢 1 (τ : ℂ)) / (2 * π * Iℂ), fun τ => ?_⟩
  have hq : 𝕢 1 (τ : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ
  have hq0 : 𝕢 1 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
  -- derivative of q
  have hdq : HasDerivAt (𝕢 1) (2 * π * Iℂ * 𝕢 1 (τ : ℂ)) (τ : ℂ) := by
    have := ((hasDerivAt_id (τ : ℂ)).const_mul (2 * π * Iℂ / 1)).cexp
    convert this using 1
    · funext z; simp only [Function.Periodic.qParam, id]; congr 1; push_cast; ring
    · simp only [Function.Periodic.qParam, id]; push_cast; ring_nf
  have hcomp := ((hG _ hq).comp (τ : ℂ) hdq).div_const (2 * π * Iℂ)
  have hval : dslope c 0 (𝕢 1 (τ : ℂ)) * (2 * π * Iℂ * 𝕢 1 (τ : ℂ)) / (2 * π * Iℂ) = f τ := by
    rw [dslope_of_ne _ hq0, slope_def_field]
    have hc0 : c 0 = 0 := CuspFormClass.cuspFunction_apply_zero f one_pos hΓ
    have hcq : c (𝕢 1 (τ : ℂ)) = f τ := by
      simpa [hcdef] using UpperHalfPlane.eq_cuspFunction τ one_ne_zero
        (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    rw [hc0, hcq]
    have : (2 * π * Iℂ : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    field_simp
    ring
  rw [hval] at hcomp
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(UpperHalfPlane.isOpen_upperHalfPlaneSet).mem_nhds τ.im_pos] with z hz
  simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

end AfTateLam.HeckePin
