import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_hasSum_jq_qParam
import Mathlib.Analysis.Complex.CauchyIntegral

/-! The Laurent expansions of the two distinguished functions at infinity.
This is the generator calculation for the comparison implicit at tex
1785–1786 and 2915–2919 (on the spot, provenance (c)). -/

noncomputable section

open ModularCurve

namespace ZInQ.Manuscript.RC.X0Model

/-- The usual analytic j-function on the upper half-plane. -/
def analyticJ (τ : UpperHalfPlane) : ℂ :=
  ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

/-- Multiplication of an upper half-plane parameter by a positive integer. -/
def dilate (N : ℕ) [NeZero N] (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(N : ℂ) * (τ : ℂ), by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) τ.im_pos⟩

/-- The function j(Nτ), with Nτ regarded as a point of the upper half-plane. -/
def analyticJN (N : ℕ) [NeZero N] (τ : UpperHalfPlane) : ℂ :=
  analyticJ (dilate N τ)

theorem analyticOn_j : AnalyticOnNhd ℂ (analyticJ ∘ UpperHalfPlane.ofComplex)
    {z : ℂ | 0 < z.im} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn UpperHalfPlane.isOpen_upperHalfPlaneSet).2
  apply UpperHalfPlane.mdifferentiable_iff.mp
  exact (ModularForm.E₄.holo'.pow 3).div CuspForm.discriminant.holo'
    ModularForm.discriminant_ne_zero

theorem analyticOn_jN (N : ℕ) [NeZero N] :
    AnalyticOnNhd ℂ (analyticJN N ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} := by
  have hpos (w : ℂ) (hw : 0 < w.im) : 0 < ((N : ℂ) * w).im :=
    (dilate N (⟨w, hw⟩ : UpperHalfPlane)).im_pos
  intro z hz
  have hlin : AnalyticAt ℂ (fun w : ℂ => (N : ℂ) * w) z :=
    analyticAt_const.mul analyticAt_id
  have ha := (analyticOn_j ((N : ℂ) * z) (hpos z hz)).comp hlin
  apply ha.congr
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  simp only [Function.comp_apply, analyticJN,
    UpperHalfPlane.ofComplex_apply_of_im_pos hw, UpperHalfPlane.ofComplex_apply_of_im_pos (hpos w hw)]
  rfl

/-- The Laurent monomial used in the section comparison. -/
private theorem qParam_zpow_eq (z : ℂ) (n : ℤ) :
    Function.Periodic.qParam 1 z ^ n =
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z) := by
  rw [Function.Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_int_mul]
  congr 1
  ring

theorem hasSum_j (τ : UpperHalfPlane) :
    HasSum (fun n : ℤ => (jq.coeff n : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ))) (analyticJ τ) := by
  simpa only [analyticJ, qParam_zpow_eq] using hasSum_jq_qParam τ

theorem hasSum_jN (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    HasSum (fun n : ℤ => ((jqN N).coeff n : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ))) (analyticJN N τ) := by
  simp only [← qParam_zpow_eq]
  have h := hasSum_jq_qParam (dilate N τ)
  have hq :
      Function.Periodic.qParam 1 ((dilate N τ : UpperHalfPlane) : ℂ) =
      Function.Periodic.qParam 1 (τ : ℂ) ^ N := by
    change Function.Periodic.qParam 1 ((N : ℂ) * (τ : ℂ)) = _
    unfold Function.Periodic.qParam
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  rw [hq] at h
  have hinj : Function.Injective (fun n : ℤ => (N : ℤ) * n) :=
    mul_right_injective₀ (by exact_mod_cast NeZero.ne N)
  refine (Function.Injective.hasSum_iff hinj ?_).mp ?_
  · intro n hn
    have hnd : ¬ (N : ℤ) ∣ n := by
      rintro ⟨m, rfl⟩
      exact hn ⟨m, rfl⟩
    simp [jqN, qExpand_coeff_of_not_dvd N jq hnd]
  · change HasSum (fun n : ℤ => ((qExpand ℚ N jq).coeff ((N : ℤ) * n) : ℂ) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ ((N : ℤ) * n)) _
    simpa only [analyticJN, analyticJ, qExpand_coeff_mul, zpow_mul, zpow_natCast] using h


end ZInQ.Manuscript.RC.X0Model
