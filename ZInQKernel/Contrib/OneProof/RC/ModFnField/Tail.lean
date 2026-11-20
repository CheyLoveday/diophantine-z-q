import ZInQKernel.Contrib.OneProof.RC.ModFnField.Laurent
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_hasSum_qParam_mul_laurent
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique

/-! Uniqueness and multiplication for Laurent series known to converge only on
a cusp tail. On-the-spot (c). -/

noncomputable section

open Complex Function
open UpperHalfPlane hiding I

namespace ZInQ.Manuscript.RC.ModFnField

private def rescale (c : ℂ) (a : LaurentSeries ℂ) : LaurentSeries ℂ where
  coeff n := a.coeff n * c ^ n
  isPWO_support' :=
    a.isPWO_support.mono fun _ hn h => hn (by simp [h])

private theorem support_rescale {c : ℂ} (hc : c ≠ 0) (a : LaurentSeries ℂ) :
    (rescale c a).support = a.support := by
  ext n
  simp [rescale, HahnSeries.mem_support, zpow_ne_zero _ hc]

private theorem rescale_mul {c : ℂ} (hc : c ≠ 0) (a b : LaurentSeries ℂ) :
    rescale c (a * b) = rescale c a * rescale c b := by
  ext n
  change (a * b).coeff n * c ^ n = _
  rw [HahnSeries.coeff_mul, HahnSeries.coeff_mul, Finset.sum_mul]
  have hi : Finset.antidiagonal (rescale c a).isPWO_support (rescale c b).isPWO_support n =
      Finset.antidiagonal a.isPWO_support b.isPWO_support n := by
    ext p
    simp [Finset.mem_antidiagonal, support_rescale hc]
  rw [hi]
  refine Finset.sum_congr rfl fun p hp => ?_
  have he := (Finset.mem_antidiagonal.mp hp).2.2
  rw [← he, zpow_add₀ hc]
  change a.coeff p.1 * b.coeff p.2 * (c ^ p.1 * c ^ p.2) =
    (a.coeff p.1 * c ^ p.1) * (b.coeff p.2 * c ^ p.2)
  ring

private def raise (T : ℝ) (hT : 0 ≤ T) (τ : ℍ) : ℍ :=
  ⟨(τ : ℂ) + (T : ℂ) * I, by simpa using add_pos_of_pos_of_nonneg τ.im_pos hT⟩

private theorem lt_im_raise (T : ℝ) (hT : 0 ≤ T) (τ : ℍ) : T < (raise T hT τ).im := by
  change T < ((τ : ℂ) + (T : ℂ) * I).im
  simpa using (lt_add_of_pos_left T τ.im_pos)

private theorem qParam_raise (T : ℝ) (hT : 0 ≤ T) (τ : ℍ) :
    Periodic.qParam 1 (raise T hT τ : ℂ) =
      Periodic.qParam 1 ((T : ℂ) * I) * Periodic.qParam 1 τ := by
  simp only [raise, Periodic.qParam, ofReal_one, div_one, mul_add, exp_add]
  rw [mul_comm]

private theorem hasSum_rescale {a : LaurentSeries ℂ} {c q s : ℂ} :
    HasSum (fun n : ℤ => (rescale c a).coeff n * q ^ n) s ↔
      HasSum (fun n : ℤ => a.coeff n * (c * q) ^ n) s := by
  simp only [rescale, mul_zpow, mul_assoc]

/-- Equality of sums on a cusp tail determines the entire Laurent series. -/
theorem laurent_unique_of_tail {a b : LaurentSeries ℂ} {g : ℍ → ℂ} {T : ℝ}
    (ha : ∀ τ : ℍ, T < τ.im → HasSum (fun n : ℤ => a.coeff n * Periodic.qParam 1 τ ^ n) (g τ))
    (hb : ∀ τ : ℍ, T < τ.im → HasSum (fun n : ℤ => b.coeff n * Periodic.qParam 1 τ ^ n) (g τ)) :
    a = b := by
  let U := max T 0
  have hU : 0 ≤ U := le_max_right _ _
  let c := Periodic.qParam 1 ((U : ℂ) * I)
  have hc : c ≠ 0 := Periodic.qParam_ne_zero _
  have he := ModularCurve.laurent_qParam_coeff_unique 1 zero_lt_one
    (fun τ => g (raise U hU τ)) (rescale c a) (rescale c b) (fun τ => ?_) (fun τ => ?_)
  · ext n
    have h := congrArg (fun v : LaurentSeries ℂ => v.coeff n) he
    exact mul_right_cancel₀ (zpow_ne_zero n hc) h
  all_goals
    apply hasSum_rescale.mpr
    rw [← qParam_raise U hU τ]
    first
    | exact ha _ ((le_max_left _ _).trans_lt (lt_im_raise U hU τ))
    | exact hb _ ((le_max_left _ _).trans_lt (lt_im_raise U hU τ))

/-- Multiplication of two Laurent series realizes pointwise multiplication
on their common cusp tail. -/
theorem hasSum_mul_of_tail {a b : LaurentSeries ℂ} {g k : ℍ → ℂ} {T : ℝ}
    (ha : ∀ τ : ℍ, T < τ.im → HasSum (fun n : ℤ => a.coeff n * Periodic.qParam 1 τ ^ n) (g τ))
    (hb : ∀ τ : ℍ, T < τ.im → HasSum (fun n : ℤ => b.coeff n * Periodic.qParam 1 τ ^ n) (k τ))
    (τ : ℍ) (hτ : max T 0 < τ.im) :
    HasSum (fun n : ℤ => (a * b).coeff n * Periodic.qParam 1 τ ^ n) (g τ * k τ) := by
  let U := max T 0
  have hU : 0 ≤ U := le_max_right _ _
  let c := Periodic.qParam 1 ((U : ℂ) * I)
  have hc : c ≠ 0 := Periodic.qParam_ne_zero _
  have hUτ : U < τ.im := hτ
  let σ : ℍ := ⟨(τ : ℂ) - (U : ℂ) * I, by
    simpa [mul_im] using (sub_pos.mpr hUτ)⟩
  have hσ : raise U hU σ = τ := by ext; exact sub_add_cancel _ _
  rw [← hσ, qParam_raise]
  apply hasSum_rescale.mp
  rw [rescale_mul hc]
  refine ModularCurve.hasSum_qParam_mul_laurent 1 zero_lt_one _ _
    (fun ζ => g (raise U hU ζ)) (fun ζ => k (raise U hU ζ)) (fun ζ => ?_) (fun ζ => ?_) σ
  all_goals
    apply hasSum_rescale.mpr
    rw [← qParam_raise U hU ζ]
    first
    | exact ha _ ((le_max_left _ _).trans_lt (lt_im_raise U hU ζ))
    | exact hb _ ((le_max_left _ _).trans_lt (lt_im_raise U hU ζ))


end ZInQ.Manuscript.RC.ModFnField
