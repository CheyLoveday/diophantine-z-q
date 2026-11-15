import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilTheta
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

noncomputable section

open Complex Filter Topology
open scoped Real

namespace ZInQ.GZWeil

/-! ## J1. Transformation laws of `θ₂, θ₃, θ₄` -/

theorem jacobiTheta₂_add_one_right (z τ : ℂ) :
    jacobiTheta₂ z (τ + 1) = jacobiTheta₂ (z + 1 / 2) τ := by
  refine tsum_congr fun n => ?_
  simp only [jacobiTheta₂_term]
  rw [Complex.exp_eq_exp_iff_exists_int]
  obtain ⟨m, hm⟩ := Int.even_mul_pred_self n
  refine ⟨m, ?_⟩
  have hm' : ((n : ℂ) * ((n : ℂ) - 1)) = (m : ℂ) + m := by exact_mod_cast hm
  linear_combination (π * I) * hm'

theorem thetaThree_add_one (t : ℂ) : thetaThree (t + 1) = thetaFour t := by
  rw [thetaThree, thetaFour, jacobiTheta₂_add_one_right, zero_add]

theorem thetaFour_add_one (t : ℂ) : thetaFour (t + 1) = thetaThree t := by
  rw [thetaThree, thetaFour, jacobiTheta₂_add_one_right]
  norm_num
  exact jacobiTheta₂_add_left 0 t ▸ by simp

theorem thetaTwo_add_one (t : ℂ) : thetaTwo (t + 1) = cexp (π * I / 4) * thetaTwo t := by
  rw [thetaTwo, thetaTwo, jacobiTheta₂_add_one_right,
    show (t + 1) / 2 + 1 / 2 = t / 2 + 1 by ring, jacobiTheta₂_add_left, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  ring

/-- `(−iτ)^{1/2}` squared. -/
theorem sqrt_factor_sq (τ : ℂ) : ((-I * τ) ^ (1 / 2 : ℂ)) ^ 2 = -I * τ := by
  rw [show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num]
  exact Complex.cpow_nat_inv_pow _ two_ne_zero

theorem sqrt_factor_ne_zero {τ : ℂ} (hτ : τ ≠ 0) : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  exact Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ)

theorem thetaThree_S {τ : ℂ} (hτ : τ ≠ 0) :
    thetaThree (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * thetaThree τ := by
  have h := jacobiTheta₂_functional_equation 0 τ
  simp only [zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Complex.exp_zero, mul_one] at h
  rw [thetaThree, thetaThree, h]
  field_simp [sqrt_factor_ne_zero hτ]

theorem thetaTwo_S {τ : ℂ} (hτ : τ ≠ 0) :
    thetaTwo (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * thetaFour τ := by
  have h := jacobiTheta₂_functional_equation (1 / 2) τ
  rw [thetaTwo, thetaFour, h, show (-1 / τ) / 2 = -((1 / 2) / τ) by ring, jacobiTheta₂_neg_left]
  have hs := sqrt_factor_ne_zero hτ
  have he : cexp (π * I * (-1 / τ) / 4) = cexp (-π * I * (1 / 2) ^ 2 / τ) := by
    congr 1; field_simp; ring
  rw [he]
  field_simp

theorem thetaThree_S_sq {τ : ℂ} (hτ : τ ≠ 0) :
    thetaThree (-1 / τ) ^ 2 = -I * τ * thetaThree τ ^ 2 := by
  rw [thetaThree_S hτ, mul_pow, sqrt_factor_sq]

theorem thetaTwo_S_sq {τ : ℂ} (hτ : τ ≠ 0) :
    thetaTwo (-1 / τ) ^ 2 = -I * τ * thetaFour τ ^ 2 := by
  rw [thetaTwo_S hτ, mul_pow, sqrt_factor_sq]

theorem thetaFour_S_sq {τ : ℂ} (hτ : τ ≠ 0) :
    thetaFour (-1 / τ) ^ 2 = -I * τ * thetaTwo τ ^ 2 := by
  have hτ' : (-1 / τ) ≠ 0 := by simp [hτ]
  have h := thetaTwo_S_sq hτ'
  rw [show -1 / (-1 / τ) = τ by field_simp] at h
  rw [h]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring


/-! ## J2. Nonvanishing and the laws of the logarithmic derivatives -/

theorem im_neg_inv_pos {t : ℂ} (ht : 0 < t.im) : 0 < (-1 / t).im := by
  have h := (UpperHalfPlane.mk t ht).im_inv_neg_coe_pos
  simpa [neg_div, div_eq_mul_inv] using h

theorem ne_zero_of_im_pos {t : ℂ} (ht : 0 < t.im) : t ≠ 0 := by
  rintro rfl; simp at ht

theorem thetaThree_ne_zero {t : ℂ} (ht : 0 < t.im) : thetaThree t ≠ 0 := by
  rw [thetaThree, ZInQ.GZTheta.jacobiTheta₂_eq_jtpP ht]
  simpa using ZInQ.GZTheta.jtpP_ne_zero_of_real ht 0

theorem thetaFour_ne_zero {t : ℂ} (ht : 0 < t.im) : thetaFour t ≠ 0 := by
  rw [thetaFour, ZInQ.GZTheta.jacobiTheta₂_eq_jtpP ht]
  have := ZInQ.GZTheta.jtpP_ne_zero_of_real ht (1 / 2)
  push_cast at this
  exact this

theorem thetaTwo_ne_zero {t : ℂ} (ht : 0 < t.im) : thetaTwo t ≠ 0 := by
  have hτ := im_neg_inv_pos ht
  have h := thetaTwo_S_sq (ne_zero_of_im_pos hτ)
  rw [show -1 / (-1 / t) = t by field_simp [ne_zero_of_im_pos ht]] at h
  intro h0
  rw [h0] at h
  have : -I * (-1 / t) * thetaFour (-1 / t) ^ 2 ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) ?_)
      (pow_ne_zero _ (thetaFour_ne_zero hτ))
    exact ne_zero_of_im_pos hτ
  exact this (by rw [← h]; ring)

theorem differentiableAt_thetaFour {t : ℂ} (ht : 0 < t.im) : DifferentiableAt ℂ thetaFour t :=
  differentiableAt_jacobiTheta₂_snd (1 / 2) ht

/-- Logarithmic derivatives `θ'/θ`. -/
def LA (t : ℂ) : ℂ := deriv thetaTwo t / thetaTwo t
def LB (t : ℂ) : ℂ := deriv thetaThree t / thetaThree t
def LC (t : ℂ) : ℂ := deriv thetaFour t / thetaFour t

theorem LB_add_one (t : ℂ) : LB (t + 1) = LC t := by
  have hd : deriv thetaFour t = deriv thetaThree (t + 1) := by
    rw [← deriv_comp_add_const]; congr 1; funext s; exact (thetaThree_add_one s).symm
  rw [LB, LC, hd, thetaThree_add_one]

theorem LC_add_one (t : ℂ) : LC (t + 1) = LB t := by
  have hd : deriv thetaThree t = deriv thetaFour (t + 1) := by
    rw [← deriv_comp_add_const]; congr 1; funext s; exact (thetaFour_add_one s).symm
  rw [LB, LC, hd, thetaFour_add_one]

theorem LA_add_one (t : ℂ) : LA (t + 1) = LA t := by
  have hc : cexp (π * I / 4) ≠ 0 := Complex.exp_ne_zero _
  have hf : (fun s => thetaTwo (s + 1)) = fun s => cexp (π * I / 4) * thetaTwo s :=
    funext thetaTwo_add_one
  have hd : deriv thetaTwo (t + 1) = cexp (π * I / 4) * deriv thetaTwo t := by
    rw [← deriv_comp_add_const, hf, deriv_const_mul_field']
  rw [LA, LA, hd, thetaTwo_add_one]
  by_cases h0 : thetaTwo t = 0
  · simp [h0]
  · field_simp

/-- **The `S`-law of a logarithmic derivative.** If `g(−1/s)² = −is h(s)²` for `s ≠ 0`, then
`g'/g (−1/t) = t/2 + t² h'/h (t)`. -/
theorem log_deriv_S {g h : ℂ → ℂ} (hgh : ∀ s : ℂ, s ≠ 0 → g (-1 / s) ^ 2 = -I * s * h s ^ 2)
    {t : ℂ} (ht0 : t ≠ 0) (hg : DifferentiableAt ℂ g (-1 / t)) (hh : DifferentiableAt ℂ h t)
    (hh0 : h t ≠ 0) :
    deriv g (-1 / t) / g (-1 / t) = t / 2 + t ^ 2 * (deriv h t / h t) := by
  have hinv : HasDerivAt (fun s : ℂ => -1 / s) (1 / t ^ 2) t := by
    have := (hasDerivAt_inv ht0).const_mul (-1 : ℂ)
    convert this using 1
    · funext s; ring
    · field_simp
  have h1 : HasDerivAt (fun s => g (-1 / s) ^ 2)
      (2 * g (-1 / t) ^ (2 - 1) * (deriv g (-1 / t) * (1 / t ^ 2))) t :=
    (hg.hasDerivAt.comp t hinv).pow 2
  have h2 : HasDerivAt (fun s => -I * s * h s ^ 2)
      (-I * 1 * h t ^ 2 + -I * t * (2 * h t ^ (2 - 1) * deriv h t)) t :=
    ((hasDerivAt_id t).const_mul (-I)).mul (hh.hasDerivAt.pow 2)
  have hev : (fun s => g (-1 / s) ^ 2) =ᶠ[𝓝 t] fun s => -I * s * h s ^ 2 := by
    filter_upwards [isOpen_ne.mem_nhds ht0] with s hs using hgh s hs
  have heq := (h1.congr_of_eventuallyEq hev.symm).unique h2
  have hsq := hgh t ht0
  have hg0 : g (-1 / t) ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hsq
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) ht0) (pow_ne_zero _ hh0) hsq.symm
  generalize g (-1 / t) = G at heq hsq hg0 ⊢
  generalize deriv g (-1 / t) = G' at heq ⊢
  generalize h t = H at heq hsq hh0 ⊢
  generalize deriv h t = H' at heq ⊢
  norm_num at heq
  have heq2 : 2 * G * G' = t ^ 2 * (-(I * H ^ 2) + -(I * t * (2 * H * H'))) := by
    rw [← heq]; field_simp
  have key : G' = G * (t * H + 2 * t ^ 2 * H') / (2 * H) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hh0)]
    apply mul_left_cancel₀ hg0
    linear_combination H * heq2 - (t * H + 2 * t ^ 2 * H') * hsq
  rw [key]
  field_simp

end ZInQ.GZWeil
