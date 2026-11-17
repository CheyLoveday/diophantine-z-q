import ZInQKernel.Contrib.OneProof.CdOptimal.Level32

noncomputable section

open Complex ModularForm CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

namespace ZInQ.CdOpt.EtaW32Proof

/-- `η(z + n) = e^{π i n / 12} η(z)`. -/
theorem eta_add_int (z : ℂ) (n : ℤ) : η (z + n) = cexp (π * I * n / 12) * η z := by
  have hq (m : ℕ) : eta_q m (z + n) = eta_q m z := by
    have harg : 2 * π * I * (m + 1) * (z + n) =
        2 * π * I * (m + 1) * z + ((m + 1) * n : ℤ) * (2 * π * I) := by
      push_cast
      ring
    simp only [eta_q_eq_cexp]
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hexp : Function.Periodic.qParam 24 (z + n) =
      cexp (π * I * n / 12) * Function.Periodic.qParam 24 z := by
    simp only [Function.Periodic.qParam, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [ModularForm.eta, hq, hexp, mul_assoc]

theorem sqrt_re_pos {z : ℂ} (hz : 0 < z.im) : 0 < (Complex.sqrt z).re := by
  rw [Complex.sqrt, cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  have := (Complex.abs_re_lt_norm (z := z)).mpr hz.ne'
  have := neg_abs_le z.re
  linarith

theorem sqrt_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (Complex.sqrt z).im := by
  rw [Complex.sqrt, cpow_inv_two_im_eq_sqrt hz.le]
  apply Real.sqrt_pos.mpr
  have := (Complex.abs_re_lt_norm (z := z)).mpr hz.ne'
  have := le_abs_self z.re
  linarith

theorem sqrt_sq' (w : ℂ) : Complex.sqrt w ^ 2 = w := ZInQ.GZTheta.sqrt_sq_eq w

/-- The branch identity: `√y √z = i √w` when `y, z, w ∈ ℍ` and `y z = −w`. -/
theorem sqrt_mul_branch {y z w : ℂ} (hy : 0 < y.im) (hz : 0 < z.im) (hw : 0 < w.im)
    (h : y * z = -w) : Complex.sqrt y * Complex.sqrt z = I * Complex.sqrt w := by
  have hsq : (Complex.sqrt y * Complex.sqrt z) ^ 2 = (I * Complex.sqrt w) ^ 2 := by
    rw [mul_pow, mul_pow, sqrt_sq', sqrt_sq', sqrt_sq', I_sq, h]; ring
  have hfac : (Complex.sqrt y * Complex.sqrt z - I * Complex.sqrt w) *
      (Complex.sqrt y * Complex.sqrt z + I * Complex.sqrt w) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact sub_eq_zero.mp h1
  · exfalso
    have him := congrArg Complex.im h1
    simp only [add_im, mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, zero_im] at him
    have := sqrt_re_pos hy
    have := sqrt_im_pos hy
    have := sqrt_re_pos hz
    have := sqrt_im_pos hz
    have := sqrt_re_pos hw
    nlinarith

/-- Mathlib's inversion law, pointwise. -/
theorem eta_neg_inv {z : ℂ} (hz : 0 < z.im) :
    η (-1 / z) = (Complex.sqrt I)⁻¹ * Complex.sqrt z * η z := by
  have h := eta_comp_eq_csqrt_I_inv (show z ∈ upperHalfPlaneSet from hz)
  simp only [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h
  rw [h, mul_assoc]

/-- **`η(z / (n z + 1)) = e^{−π i n / 12} √(n z + 1) η(z)`** for `n ≥ 1`, `Im z > 0`. -/
theorem eta_lower (n : ℕ) (hn : 0 < n) {z : ℂ} (hz : 0 < z.im) :
    η (z / (n * z + 1)) = cexp (-(π * I * n / 12)) * Complex.sqrt (n * z + 1) * η z := by
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set u : ℂ := -1 / z with hu
  have hui : 0 < u.im := by
    rw [hu, neg_div, neg_im, div_im]; simp only [one_re, one_im, zero_mul, zero_div, zero_sub,
      one_mul, neg_neg]
    exact div_pos hz (Complex.normSq_pos.mpr hz0)
  set y : ℂ := u + ((-(n : ℤ) : ℤ) : ℂ) with hy
  have hyi : 0 < y.im := by rw [hy]; simpa using hui
  have hy0 : y ≠ 0 := fun h0 => by simp [h0] at hyi
  have hw : 0 < ((n : ℂ) * z + 1).im := by simpa using mul_pos hn' hz
  have hw0 : (n : ℂ) * z + 1 ≠ 0 := fun h0 => by simp [h0] at hw
  have hyz : y * z = -((n : ℂ) * z + 1) := by
    rw [hy, hu]; simp only [Int.cast_neg, Int.cast_natCast]; field_simp; ring
  clear_value u y
  have harg : z / (n * z + 1) = -1 / y := by
    rw [div_eq_div_iff hw0 hy0]; linear_combination hyz
  rw [harg, eta_neg_inv hyi, hy, eta_add_int, ← hy, hu, eta_neg_inv hz]
  have hb := sqrt_mul_branch hyi hz hw hyz
  have hI : Complex.sqrt I ^ 2 = I := sqrt_sq' I
  have hI0 : Complex.sqrt I ≠ 0 := fun h0 => by rw [h0] at hI; simp at hI; exact I_ne_zero hI.symm
  have e : (Complex.sqrt I)⁻¹ * Complex.sqrt y *
      (cexp (π * I * ((-(n : ℤ) : ℤ) : ℂ) / 12) * ((Complex.sqrt I)⁻¹ * Complex.sqrt z * η z)) =
      cexp (π * I * ((-(n : ℤ) : ℤ) : ℂ) / 12) * (Complex.sqrt y * Complex.sqrt z) /
        Complex.sqrt I ^ 2 * η z := by
    field_simp
  rw [e, hb, hI]
  have : cexp (π * I * ((-(n : ℤ) : ℤ) : ℂ) / 12) = cexp (-(π * I * n / 12)) := by
    congr 1; push_cast; ring
  rw [this]
  field_simp [I_ne_zero]

end ZInQ.CdOpt.EtaW32Proof
