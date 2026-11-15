import Mathlib

/-! gt-gamma: the hyperbolic area of the triangle `T` (calculus part). -/

noncomputable section

namespace HDec.GammaStarArea.AreaCalc

open Real

/-- `L = 1 + √2`, `k = 9 + 6√2`. -/
def LL : ℝ := 1 + √2
def kk : ℝ := 9 + 6 * √2

/-- `h(x) = 1/√(3 + 6|x| − x²) − 1/√(k − x²)`: the `y`-integral of `dy/y²` over the vertical section of `T`. -/
def hc (x : ℝ) : ℝ := 1 / √(3 + 6 * |x| - x ^ 2) - 1 / √(kk - x ^ 2)

theorem s2_sq : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
theorem s3_sq : √3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
theorem s2_pos : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
theorem s3_pos : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
theorem s2_lt : √2 < (3 / 2 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num
theorem s2_gt : (1 : ℝ) < √2 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem LL_pos : 0 < LL := by unfold LL; linarith [s2_pos]
theorem LL_lt : LL < 3 := by unfold LL; linarith [s2_lt]

theorem kk_sub_pos {x : ℝ} (hx : |x| ≤ LL) : 0 < kk - x ^ 2 := by
  have h1 : x ^ 2 ≤ LL ^ 2 := by
    have := abs_nonneg x
    calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ LL ^ 2 := by gcongr
  unfold kk; unfold LL at h1; nlinarith [s2_sq, s2_pos]

theorem lo_pos {x : ℝ} (hx : |x| ≤ LL) : 0 < 3 + 6 * |x| - x ^ 2 := by
  have h0 := abs_nonneg x
  have h1 := LL_lt
  have : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  nlinarith

theorem hc_neg (x : ℝ) : hc (-x) = hc x := by simp [hc, abs_neg]

theorem hc_cont : ContinuousOn hc (Set.Icc (-LL) LL) := by
  intro x hx
  have hx' : |x| ≤ LL := abs_le.2 hx
  apply ContinuousAt.continuousWithinAt
  unfold hc
  apply ContinuousAt.sub
  · apply ContinuousAt.div continuousAt_const (by fun_prop)
    exact (Real.sqrt_pos.2 (lo_pos hx')).ne'
  · apply ContinuousAt.div continuousAt_const (by fun_prop)
    exact (Real.sqrt_pos.2 (kk_sub_pos hx')).ne'

/-- `√k = √3 (1 + √2)`. -/
theorem sqrt_kk : √kk = √3 * LL := by
  have : kk = (√3 * LL) ^ 2 := by
    unfold kk LL; rw [mul_pow, s3_sq]; nlinarith [s2_sq]
  rw [this, Real.sqrt_sq (by have := s3_pos; have := LL_pos; positivity)]

theorem arcsin_sqrt3_half : arcsin (√3 / 2) = π / 3 := by
  rw [← Real.sin_pi_div_three, Real.arcsin_sin] <;> linarith [Real.pi_pos]

/-- `arcsin((√2 − 2)/(2√3)) = arcsin(1/√3) − π/4`. -/
theorem arcsin_key : arcsin ((√2 - 2) / (2 * √3)) = arcsin (1 / √3) - π / 4 := by
  set a := arcsin (1 / √3)
  have h3 := s3_pos
  have hb : 1 / √3 ≤ 1 := by
    rw [div_le_one h3]; rw [Real.le_sqrt' one_pos]; norm_num
  have hb' : -1 ≤ 1 / √3 := by linarith [show (0 : ℝ) ≤ 1 / √3 by positivity]
  have hsa : sin a = 1 / √3 := Real.sin_arcsin hb' hb
  have hca : cos a = √(1 - (1 / √3) ^ 2) := Real.cos_arcsin _
  have hc2 : √(1 - (1 / √3) ^ 2) = √2 / √3 := by
    rw [show 1 - (1 / √3) ^ 2 = 2 / 3 by rw [div_pow, s3_sq]; norm_num, Real.sqrt_div' 2 (by norm_num : (0:ℝ) ≤ 3)]
  have hsin : sin (a - π / 4) = (√2 - 2) / (2 * √3) := by
    rw [Real.sin_sub, hsa, hca, hc2, Real.cos_pi_div_four, Real.sin_pi_div_four]
    field_simp
    nlinarith [s2_sq]
  have ha0 : 0 ≤ a := Real.arcsin_nonneg.2 (by positivity)
  have ha1 : a ≤ π / 2 := Real.arcsin_le_pi_div_two _
  rw [← hsin, Real.arcsin_sin] <;> linarith [Real.pi_pos]

theorem hasDerivAt_F {x : ℝ} (hx0 : 0 ≤ x) (hxL : x ≤ LL) :
    HasDerivAt (fun x => arcsin ((x - 3) / (2 * √3)) - arcsin (x / √kk)) (hc x) x := by
  have h3 := s3_pos
  have hk := kk_sub_pos (x := x) (by rw [abs_of_nonneg hx0]; exact hxL)
  have hk0 : 0 < kk := by unfold kk; linarith [s2_pos]
  have hsk : 0 < √kk := Real.sqrt_pos.2 hk0
  have hL3 := LL_lt
  -- the arguments stay in `(-1, 1)`
  have hu1 : -1 < (x - 3) / (2 * √3) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [s3_sq, Real.sqrt_nonneg 3, show (3 / 2 : ℝ) < √3 by rw [Real.lt_sqrt (by norm_num)]; norm_num]
  have hu2 : (x - 3) / (2 * √3) < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  have hv1 : -1 < x / √kk := by
    have : 0 ≤ x / √kk := by positivity
    linarith
  have hv2 : x / √kk < 1 := by
    rw [div_lt_one hsk, Real.lt_sqrt hx0]; linarith
  have hu : HasDerivAt (fun x : ℝ => (x - 3) / (2 * √3)) (1 / (2 * √3)) x :=
    ((hasDerivAt_id x).sub_const 3).div_const _
  have hv : HasDerivAt (fun x : ℝ => x / √kk) (1 / √kk) x := (hasDerivAt_id x).div_const _
  have hA := (Real.hasDerivAt_arcsin hu1.ne' hu2.ne).comp x hu
  have hB := (Real.hasDerivAt_arcsin hv1.ne' hv2.ne).comp x hv
  refine (hA.sub hB).congr_deriv ?_
  unfold hc
  rw [abs_of_nonneg hx0]
  congr 1
  · have hw : 0 ≤ 1 - ((x - 3) / (2 * √3)) ^ 2 := by nlinarith
    have e : √(1 - ((x - 3) / (2 * √3)) ^ 2) * (2 * √3) = √(3 + 6 * x - x ^ 2) := by
      have hsq : (√(1 - ((x - 3) / (2 * √3)) ^ 2) * (2 * √3)) ^ 2 = 3 + 6 * x - x ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hw, mul_pow, div_pow, mul_pow, s3_sq]; field_simp; ring
      rw [← hsq, Real.sqrt_sq (by positivity)]
    rw [← e]; field_simp
  · have hw : 0 ≤ 1 - (x / √kk) ^ 2 := by nlinarith
    have e : √(1 - (x / √kk) ^ 2) * √kk = √(kk - x ^ 2) := by
      have hsq : (√(1 - (x / √kk) ^ 2) * √kk) ^ 2 = kk - x ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hw, div_pow, Real.sq_sqrt hk0.le]; field_simp
      rw [← hsq, Real.sqrt_sq (by positivity)]
    rw [← e]; field_simp

theorem integral_half : ∫ x in (0 : ℝ)..LL, hc x = π / 12 := by
  have hL := LL_pos
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => arcsin ((x - 3) / (2 * √3)) - arcsin (x / √kk))]
  · simp only [zero_sub, zero_div, Real.arcsin_zero, sub_zero]
    have e1 : (-3) / (2 * √3) = -(√3 / 2) := by
      have := s3_pos; field_simp; nlinarith [s3_sq]
    have e2 : LL / √kk = 1 / √3 := by
      rw [sqrt_kk]; have := s3_pos; field_simp
    have e3 : (LL - 3) / (2 * √3) = (√2 - 2) / (2 * √3) := by unfold LL; ring_nf
    rw [e1, e2, e3, Real.arcsin_neg, arcsin_sqrt3_half, arcsin_key]
    ring
  · intro x hx
    rw [Set.uIcc_of_le hL.le] at hx
    exact hasDerivAt_F hx.1 hx.2
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hL.le]
    exact hc_cont.mono (Set.Icc_subset_Icc (by linarith) le_rfl)

theorem integral_full : ∫ x in (-LL)..LL, hc x = π / 6 := by
  have hL := LL_pos
  have hi1 : IntervalIntegrable hc MeasureTheory.volume (-LL) 0 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    exact hc_cont.mono (Set.Icc_subset_Icc le_rfl (by linarith))
  have hi2 : IntervalIntegrable hc MeasureTheory.volume 0 LL := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hL.le]
    exact hc_cont.mono (Set.Icc_subset_Icc (by linarith) le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, integral_half]
  have : ∫ x in (-LL)..0, hc x = ∫ x in (0 : ℝ)..LL, hc x := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := LL) hc
    simp only [neg_zero, hc_neg] at h
    exact h.symm
  rw [this, integral_half]; ring

end HDec.GammaStarArea.AreaCalc
