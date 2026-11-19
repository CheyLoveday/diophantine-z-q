import ZInQKernel.Contrib.OneProof.RC.Even.EvenSource
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Curve

/-! The period normalization on the fixed complementary twist (tex 10288–10314). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenReading

open ZInQ.Manuscript.RC.Even ZInQ.Contrib.CloudB3RC53

/-- Transport the central values by sending `h` to `h * k`. A negative twist swaps the
two signs of the periods, and both absolute periods are divided by `√|k|`. -/
def transportedNormalization {E : WeierstrassCurve ℚ} (C : CentralNormalization E)
    {k : ℤ} (hk : k < 0) : CentralNormalization (qtwist E (k : ℚ)) where
  Ωp := C.Ωm / Real.sqrt |(k : ℝ)|
  Ωm := C.Ωp / Real.sqrt |(k : ℝ)|
  Ωp_pos := div_pos C.Ωm_pos (Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast hk.ne)))
  Ωm_pos := div_pos C.Ωp_pos (Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast hk.ne)))
  Lstar h := C.Lstar (h * k)
  anchor h hh F hF := by
    have hF' : IsLContinuation (qtwist E ((h * k : ℤ) : ℚ)) F := by
      push_cast
      rw [← Nonvanishing.qtwist_qtwist]
      exact hF
    have hs : Real.sqrt |((h * k : ℤ) : ℝ)| =
        Real.sqrt |(h : ℝ)| * Real.sqrt |(k : ℝ)| := by
      rw [Int.cast_mul, abs_mul, Real.sqrt_mul (abs_nonneg _)]
    rw [C.anchor _ (mul_ne_zero hh hk.ne) F hF', hs, Complex.ofReal_mul]
    by_cases hp : 0 < h
    · have hneg : ¬ 0 < h * k := (mul_neg_of_pos_of_neg hp hk).not_gt
      rw [ite_eq_right hneg, ite_eq_left hp, Complex.ofReal_div]
      rw [div_div_eq_mul_div]
      ring
    · have hn : h < 0 := lt_of_le_of_ne (le_of_not_gt hp) hh
      rw [ite_eq_left (mul_pos_of_neg_of_neg hn hk), ite_eq_right hp, Complex.ofReal_div]
      rw [div_div_eq_mul_div]
      ring

end ZInQ.Manuscript.RC.EvenReading
