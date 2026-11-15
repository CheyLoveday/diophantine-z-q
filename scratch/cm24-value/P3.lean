namespace CM24
open HDec.LeafQCheck.HM.QMSplit.Value24

/-! ## Bridge to `PkgI1.thetaConst` -/

theorem thetaConst_eq (m : HDec.PkgI1.Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hΩ : Ω 1 0 = Ω 0 1) :
    HDec.PkgI1.thetaConst m Ω = Th2 (Ω 0 0) (Ω 0 1) (Ω 1 1) (((m.1 0 : ℕ) : ℝ) / 2) (((m.1 1 : ℕ) : ℝ) / 2)
      (((m.2 0 : ℕ) : ℝ) / 2) (((m.2 1 : ℕ) : ℝ) / 2) := by
  rw [HDec.PkgI1.thetaConst, Th2, ← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  congr 1; funext p
  simp only [finTwoArrowEquiv_symm_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, term2,
    Matrix.cons_val_zero, Matrix.cons_val_one, hΩ]
  congr 1; push_cast; ring

theorem om24_00 : Om24 0 0 = α0 := by
  apply Complex.ext <;> simp [Om24, α0] <;> ring
theorem om24_01 : Om24 0 1 = β0 := by
  apply Complex.ext <;> simp [Om24, β0] <;> ring
theorem om24_10 : Om24 1 0 = β0 := by
  apply Complex.ext <;> simp [Om24, β0] <;> ring
theorem om24_11 : Om24 1 1 = γ0 := by
  apply Complex.ext <;> simp [Om24, γ0] <;> ring


/-! ## Squares of theta constants at `Ω₂₄` in terms of `U` -/

/-- `𝓔 = 1/((−iα0)(−iγ1))`: the square of the two automorphy factors. -/
def Ecal : ℂ := 1 / (-I * α0) * (1 / (-I * γ1))

theorem cpow_half_sq (x : ℂ) : (1 / x ^ (1 / 2 : ℂ)) ^ 2 = 1 / x := by
  rw [div_pow, one_pow, show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num, Complex.cpow_nat_inv_pow x two_ne_zero]

theorem sq_inv (a0 a1 b0 b1 : ℕ) :
    Th2 α0 β0 γ0 ((a0 : ℝ) / 2) ((a1 : ℝ) / 2) ((b0 : ℝ) / 2) ((b1 : ℝ) / 2) ^ 2 =
      Ecal * cexp (π * I * ((a0 * b0 + a1 * b1 : ℕ) : ℂ)) *
        Th2 wa wb wc ((b0 : ℝ) / 2) ((b1 : ℝ) / 2) ((a0 : ℝ) / 2) ((a1 : ℝ) / 2) ^ 2 := by
  have h := invert (a0 : ℝ) (a1 : ℝ) (b0 : ℤ) (b1 : ℤ)
  simp only [Int.cast_natCast] at h
  have e1 : cexp (2 * π * I * ((a0 : ℝ) / 2 : ℝ) * ((b0 : ℝ) / 2 : ℝ)) ^ 2 *
      cexp (2 * π * I * ((a1 : ℝ) / 2 : ℝ) * ((b1 : ℝ) / 2 : ℝ)) ^ 2 =
      cexp (π * I * ((a0 * b0 + a1 * b1 : ℕ) : ℂ)) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [h]
  simp only [mul_pow]
  rw [cpow_half_sq, cpow_half_sq, ← e1, Ecal]
  ring

end CM24
