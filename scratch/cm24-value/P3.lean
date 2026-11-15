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

/-- `U` with characteristic reduced mod `ℤ²`. -/
def Uf (s0 s1 : ℕ) : ℂ := U (((s0 % 2 : ℕ) : ℝ) / 2) (((s1 % 2 : ℕ) : ℝ) / 2)

theorem U_nat (s0 s1 : ℕ) : U ((s0 : ℝ) / 2) ((s1 : ℝ) / 2) = Uf s0 s1 := by
  rw [Uf, U, U]
  conv_rhs => rw [← th2_shift_c _ _ _ _ _ _ _ ((s0 / 2 : ℕ) : ℤ) ((s1 / 2 : ℕ) : ℤ)]
  simp only [Int.cast_natCast]
  have h0 : (s0 : ℝ) = ((s0 % 2 : ℕ) : ℝ) + 2 * ((s0 / 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div s0 2).symm
  have h1 : (s1 : ℝ) = ((s1 % 2 : ℕ) : ℝ) + 2 * ((s1 / 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div s1 2).symm
  congr 1 <;> linarith

theorem exp_pi_nat (k : ℕ) : cexp (π * I * (k : ℂ)) = (-1) ^ k := by
  rw [mul_comm, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-- **Duplication at `W`, with the translation reductions.** -/
theorem sqW (a0 a1 b0 b1 : ℕ) :
    Th2 wa wb wc ((b0 : ℝ) / 2) ((b1 : ℝ) / 2) ((a0 : ℝ) / 2) ((a1 : ℝ) / 2) ^ 2 =
      ∑ σ : Fin 2 × Fin 2, (-1 : ℂ) ^ (((σ.1 : ℕ) + b0) * a0 + ((σ.2 : ℕ) + b1) * a1) *
        Uf ((σ.1 : ℕ) + b0) ((σ.2 : ℕ) + b1) * Uf σ.1 σ.2 := by
  rw [dup2 _ _ _ _ (summable_norm_term2 d2pos posW _ _ _ _)
    (fun _ _ _ _ => summable_norm_term2 d3pos posW2 _ _ _ _)]
  congr 1; funext σ
  have e0 : 2 * ((a0 : ℝ) / 2) = 0 + ((a0 : ℤ) : ℝ) := by push_cast; ring
  have e1 : 2 * ((a1 : ℝ) / 2) = 0 + ((a1 : ℤ) : ℝ) := by push_cast; ring
  rw [e0, e1, th2_shift_d]
  have c0 : ((σ.1 : ℕ) : ℝ) / 2 + (b0 : ℝ) / 2 = (((σ.1 : ℕ) + b0 : ℕ) : ℝ) / 2 := by push_cast; ring
  have c1 : ((σ.2 : ℕ) : ℝ) / 2 + (b1 : ℝ) / 2 = (((σ.2 : ℕ) + b1 : ℕ) : ℝ) / 2 := by push_cast; ring
  rw [c0, c1]
  change _ * U _ _ * U _ _ = _
  rw [U_nat, U_nat, ← exp_pi_nat]
  congr 2
  congr 1; push_cast; ring

theorem om24_sym : Om24 1 0 = Om24 0 1 := by rw [om24_10, om24_01]

theorem sq_char (m : HDec.PkgI1.Char2) :
    HDec.PkgI1.thetaConst m Om24 ^ 2 =
      Ecal * cexp (π * I * (((m.1 0 : ℕ) * (m.2 0 : ℕ) + (m.1 1 : ℕ) * (m.2 1 : ℕ) : ℕ) : ℂ)) *
      ∑ σ : Fin 2 × Fin 2, (-1 : ℂ) ^ (((σ.1 : ℕ) + (m.2 0 : ℕ)) * (m.1 0 : ℕ) + ((σ.2 : ℕ) + (m.2 1 : ℕ)) * (m.1 1 : ℕ)) *
        Uf ((σ.1 : ℕ) + (m.2 0 : ℕ)) ((σ.2 : ℕ) + (m.2 1 : ℕ)) * Uf σ.1 σ.2 := by
  rw [thetaConst_eq m Om24 om24_sym, om24_00, om24_01, om24_11, sq_inv, sqW]

theorem U11' : U (1 / 2) (1 / 2) = 0 := U11
theorem U11'' : U 2⁻¹ 2⁻¹ = 0 := by rw [← one_div]; exact U11

theorem exp_pi_two : cexp (π * I * 2) = 1 := by
  rw [show (π : ℂ) * I * 2 = ((1 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring, exp_int_mul_two_pi_mul_I]

theorem sqc0 : HDec.PkgI1.thetaConst (![0, 0], ![0, 0]) Om24 ^ 2 =
    Ecal * (U 0 0 ^ 2 + U (1 / 2) 0 ^ 2 + U 0 (1 / 2) ^ 2) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc1 : HDec.PkgI1.thetaConst (![0, 1], ![0, 0]) Om24 ^ 2 =
    Ecal * (U 0 0 ^ 2 + U (1 / 2) 0 ^ 2 - U 0 (1 / 2) ^ 2) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc2 : HDec.PkgI1.thetaConst (![1, 0], ![0, 0]) Om24 ^ 2 =
    Ecal * (U 0 0 ^ 2 - U (1 / 2) 0 ^ 2 + U 0 (1 / 2) ^ 2) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc3 : HDec.PkgI1.thetaConst (![1, 1], ![0, 0]) Om24 ^ 2 =
    Ecal * (U 0 0 ^ 2 - U (1 / 2) 0 ^ 2 - U 0 (1 / 2) ^ 2) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc4 : HDec.PkgI1.thetaConst (![0, 0], ![1, 0]) Om24 ^ 2 =
    Ecal * (2 * U 0 0 * U (1 / 2) 0) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc5 : HDec.PkgI1.thetaConst (![0, 1], ![1, 0]) Om24 ^ 2 =
    Ecal * (2 * U 0 0 * U (1 / 2) 0) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc6 : HDec.PkgI1.thetaConst (![0, 0], ![0, 1]) Om24 ^ 2 =
    Ecal * (2 * U 0 0 * U 0 (1 / 2)) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc7 : HDec.PkgI1.thetaConst (![1, 0], ![0, 1]) Om24 ^ 2 =
    Ecal * (2 * U 0 0 * U 0 (1 / 2)) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc8 : HDec.PkgI1.thetaConst (![0, 0], ![1, 1]) Om24 ^ 2 =
    Ecal * (2 * U 0 (1 / 2) * U (1 / 2) 0) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc9 : HDec.PkgI1.thetaConst (![1, 1], ![1, 1]) Om24 ^ 2 =
    Ecal * (-(2 * U 0 (1 / 2) * U (1 / 2) 0)) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

/-! ## Genus one: duplication (Landen) and Jacobi's identity -/

theorem th1_c1 (τ : ℂ) (d : ℝ) : th1 τ 1 d = th1 τ 0 d := by
  simpa using th1_shift_c τ 0 d 1

theorem th1_d1 (τ : ℂ) (c : ℝ) : th1 τ c 1 = cexp (2 * π * I * c) * th1 τ c 0 := by
  simpa using th1_shift_d τ c 0 1

theorem exp_half : cexp (2 * π * I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
  rw [show (2 : ℂ) * π * I * ((1 / 2 : ℝ) : ℂ) = π * I by push_cast; ring, Complex.exp_pi_mul_I]

theorem dupA {τ : ℂ} (hτ : 0 < τ.im) :
    th1 τ 0 0 ^ 2 = th1 (2 * τ) 0 0 ^ 2 + th1 (2 * τ) (1 / 2) 0 ^ 2 := by
  rw [dup1 hτ, Fin.sum_univ_two]; norm_num; ring

theorem dupB {τ : ℂ} (hτ : 0 < τ.im) :
    th1 τ 0 (1 / 2) ^ 2 = th1 (2 * τ) 0 0 ^ 2 - th1 (2 * τ) (1 / 2) 0 ^ 2 := by
  rw [dup1 hτ, Fin.sum_univ_two]
  have e : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  simp only [e, th1_d1, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_div, zero_add,
    add_zero, exp_half]
  push_cast; simp only [mul_zero, Complex.exp_zero]; ring

theorem dupC {τ : ℂ} (hτ : 0 < τ.im) :
    th1 τ (1 / 2) 0 ^ 2 = 2 * th1 (2 * τ) 0 0 * th1 (2 * τ) (1 / 2) 0 := by
  rw [dup1 hτ, Fin.sum_univ_two]
  have e : (1 : ℝ) / 2 + 1 / 2 = 1 := by norm_num
  simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_div, zero_add, mul_zero, e, th1_c1]
  ring

/-- **Jacobi's quartic identity** `θ₀₀⁴ = θ₀₁⁴ + θ₁₀⁴`, from the duplication formulas. -/
theorem jacobi {τ : ℂ} (hτ : 0 < τ.im) :
    th1 τ 0 0 ^ 4 = th1 τ 0 (1 / 2) ^ 4 + th1 τ (1 / 2) 0 ^ 4 := by
  have hA := dupA hτ; have hB := dupB hτ; have hC := dupC hτ
  linear_combination (th1 τ 0 0 ^ 2 + th1 (2 * τ) 0 0 ^ 2 + th1 (2 * τ) (1 / 2) 0 ^ 2) * hA
    - (th1 τ 0 (1 / 2) ^ 2 + th1 (2 * τ) 0 0 ^ 2 - th1 (2 * τ) (1 / 2) 0 ^ 2) * hB
    - (th1 τ (1 / 2) 0 ^ 2 + 2 * th1 (2 * τ) 0 0 * th1 (2 * τ) (1 / 2) 0) * hC

theorem h2τ3 : 2 * τ3 = τ6 := by apply Complex.ext <;> simp [τ3, τ6] <;> ring

end CM24
