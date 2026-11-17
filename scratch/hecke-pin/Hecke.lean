import ZInQKernel.Contrib.OneProof.HeckePin

noncomputable section
namespace AfTateLam.HeckePin
open PkgI4 (CF coeff)
open Function UpperHalfPlane Real
open scoped MatrixGroups ModularForm
local notation "Iℂ" => Complex.I
local notation "𝕢" => Function.Periodic.qParam

variable {N : ℕ}

/-- `Σ_{j<p} e^{2πi n (τ+j)/p} = p e^{2πi (n/p) τ}` if `p ∣ n`, else `0`. -/
theorem sum_exp_shift (p : ℕ) (hp : 0 < p) (n : ℕ) (τ : ℂ) :
    ∑ j ∈ Finset.range p, Complex.exp (2 * π * Iℂ * n * ((τ + j) / p)) =
      if p ∣ n then (p : ℂ) * Complex.exp (2 * π * Iℂ * (n / p : ℕ) * τ) else 0 := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hsplit : ∀ j : ℕ, Complex.exp (2 * π * Iℂ * n * ((τ + j) / p)) =
      Complex.exp (2 * π * Iℂ * n * τ / p) * Complex.exp (2 * π * Iℂ * n / p) ^ j := by
    intro j
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; field_simp
  simp_rw [hsplit, ← Finset.mul_sum]
  split_ifs with hdvd
  · obtain ⟨m, rfl⟩ := hdvd
    have h1 : Complex.exp (2 * π * Iℂ * ((p * m : ℕ) : ℂ) / p) = 1 := by
      rw [Complex.exp_eq_one_iff]; exact ⟨m, by push_cast; field_simp⟩
    rw [h1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [Nat.mul_div_cancel_left _ hp]
    rw [mul_comm]; congr 2; push_cast; field_simp
  · have hne : Complex.exp (2 * π * Iℂ * n / p) ≠ 1 := by
      rw [Ne, Complex.exp_eq_one_iff]
      rintro ⟨k, hk⟩
      apply hdvd
      have hk' : (n : ℂ) = k * p := by
        have h2 : (2 * π * Iℂ : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
        field_simp at hk
        linear_combination hk
      have : (n : ℤ) = k * p := by exact_mod_cast hk'
      have : (p : ℤ) ∣ n := ⟨k, by rw [this]; ring⟩
      exact_mod_cast this
    rw [geom_sum_eq hne, ← Complex.exp_nat_mul]
    have : Complex.exp (p * (2 * π * Iℂ * n / p)) = 1 := by
      rw [Complex.exp_eq_one_iff]; exact ⟨n, by push_cast; field_simp⟩
    rw [this]; simp

end AfTateLam.HeckePin
