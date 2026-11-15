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

end ZInQ.GZWeil

#print axioms ZInQ.GZWeil.thetaFour_S_sq
#print axioms ZInQ.GZWeil.thetaFour_add_one
