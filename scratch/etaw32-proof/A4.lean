import ZInQKernel.Contrib.OneProof.CdOptimal.Level32

noncomputable section

open Complex ModularForm CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

open ZInQ.Contrib.TYZGenus

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

/-- `η(δ γ τ)` for `γ = (a b; 32 d)` with `n δ = 32`, `a = nα + 1`, `d = nβ + 1`. -/
theorem etaD_c32 (n δ : ℕ) (hnδ : n * δ = 32) (hn : 0 < n) {a b d α β : ℤ}
    (ha : a = n * α + 1) (hd : d = n * β + 1) (hdet : a * d - b * 32 = 1) {τ : ℂ}
    (hτ : 0 < τ.im) :
    X0.etaD δ ((a * τ + b) / (32 * τ + d)) =
      cexp (π * I * (α + β - n) / 12) * Complex.sqrt (32 * τ + d) * X0.etaD δ τ := by
  have hδ : 0 < δ := by
    rcases Nat.eq_zero_or_pos δ with h | h
    · rw [h] at hnδ; simp at hnδ
    · exact h
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hnδc : (n : ℂ) * δ = 32 := by exact_mod_cast hnδ
  set z : ℂ := δ * τ + β with hz
  have hzi : 0 < z.im := by rw [hz]; simpa using mul_pos hδ' hτ
  have hw : (n : ℂ) * z + 1 = 32 * τ + d := by
    rw [hz, hd]; push_cast; linear_combination τ * hnδc
  have hwi : 0 < ((32 : ℂ) * τ + d).im := by simpa using mul_pos (by norm_num : (0 : ℝ) < 32) hτ
  have hw0 : (32 : ℂ) * τ + d ≠ 0 := fun h0 => by simp [h0] at hwi
  have hb : (δ : ℂ) * b = n * α * β + α + β := by
    have hdet' : (a : ℂ) * d - b * 32 = 1 := by exact_mod_cast hdet
    rw [ha, hd] at hdet'
    push_cast at hdet'
    linear_combination ((n * α * β + α + β : ℂ) / 32) * hnδc - ((δ : ℂ) / 32) * hdet'
  have hkey : (δ : ℂ) * ((a * τ + b) / (32 * τ + d)) = z / (n * z + 1) + (α : ℂ) := by
    rw [hw, mul_div_assoc', div_add' _ _ _ hw0]
    congr 1
    rw [hz, ha, hd]
    push_cast
    linear_combination (α * τ) * hnδc + hb
  unfold X0.etaD
  rw [hkey, eta_add_int, eta_lower n hn hzi, hw, hz, eta_add_int]
  rw [show cexp (π * I * α / 12) * (cexp (-(π * I * n / 12)) * Complex.sqrt (32 * τ + d) *
      (cexp (π * I * β / 12) * η (δ * τ))) =
      (cexp (π * I * α / 12) * cexp (-(π * I * n / 12)) * cexp (π * I * β / 12)) *
        Complex.sqrt (32 * τ + d) * η (δ * τ) by ring]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 3
  ring

/-- `v(γτ) = e^{π i (A + B)/4} v(τ)` for `γ = (4A+1, b; 32, 4B+1)`. -/
theorem vC_c32 {a b d A B : ℤ} (ha : a = 4 * A + 1) (hd : d = 4 * B + 1)
    (hdet : a * d - b * 32 = 1) (τ : ℍ) :
    vC ((a * (τ : ℂ) + b) / (32 * τ + d)) = cexp (π * I * (A + B) / 4) * vC τ := by
  have h8 := etaD_c32 4 8 (by norm_num) (by norm_num) (α := A) (β := B) (by rw [ha]; push_cast; ring)
    (by rw [hd]; push_cast; ring) hdet τ.im_pos
  have h16 := etaD_c32 2 16 (by norm_num) (by norm_num) (α := 2 * A) (β := 2 * B)
    (by rw [ha]; push_cast; ring) (by rw [hd]; push_cast; ring) hdet τ.im_pos
  have h32 := etaD_c32 1 32 (by norm_num) (by norm_num) (α := 4 * A) (β := 4 * B)
    (by rw [ha]; push_cast; ring) (by rw [hd]; push_cast; ring) hdet τ.im_pos
  unfold vC
  rw [h8, h16, h32]
  set s := Complex.sqrt (32 * (τ : ℂ) + d)
  have hwi : 0 < ((32 : ℂ) * τ + d).im := by
    simpa using mul_pos (by norm_num : (0 : ℝ) < 32) τ.im_pos
  have hs : s ≠ 0 := by
    intro h0
    have h := sqrt_sq' (32 * (τ : ℂ) + d)
    change s ^ 2 = _ at h
    rw [h0] at h
    rw [← h] at hwi; simp at hwi
  have hE16 := X0.etaD_ne_zero (d := 16) (by norm_num) τ
  have hexp : cexp (π * I * ((A : ℂ) + B - ((4 : ℕ) : ℂ)) / 12) *
      cexp (π * I * (((4 * A : ℤ) : ℂ) + ((4 * B : ℤ) : ℂ) - ((1 : ℕ) : ℂ)) / 12) ^ 2 =
      cexp (π * I * (A + B) / 4) *
        cexp (π * I * (((2 * A : ℤ) : ℂ) + ((2 * B : ℤ) : ℂ) - ((2 : ℕ) : ℂ)) / 12) ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have he16 : cexp (π * I * (((2 * A : ℤ) : ℂ) + ((2 * B : ℤ) : ℂ) - ((2 : ℕ) : ℂ)) / 12) ≠ 0 :=
    Complex.exp_ne_zero _
  field_simp
  linear_combination (X0.etaD 8 τ * X0.etaD 32 τ ^ 2) * hexp

/-- `e^{π i (A + B)/4} = χ₈(4B + 1)` when `(4A+1)(4B+1) ≡ 1 (mod 32)`. -/
theorem exp_eq_chi8 {A B b : ℤ} (hdet : (4 * A + 1) * (4 * B + 1) - b * 32 = 1) :
    cexp (π * I * (A + B) / 4) = ((ZMod.χ₈ (((4 * B + 1 : ℤ)) : ZMod 8) : ℤ) : ℂ) := by
  have h' : 16 * (A * B) + 4 * A + 4 * B - 32 * b = 0 := by linear_combination hdet
  have hAB : A + B = 4 * (2 * b - A * B) := by omega
  set m := 2 * b - A * B with hm
  have he : cexp (π * I * (A + B) / 4) = (-1 : ℂ) ^ m := by
    have : π * I * ((A : ℂ) + B) / 4 = (m : ℂ) * (π * I) := by
      have : ((A : ℂ) + B) = 4 * m := by exact_mod_cast hAB
      rw [this]; ring
    rw [this, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rw [he, ZMod.χ₈_int_eq_if_mod_eight]
  rcases Int.even_or_odd B with hB | hB
  · have hA : Even A := by
      have : Even (A + B) := ⟨2 * m, by omega⟩
      exact (Int.even_add.mp this).mpr hB
    have hmE : Even m := by
      rw [hm]; exact (even_two_mul b).sub (hA.mul_right B)
    rw [hmE.neg_one_zpow]
    obtain ⟨k, hk⟩ := hB
    have h1 : (4 * B + 1) % 2 ≠ 0 := by omega
    have h2 : (4 * B + 1) % 8 = 1 ∨ (4 * B + 1) % 8 = 7 := by omega
    simp [h1, h2]
  · have hA : Odd A := by
      have : Even (A + B) := ⟨2 * m, by omega⟩
      rcases Int.even_or_odd A with hA | hA
      · exact absurd ((Int.even_add.mp this).mp hA) (Int.not_even_iff_odd.mpr hB)
      · exact hA
    have hmO : Odd m := by
      rw [hm]; exact (even_two_mul b).sub_odd (hA.mul hB)
    rw [hmO.neg_one_zpow]
    obtain ⟨k, hk⟩ := hB
    have h1 : (4 * B + 1) % 2 ≠ 0 := by omega
    have h2 : ¬((4 * B + 1) % 8 = 1 ∨ (4 * B + 1) % 8 = 7) := by omega
    simp [h1, h2]

/-! ## The group-theoretic reduction -/

/-- The statement of `EtaW32Character` for one matrix. -/
def P (γ : SL(2, ℤ)) : Prop :=
  ∀ τ : ℍ, vC ((γ • τ : ℍ) : ℂ) = ((ZMod.χ₈ ((γ 1 1 : ℤ) : ZMod 8) : ℤ) : ℂ) * vC τ

theorem coe_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ • τ : ℍ) : ℂ) = ((γ 0 0 : ℂ) * τ + γ 0 1) / ((γ 1 0 : ℂ) * τ + γ 1 1) := by
  rw [coe_specialLinearGroup_apply]; simp

theorem det_entries (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := γ.det_coe; rwa [Matrix.det_fin_two] at h

theorem mul_10 (g γ : SL(2, ℤ)) : (g * γ) 1 0 = g 1 0 * γ 0 0 + g 1 1 * γ 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_11 (g γ : SL(2, ℤ)) : (g * γ) 1 1 = g 1 0 * γ 0 1 + g 1 1 * γ 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem chi8_ne_zero {d : ℤ} (hd : d % 2 = 1) : ((ZMod.χ₈ ((d : ℤ) : ZMod 8) : ℤ) : ℂ) ≠ 0 := by
  rw [ZMod.χ₈_int_eq_if_mod_eight]
  have h1 : d % 2 ≠ 0 := by omega
  simp only [h1, ite_false]
  split_ifs <;> norm_num

theorem chi8_neg (d : ℤ) : ZMod.χ₈ (((-d : ℤ)) : ZMod 8) = ZMod.χ₈ ((d : ℤ) : ZMod 8) := by
  rw [ZMod.χ₈_int_eq_if_mod_eight, ZMod.χ₈_int_eq_if_mod_eight]
  have h2 : (-d) % 2 = 0 ↔ d % 2 = 0 := by omega
  have h8 : ((-d) % 8 = 1 ∨ (-d) % 8 = 7) ↔ (d % 8 = 1 ∨ d % 8 = 7) := by omega
  simp only [h2, h8]

theorem P_neg {γ : SL(2, ℤ)} (h : P γ) : P (-γ) := by
  intro τ
  rw [ModularGroup.SL_neg_smul, h τ]
  have e : (-γ) 1 1 = -(γ 1 1) := by simp
  rw [e, chi8_neg]

theorem chi8_mul_of_dvd {c b d d' : ℤ} (hc : (8 : ℤ) ∣ c) :
    ZMod.χ₈ (((c * b + d * d' : ℤ)) : ZMod 8) =
      ZMod.χ₈ ((d : ℤ) : ZMod 8) * ZMod.χ₈ ((d' : ℤ) : ZMod 8) := by
  have : ((c : ℤ) : ZMod 8) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd c 8).mpr (by exact_mod_cast hc)
  push_cast
  rw [this, zero_mul, zero_add, map_mul]

/-- `P g`, `P (g γ)` imply `P γ`, for `8 ∣ g₁₀` and `g₁₁` odd. -/
theorem P_cancel {g γ : SL(2, ℤ)} (hc : (8 : ℤ) ∣ g 1 0) (hd : g 1 1 % 2 = 1) (hg : P g)
    (hgγ : P (g * γ)) : P γ := by
  intro τ
  have h1 := hgγ τ
  rw [mul_smul, hg, mul_11, chi8_mul_of_dvd hc] at h1
  push_cast at h1
  exact mul_left_cancel₀ (chi8_ne_zero hd) (by rw [h1]; ring)

theorem P_one : P 1 := by
  intro τ; simp

theorem P_inv {g : SL(2, ℤ)} (hc : (8 : ℤ) ∣ g 1 0) (hd : g 1 1 % 2 = 1) (hg : P g) : P g⁻¹ :=
  P_cancel hc hd hg (by rw [mul_inv_cancel]; exact P_one)

theorem P_c32_one_mod_four {γ : SL(2, ℤ)} (hc : γ 1 0 = 32) (ha : γ 0 0 % 4 = 1) : P γ := by
  intro τ
  have hdet := det_entries γ
  rw [hc] at hdet
  obtain ⟨A, hA⟩ : ∃ A, γ 0 0 = 4 * A + 1 := ⟨γ 0 0 / 4, by omega⟩
  have hd4 : 4 * (A * γ 1 1) + γ 1 1 - 32 * γ 0 1 = 1 := by rw [hA] at hdet; linear_combination hdet
  obtain ⟨B, hB⟩ : ∃ B, γ 1 1 = 4 * B + 1 := ⟨γ 1 1 / 4, by omega⟩
  rw [coe_smul, hc, Int.cast_ofNat]
  rw [vC_c32 hA hB hdet τ, hB, ← exp_eq_chi8 (b := γ 0 1)]
  rw [← hA, ← hB]; exact hdet

theorem P_c32 {γ : SL(2, ℤ)} (hc : γ 1 0 = 32) : P γ := by
  have hdet := det_entries γ
  rw [hc] at hdet
  have ha : γ 0 0 % 2 = 1 := by
    have : γ 0 0 * γ 1 1 % 2 = 1 := by omega
    rcases Int.emod_two_eq_zero_or_one (γ 0 0) with h | h
    · exfalso; rw [Int.mul_emod, h, zero_mul] at this; simp at this
    · exact h
  rcases (show γ 0 0 % 4 = 1 ∨ γ 0 0 % 4 = 3 by omega) with h4 | h4
  · exact P_c32_one_mod_four hc h4
  · -- `−γ⁻¹ = (−d, b; 32, −a)` with `−d ≡ 1 (mod 4)`
    obtain ⟨A, hA⟩ : ∃ A, γ 0 0 = 4 * A + 3 := ⟨γ 0 0 / 4, by omega⟩
    have hd4 : 4 * (A * γ 1 1) + 3 * γ 1 1 - 32 * γ 0 1 = 1 := by
      rw [hA] at hdet; linear_combination hdet
    have hinv10 : (-γ⁻¹) 1 0 = 32 := by
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two]; simp [hc]
    have hinv00 : (-γ⁻¹) 0 0 = -γ 1 1 := by
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two]; simp
    have h1 : P (-γ⁻¹) := P_c32_one_mod_four hinv10 (by rw [hinv00]; omega)
    have h2 : P γ⁻¹ := by simpa using P_neg h1
    have hi10 : γ⁻¹ 1 0 = -32 := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp [hc]
    have hi11 : γ⁻¹ 1 1 = γ 0 0 := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp
    simpa using P_inv (g := γ⁻¹) (by rw [hi10]; norm_num) (by rw [hi11]; exact ha) h2

theorem P_c32_abs {γ : SL(2, ℤ)} (hc : γ 1 0 = 32 ∨ γ 1 0 = -32) : P γ := by
  rcases hc with hc | hc
  · exact P_c32 hc
  · have h : P (-γ) := P_c32 (by simp [hc])
    simpa using P_neg h

end ZInQ.CdOpt.EtaW32Proof
