import ZInQKernel.Contrib.TYZGenus.ShimuraThetaDup
import ZInQKernel.Contrib.GZTheta.EtaForm32
import ZInQKernel.Contrib.GZTheta.EtaTheta

noncomputable section

open UpperHalfPlane CongruenceSubgroup Complex
open ZInQ.Contrib.HeckeFE
open scoped MatrixGroups

namespace ZInQ.GZWeil

/-! ## Copy of the Eichler integral (as in `Twist.lean`) -/

def eichlerCd (d : ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, heckeCoeff d (n + 1) / ((n : ℂ) + 1) *
    Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z)

theorem norm_unitOf_le (t : ZMod 4 × ZMod 4) : ‖unitOf t‖ ≤ 1 := by
  unfold unitOf
  split_ifs <;> simp

theorem norm_jacobiSym_le (a : ℤ) (b : ℕ) : ‖(jacobiSym a b : ℂ)‖ ≤ 1 := by
  rcases jacobiSym.trichotomy a b with h | h | h <;> simp [h]

theorem norm_heckeCoeff_le (d m : ℕ) : ‖heckeCoeff d m‖ ≤ (2 * m + 1) ^ 3 := by
  unfold heckeCoeff
  have hcard : ((normFiber m).card : ℝ) ≤ (2 * m + 1) ^ 2 := by
    have : (normFiber m).card ≤ (2 * m + 1) ^ 2 := by
      unfold normFiber
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_product, Int.card_Icc]
      have : ((m : ℤ) + 1 - -(m : ℤ)).toNat = 2 * m + 1 := by omega
      rw [this, sq]
    exact_mod_cast this
  have hterm : ∀ p ∈ normFiber m,
      ‖(jacobiSym (p.1 ^ 2 + p.2 ^ 2) d : ℂ) * unitOf ((p.1 : ZMod 4), (p.2 : ZMod 4)) *
        gz 0 0 p‖ ≤ 2 * m + 1 := by
    intro p hp
    have hp' := mem_normFiber.mp hp
    rw [norm_mul, norm_mul]
    have h1 := norm_jacobiSym_le (p.1 ^ 2 + p.2 ^ 2) d
    have h2 := norm_unitOf_le ((p.1 : ZMod 4), (p.2 : ZMod 4))
    have h3 : ‖gz 0 0 p‖ ≤ 2 * m + 1 := by
      have hg : gz 0 0 p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by simp [gz]
      rw [hg]
      have hn : ‖((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ ≤ |(p.1 : ℝ)| + |(p.2 : ℝ)| := by
        refine (norm_add_le _ _).trans ?_
        simp [Complex.norm_intCast]
      have hb1 : |(p.1 : ℝ)| ≤ m := by
        have : |p.1| ≤ m := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2, sq_abs p.1]
        exact_mod_cast this
      have hb2 : |(p.2 : ℝ)| ≤ m := by
        have : |p.2| ≤ m := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2, sq_abs p.2]
        exact_mod_cast this
      linarith
    calc ‖(jacobiSym (p.1 ^ 2 + p.2 ^ 2) d : ℂ)‖ * ‖unitOf ((p.1 : ZMod 4), (p.2 : ZMod 4))‖ *
          ‖gz 0 0 p‖ ≤ 1 * 1 * (2 * m + 1) := by gcongr
      _ = 2 * m + 1 := by ring
  rw [norm_mul]
  calc ‖(1 / 4 : ℂ)‖ * ‖∑ p ∈ normFiber m, (jacobiSym (p.1 ^ 2 + p.2 ^ 2) d : ℂ) *
        unitOf ((p.1 : ZMod 4), (p.2 : ZMod 4)) * gz 0 0 p‖
      ≤ 1 * ((normFiber m).card * (2 * m + 1)) := by
        gcongr
        · norm_num
        · refine (norm_sum_le _ _).trans ?_
          have := Finset.sum_le_card_nsmul _ _ _ hterm
          rwa [nsmul_eq_mul] at this
    _ ≤ 1 * ((2 * m + 1) ^ 2 * (2 * m + 1)) := by gcongr
    _ = (2 * m + 1) ^ 3 := by ring

theorem norm_exp_term (n : ℕ) (z : ℂ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z)‖ =
      Real.exp (-2 * Real.pi * z.im) ^ (n + 1) := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.natCast_re,
    Complex.natCast_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  ring

theorem summable_poly_geom {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => ((2 * (n : ℝ) + 3) ^ 3) * r ^ n := by
  have hn : ‖r‖ < 1 := by rw [Real.norm_of_nonneg hr0]; exact hr1
  have h0 := summable_pow_mul_geometric_of_norm_lt_one 0 hn
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hn
  have h3 := summable_pow_mul_geometric_of_norm_lt_one 3 hn
  have := (((h3.mul_left 8).add (h2.mul_left 36)).add (h1.mul_left 54)).add (h0.mul_left 27)
  refine this.congr fun n => ?_
  ring

/-! ## C1. `Φ₁' = 2πi f₁` on `ℍ` -/

theorem hasDerivAt_eichler_term (n : ℕ) (z : ℂ) :
    HasDerivAt (fun w => heckeCoeff 1 (n + 1) / ((n : ℂ) + 1) *
      Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * w))
      (heckeCoeff 1 (n + 1) * (2 * Real.pi * Complex.I) *
        Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z)) z := by
  have hn : ((n : ℂ) + 1) ≠ 0 := by
    have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast Nat.succ_ne_zero n
  have h1 : HasDerivAt (fun w => 2 * Real.pi * Complex.I * ((n : ℂ) + 1) * w)
      (2 * Real.pi * Complex.I * ((n : ℂ) + 1)) z := by
    simpa using (hasDerivAt_id z).const_mul (2 * Real.pi * Complex.I * ((n : ℂ) + 1))
  have h2 := (h1.cexp).const_mul (heckeCoeff 1 (n + 1) / ((n : ℂ) + 1))
  convert h2 using 1
  field_simp

/-- **`Φ₁'(τ) = 2πi f₁(τ)`**, `f₁ = η(4τ)²η(8τ)²` (termwise differentiation and gz-theta's
`etaThetaIdentity`). -/
theorem hasDerivAt_eichlerCd_one {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (eichlerCd 1) (2 * Real.pi * Complex.I * ZInQ.Contrib.TYZGenus.X0.fC z) z := by
  set ε := z.im / 2 with hε
  have hε0 : 0 < ε := by positivity
  set r : ℝ := Real.exp (-2 * Real.pi * ε) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
  set t : Set ℂ := {w | ε < w.im} with ht
  have htopen : IsOpen t := isOpen_lt continuous_const Complex.continuous_im
  have htconv : Convex ℝ t := convex_halfSpace_im_gt ε
  have hzt : z ∈ t := by show ε < z.im; linarith
  have hbound : ∀ (n : ℕ) (w : ℂ), w ∈ t →
      ‖heckeCoeff 1 (n + 1) * (2 * Real.pi * Complex.I) *
        Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * w)‖ ≤
        2 * Real.pi * ((2 * (n : ℝ) + 3) ^ 3 * r ^ n) := by
    intro n w hw
    rw [norm_mul, norm_mul, norm_exp_term]
    have hb := norm_heckeCoeff_le 1 (n + 1)
    push_cast at hb
    have h2pi : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      simp [abs_of_pos Real.pi_pos]
    rw [h2pi]
    have hexp : Real.exp (-2 * Real.pi * w.im) ^ (n + 1) ≤ r ^ n := by
      have h1 : Real.exp (-2 * Real.pi * w.im) ≤ r := by
        rw [hr]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, show ε < w.im from hw])
      calc Real.exp (-2 * Real.pi * w.im) ^ (n + 1) ≤ r ^ (n + 1) :=
            pow_le_pow_left₀ (Real.exp_pos _).le h1 _
        _ ≤ r ^ n := pow_le_pow_of_le_one hr0 hr1.le (Nat.le_succ n)
    have : (2 * ((n : ℝ) + 1) + 1) = 2 * (n : ℝ) + 3 := by ring
    rw [this] at hb
    calc ‖heckeCoeff 1 (n + 1)‖ * (2 * Real.pi) * Real.exp (-2 * Real.pi * w.im) ^ (n + 1)
        ≤ (2 * (n : ℝ) + 3) ^ 3 * (2 * Real.pi) * r ^ n := by gcongr
      _ = _ := by ring
  have hsum0 : Summable fun n : ℕ => heckeCoeff 1 (n + 1) / ((n : ℂ) + 1) *
      Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z) := by
    refine Summable.of_norm_bounded ((summable_poly_geom hr0 hr1).mul_left (2 * Real.pi)) ?_
    intro n
    have h := hbound n z hzt
    rw [norm_mul, norm_mul] at h
    rw [norm_mul, norm_div]
    have hn1 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]; push_cast; ring
    have h2pi : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      simp [abs_of_pos Real.pi_pos]
    rw [h2pi] at h
    rw [hn1]
    have hpos : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hA : 0 ≤ ‖heckeCoeff 1 (n + 1)‖ * ‖Complex.exp (2 * Real.pi * Complex.I *
        ((n : ℂ) + 1) * z)‖ := by positivity
    calc ‖heckeCoeff 1 (n + 1)‖ / ((n : ℝ) + 1) *
          ‖Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z)‖
        ≤ ‖heckeCoeff 1 (n + 1)‖ * ‖Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z)‖ := by
          rw [div_mul_eq_mul_div]
          exact div_le_self hA hpos
      _ ≤ ‖heckeCoeff 1 (n + 1)‖ * (2 * Real.pi) *
          ‖Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z)‖ := by
          nlinarith
      _ ≤ _ := h
  have hD := hasDerivAt_tsum_of_isPreconnected
    ((summable_poly_geom hr0 hr1).mul_left (2 * Real.pi)) htopen htconv.isPreconnected
    (fun n w _ => hasDerivAt_eichler_term n w) hbound hzt hsum0 hzt
  convert hD using 1
  · rfl
  -- the derivative series is `2πi f₁(z)`
  set τ : ℍ := ⟨z, hz⟩
  have hf := ZInQ.GZTheta.etaThetaIdentity τ
  rw [← hasSum_nat_add_iff' 1] at hf
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one] at hf
  have h0 : heckeCoeff 1 0 = 0 := by
    simp [heckeCoeff, normFiber, gz, Finset.sum_filter]
  rw [h0, sub_zero] at hf
  have hfC : ZInQ.Contrib.TYZGenus.X0.fC z = ModularForm.eta (4 * (τ : ℂ)) ^ 2 * ModularForm.eta (8 * (τ : ℂ)) ^ 2 := rfl
  rw [hfC, ← hf.tsum_eq, ← tsum_mul_left]
  congr 1
  funext n
  rw [← Complex.exp_nat_mul]
  push_cast
  ring_nf
  rfl

end ZInQ.GZWeil
