import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.Cd
import ZInQKernel.Contrib.GZStatements.Level
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Cusps.Basic

noncomputable section

open UpperHalfPlane WeierstrassCurve ZInQ.GZDecomp CongruenceSubgroup
open ZInQ.Contrib.HeckeFE
open Matrix.GeneralLinearGroup (upperRightHom)
open scoped MatrixGroups ZMod

namespace ZInQ.GZWeil

/-! ## §1. The Eichler integral of the theta series of `ψ_d` -/

/-- `Φ_d(τ) = Σ_{n ≥ 1} heckeCoeff d n / n · e^{2πinτ}`: the Eichler integral `2πi ∫_{i∞}^τ f_d`
of the theta series `f_d = Σ heckeCoeff d n qⁿ` of the Hecke character `ψ_d` of `C_d`. -/
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

theorem summable_eichler_term (d : ℕ) {z : ℂ} (hz : 0 < z.im) :
    Summable fun n : ℕ => heckeCoeff d (n + 1) / ((n : ℂ) + 1) *
      Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z) := by
  set r : ℝ := Real.exp (-2 * Real.pi * z.im) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
  have hS : Summable fun n : ℕ => ((2 * (n : ℝ) + 3) ^ 3) * r ^ n := by
    have h0 := summable_pow_mul_geometric_of_norm_lt_one 0 (r := r) (by
      rw [Real.norm_of_nonneg hr0]; exact hr1)
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r) (by
      rw [Real.norm_of_nonneg hr0]; exact hr1)
    have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 (r := r) (by
      rw [Real.norm_of_nonneg hr0]; exact hr1)
    have h3 := summable_pow_mul_geometric_of_norm_lt_one 3 (r := r) (by
      rw [Real.norm_of_nonneg hr0]; exact hr1)
    have := (((h3.mul_left 8).add (h2.mul_left 36)).add (h1.mul_left 54)).add (h0.mul_left 27)
    refine this.congr fun n => ?_
    ring
  refine Summable.of_norm_bounded hS fun n => ?_
  rw [norm_mul, norm_div]
  have he : ‖Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z)‖ = r ^ (n + 1) := by
    rw [Complex.norm_exp, hr, ← Real.exp_nat_mul]
    congr 1
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.natCast_re,
      Complex.natCast_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
    push_cast
    ring
  have hn1 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_natCast]; push_cast; ring
  rw [he, hn1]
  have hb := norm_heckeCoeff_le d (n + 1)
  push_cast at hb
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  have hrn : r ^ (n + 1) ≤ r ^ n := pow_le_pow_of_le_one hr0 hr1.le (Nat.le_succ n)
  calc ‖heckeCoeff d (n + 1)‖ * r ^ (n + 1) ≤ (2 * ((n : ℝ) + 1) + 1) ^ 3 * r ^ n := by
        gcongr
    _ ≤ (2 * (n : ℝ) + 3) ^ 3 * r ^ n * ((n : ℝ) + 1) := by
        have : (2 * ((n : ℝ) + 1) + 1) = 2 * (n : ℝ) + 3 := by ring
        rw [this]
        have : 0 ≤ (2 * (n : ℝ) + 3) ^ 3 * r ^ n := by positivity
        nlinarith

/-! ## §2. The twist formula `d Φ_d(z) = Σ_a 𝓕χ(a) Φ₁(z + a/d)` -/

open ZInQ.GZTheta (jacobiChar jacobiChar_natCast heckeCoeff_eq_jacobiSym_mul)

/-- Fourier inversion on `ZMod d`: `Σ_a 𝓕Φ(a) e(ak/d) = d Φ(k)`. -/
theorem sum_dft_mul_stdAddChar (d : ℕ) [NeZero d] (Φ : ZMod d → ℂ) (k : ZMod d) :
    ∑ a : ZMod d, 𝓕 Φ a * ZMod.stdAddChar (a * k) = (d : ℂ) * Φ k := by
  have h := ZMod.invDFT_apply (𝓕 Φ) k
  rw [LinearEquiv.symm_apply_apply] at h
  rw [h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast NeZero.ne d), one_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_eq_mul, mul_comm]

theorem exp_translate (d : ℕ) [NeZero d] (a : ZMod d) (m : ℕ) (z : ℂ) :
    Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (z + (a.val : ℂ) / d)) =
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * z) * ZMod.stdAddChar (a * (m : ZMod d)) := by
  have hcast : (a * (m : ZMod d)) = (((a.val * m : ℕ) : ℤ) : ZMod d) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [hcast, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The twist formula for Eichler integrals**: `d Φ_d(z) = Σ_{a mod d} 𝓕χ_d(a) Φ₁(z + a/d)`,
with `χ_d = (·/d)` (Tau Ceti's `twist_apply`, one level up: `Φ_d` is the Eichler integral of
`f₁ ⊗ χ_d`). -/
theorem twist_formula (d : ℕ) [NeZero d] {z : ℂ} (hz : 0 < z.im) :
    (d : ℂ) * eichlerCd d z =
      ∑ a : ZMod d, 𝓕 (jacobiChar d) a * eichlerCd 1 (z + (a.val : ℂ) / d) := by
  have hz' : ∀ a : ZMod d, 0 < (z + (a.val : ℂ) / d).im := fun a => by
    have : ((a.val : ℂ) / d).im = 0 := by
      rw [show ((a.val : ℂ) / d) = (((a.val : ℝ) / d : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_im _
    rw [Complex.add_im, this, add_zero]; exact hz
  simp only [eichlerCd]
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun a _ => (summable_eichler_term 1 (hz' a)).mul_left _]
  congr 1
  funext n
  have key := sum_dft_mul_stdAddChar d (jacobiChar d) ((n + 1 : ℕ) : ZMod d)
  rw [jacobiChar_natCast] at key
  have e1 : ∀ a : ZMod d, 𝓕 (jacobiChar d) a *
      (heckeCoeff 1 (n + 1) / ((n : ℂ) + 1) *
        Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * (z + (a.val : ℂ) / d))) =
      (heckeCoeff 1 (n + 1) / ((n : ℂ) + 1) * Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z))
        * (𝓕 (jacobiChar d) a * ZMod.stdAddChar (a * ((n + 1 : ℕ) : ZMod d))) := by
    intro a
    have := exp_translate d a (n + 1) z
    rw [show (((n + 1 : ℕ)) : ℂ) = (n : ℂ) + 1 by push_cast; ring] at this
    rw [this]; ring
  rw [Finset.sum_congr rfl fun a _ => e1 a, ← Finset.mul_sum, key,
    heckeCoeff_eq_jacobiSym_mul d (n + 1)]
  push_cast
  ring

/-! ## §3. The periods of `Φ_d` over `Γ₀(32 d²)` through the periods of `Φ₁` over `Γ₀(32)` -/

open ZInQ.GZTheta (jacobiChar_sq_unit dvd_level_left dvd_level_right)
open Matrix.SpecialLinearGroup (mapGL)

/-- `𝓕χ(a u) = 𝓕χ(a)` for a unit `u` with `χ(u⁻¹) = 1`. -/
theorem dft_mul_unit (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (u : (ZMod d)ˣ)
    (hu : χ (u⁻¹ : (ZMod d)ˣ) = 1) (a : ZMod d) : 𝓕 χ (a * u) = 𝓕 χ a := by
  have h := ZMod.dft_comp_unitMul (⇑χ) u⁻¹ a
  rw [inv_inv] at h
  have hf : (fun j => χ ((u⁻¹ : (ZMod d)ˣ).val * j)) = ⇑χ := by
    funext j; rw [map_mul, hu, one_mul]
  rw [hf] at h
  rw [h, mul_comm]

/-- **The period identity.** For `γ ∈ Γ₀(32 d²)` and `τ ∈ ℍ` there are `γ'_a ∈ Γ₀(32)` and
`τ'_a ∈ ℍ` (`a ∈ ℤ/d`) with
`d (Φ_d(γτ) − Φ_d(τ)) = Σ_a 𝓕χ_d(a) (Φ₁(γ'_a τ'_a) − Φ₁(τ'_a))`: move `[1, a/d; 0, 1]` past `γ`
(Tau Ceti `exists_upperRightHom_mul_mapGL_eq_mapGL_mul_upperRightHom`) and reindex `a ↦ a D²`. -/
theorem period_identity (d : ℕ) [NeZero d] {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (32 * d ^ 2))
    (τ : ℍ) :
    ∃ (γ' : ZMod d → SL(2, ℤ)) (τ' : ZMod d → ℍ), (∀ a, γ' a ∈ Gamma0 32) ∧
      (d : ℂ) * (eichlerCd d ((γ • τ : ℍ) : ℂ) - eichlerCd d (τ : ℂ)) =
        ∑ a : ZMod d, 𝓕 (jacobiChar d) a *
          (eichlerCd 1 ((γ' a • τ' a : ℍ) : ℂ) - eichlerCd 1 (τ' a : ℂ)) := by
  obtain ⟨c, hc, -⟩ := CongruenceSubgroup.exists_eq_mul_mul_of_mem_Gamma0
    (dvd_level_left d) (dvd_level_right d) hγ
  set D : ZMod d := ((γ 1 1 : ℤ) : ZMod d) with hDdef
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  have hAD : ((γ 0 0 : ℤ) : ZMod d) * D = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod d) hdet
    push_cast [hc, ZMod.natCast_self] at this
    simpa [hDdef] using this
  have hD : IsUnit D := IsUnit.of_mul_eq_one_right _ hAD
  set w : (ZMod d)ˣ := hD.unit with hw
  set v : (ZMod d)ˣ := w ^ 2 with hv
  have hvD : (v : ZMod d) = D ^ 2 := by simp [hv, hw]
  have hχv : jacobiChar d ((v⁻¹ : (ZMod d)ˣ) : ZMod d) = 1 := by
    rw [hv, ← inv_pow, Units.val_pow_eq_pow_val, map_pow]
    exact jacobiChar_sq_unit d _
  have hex : ∀ a : ZMod d, ∃ γ' : SL(2, ℤ), γ' 0 0 = γ 0 0 + (a.val : ℤ) * d * c ∧
      γ' 1 0 = γ 1 0 ∧ γ' 1 1 = γ 1 1 - (((a * D ^ 2).val : ℕ) : ℤ) * d * c ∧
      upperRightHom (((a.val : ℤ) : ℝ) / d) * mapGL ℝ γ =
        mapGL ℝ γ' * upperRightHom (((((a * D ^ 2).val : ℕ) : ℤ) : ℝ) / d) := fun a =>
    TauCeti.exists_upperRightHom_mul_mapGL_eq_mapGL_mul_upperRightHom γ hc (by
      rw [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val])
  choose γ' hγ'0 hγ'1 hγ'2 hγ'eq using hex
  set τ' : ZMod d → ℍ := fun a => ((((((a * D ^ 2).val : ℕ) : ℤ) : ℝ) / d) +ᵥ τ) with hτ'
  refine ⟨γ', τ', fun a => ?_, ?_⟩
  · rw [mem_Gamma0_iff_dvd, hγ'1]
    have := (mem_Gamma0_iff_dvd.mp hγ)
    exact (Int.natCast_dvd_natCast.mpr (dvd_mul_right 32 (d ^ 2))).trans (by exact_mod_cast this)
  -- the translate of `γ τ` by `a/d` is `γ'_a τ'_a`
  have hmove : ∀ a : ZMod d, ((γ • τ : ℍ) : ℂ) + (a.val : ℂ) / d = ((γ' a • τ' a : ℍ) : ℂ) := by
    intro a
    have h := congrArg (fun g : GL (Fin 2) ℝ => g • τ) (hγ'eq a)
    simp only [mul_smul, TauCeti.Matrix.GeneralLinearGroup.upperRightHom_smul] at h
    have h' := congrArg (fun z : ℍ => (z : ℂ)) h
    simp only [UpperHalfPlane.coe_vadd] at h'
    rw [ModularGroup.sl_moeb, ModularGroup.sl_moeb, TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
      TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← h']
    push_cast
    ring
  have hz : 0 < ((γ • τ : ℍ) : ℂ).im := (γ • τ).im_pos
  rw [mul_sub, twist_formula d hz, twist_formula d τ.im_pos, ← Finset.sum_sub_distrib]
  -- reindex the second sum by `b = a D²`
  have hre : ∑ b : ZMod d, 𝓕 (jacobiChar d) b * eichlerCd 1 ((τ : ℂ) + (b.val : ℂ) / d) =
      ∑ a : ZMod d, 𝓕 (jacobiChar d) a * eichlerCd 1 ((τ' a : ℍ) : ℂ) := by
    refine (Fintype.sum_equiv (Units.mulRight v) _ _ fun a => ?_).symm
    simp only [Units.mulRight_apply, hτ', UpperHalfPlane.coe_vadd]
    rw [dft_mul_unit d (jacobiChar d) v hχv a, hvD]
    congr 2
    push_cast
    ring
  rw [Finset.sum_sub_distrib, hre, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hmove a, mul_sub]

end ZInQ.GZWeil
