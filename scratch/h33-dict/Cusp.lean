import ZInQKernel.Contrib.TYZGenus.ShimuraCusp

/-! h33-dict, part C (dev file): the pole structure of x0-32's `x` at the cusps of `Γ₀(32)`. -/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.H33Dict

open Complex Filter Topology
open UpperHalfPlane hiding I
open scoped MatrixGroups

/-- `gcd(δ, c)` for the lower-left entry `c` of `γ`. -/
abbrev gδ (δ : ℕ) (γ : SL(2, ℤ)) : ℕ := Nat.gcd δ (γ 1 0).natAbs

/-- `Shimura.exists_smul_decomp` with the exact imaginary part: `δ·γτ = γ'w`, `δ·Im w = gcd(δ, c)²·Im τ`. -/
theorem exists_smul_decomp_exact {δ : ℕ} (hδ : 0 < δ) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ∃ (γ' : SL(2, ℤ)) (w : UpperHalfPlane), (δ : ℂ) * ((γ • τ : UpperHalfPlane) : ℂ) =
      ((γ' • w : UpperHalfPlane) : ℂ) ∧ w.im * δ = ((gδ δ γ : ℕ) : ℝ) ^ 2 * τ.im := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact this
  obtain ⟨p, u, s, v, g, t, e, hB, hp, hpt, hs, hst, hg0, he0, hge⟩ :=
    Shimura.exists_hermite (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) δ hdet (by exact_mod_cast hδ)
  have hgval : g = ((gδ δ γ : ℕ) : ℤ) := by
    have h1 : Int.gcd p s = 1 := Int.isCoprime_iff_gcd_eq_one.1 ⟨v, -u, by linear_combination hB⟩
    have h2 : Int.gcd (γ 0 0) (γ 1 0) = 1 :=
      Int.isCoprime_iff_gcd_eq_one.1 ⟨γ 1 1, -γ 0 1, by linear_combination hdet⟩
    have h3 : Int.gcd ((δ : ℤ) * γ 0 0) (γ 1 0) = Int.gcd (p * g) (s * g) := by rw [hp, hs]
    rw [Int.gcd_mul_right, h1, one_mul] at h3
    have h4 : Int.gcd ((δ : ℤ) * γ 0 0) (γ 1 0) = Nat.gcd δ (γ 1 0).natAbs := by
      show Nat.gcd ((δ : ℤ) * γ 0 0).natAbs (γ 1 0).natAbs = _
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.Coprime.gcd_mul_right_cancel δ h2
    rw [h3] at h4
    rw [gδ, ← h4, Int.natAbs_of_nonneg hg0.le]
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
  have heR : (0 : ℝ) < e := by exact_mod_cast he0
  have hgeR : (g : ℝ) * e = δ := by exact_mod_cast hge
  have hwim : 0 < (((g : ℂ) * τ + t) / e).im := by
    have : (((g : ℂ) * τ + t) / e).im = g * τ.im / e := by
      rw [show (e : ℂ) = ((e : ℝ) : ℂ) by simp, Complex.div_ofReal_im]
      simp
    rw [this]; have := τ.im_pos; positivity
  let w : UpperHalfPlane := ⟨((g : ℂ) * τ + t) / e, hwim⟩
  have hwim' : w.im = g * τ.im / e := by
    show (((g : ℂ) * τ + t) / e).im = _
    rw [show (e : ℂ) = ((e : ℝ) : ℂ) by simp, Complex.div_ofReal_im]
    simp
  let γ' : SL(2, ℤ) := ⟨!![p, u; s, v], by rw [Matrix.det_fin_two_of]; exact hB⟩
  refine ⟨γ', w, ?_, ?_⟩
  · rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
    simp only [γ', Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      algebraMap_int_eq, eq_intCast, Int.cast_id]
    have hden : ((γ 1 0 : ℝ) : ℂ) * τ + ((γ 1 1 : ℝ) : ℂ) ≠ 0 := by
      have := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
      simpa [ModularGroup.denom_apply] using this
    have heC : (e : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
    have h1 : ((p : ℝ) : ℂ) * (w : ℂ) + ((u : ℝ) : ℂ) =
        δ * (((γ 0 0 : ℝ) : ℂ) * τ + ((γ 0 1 : ℝ) : ℂ)) / e := by
      show ((p : ℝ) : ℂ) * (((g : ℂ) * τ + t) / e) + ((u : ℝ) : ℂ) = _
      field_simp
      have hp' : (p : ℂ) * g = δ * γ 0 0 := by exact_mod_cast hp
      have hpt' : (p : ℂ) * t + u * e = δ * γ 0 1 := by exact_mod_cast hpt
      push_cast
      linear_combination (τ : ℂ) * hp' + hpt'
    have h2 : ((s : ℝ) : ℂ) * (w : ℂ) + ((v : ℝ) : ℂ) =
        (((γ 1 0 : ℝ) : ℂ) * τ + ((γ 1 1 : ℝ) : ℂ)) / e := by
      show ((s : ℝ) : ℂ) * (((g : ℂ) * τ + t) / e) + ((v : ℝ) : ℂ) = _
      field_simp
      have hs' : (s : ℂ) * g = γ 1 0 := by exact_mod_cast hs
      have hst' : (s : ℂ) * t + v * e = γ 1 1 := by exact_mod_cast hst
      push_cast
      linear_combination (τ : ℂ) * hs' + hst'
    rw [h1, h2]
    field_simp
  · have hg' : (g : ℝ) = ((gδ δ γ : ℕ) : ℝ) := by rw [hgval]; push_cast; rfl
    rw [hwim', ← hgeR, ← hg']
    field_simp

/-- `|η(δγτ)|⁴·δ·Im(γτ) = H(w)` with `δ·Im w = gcd(δ, c)²·Im τ`. -/
theorem etaD_norm_exact {δ : ℕ} (hδ : 0 < δ) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ∃ w : UpperHalfPlane, ‖X0.etaD δ ((γ • τ : UpperHalfPlane) : ℂ)‖ ^ 4 * (δ * (γ • τ).im) =
      Shimura.Hinv w ∧ w.im * δ = ((gδ δ γ : ℕ) : ℝ) ^ 2 * τ.im := by
  obtain ⟨γ', w, hw, h1⟩ := exists_smul_decomp_exact hδ γ τ
  refine ⟨w, ?_, h1⟩
  rw [← Shimura.Hinv_smul γ' w]
  unfold Shimura.Hinv X0.etaD
  rw [hw]
  congr 1
  have := congrArg Complex.im hw
  simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero] at this
  exact this

/-- `H(w) = e^{−π Im w/3}·P(w)·Im w` with `m ≤ P(w) ≤ M` for `Im w ≥ 1` (`P = |∏(1 − qⁿ)|⁴`). -/
theorem Hinv_exact :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ w : UpperHalfPlane, 1 ≤ w.im → ∃ P : ℝ, m ≤ P ∧ P ≤ M ∧
      Shimura.Hinv w = Real.exp (-(Real.pi * w.im / 3)) * P * w.im := by
  obtain ⟨m, M, hm, hM, hb⟩ := Shimura.exists_prodF_bounds
  refine ⟨m ^ 4, M ^ 4, by positivity, by positivity, fun w hw => ?_⟩
  obtain ⟨h1, h2⟩ := hb _ (Shimura.norm_q_le w hw)
  refine ⟨‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4, pow_le_pow_left₀ hm.le h1 4,
    pow_le_pow_left₀ (norm_nonneg _) h2 4, ?_⟩
  unfold Shimura.Hinv
  rw [Shimura.eta_eq_prodF, norm_mul, mul_pow, Shimura.norm_qParam24_pow4]

/-- The exponent `32·S(c) = 32g₂² + 2g₁₆² − 8g₄² − 2g₃₂²` of `|x(γτ) − 2|⁴` (Ligozat's order formula). -/
def expS (γ : SL(2, ℤ)) : ℝ :=
  32 * ((gδ 2 γ : ℕ) : ℝ) ^ 2 + 2 * ((gδ 16 γ : ℕ) : ℝ) ^ 2 - 8 * ((gδ 4 γ : ℕ) : ℝ) ^ 2 -
    2 * ((gδ 32 γ : ℕ) : ℝ) ^ 2


theorem gratio_le {a b c d : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 2) (hb : 0 ≤ b) (hb2 : b ≤ 16)
    (hc : 1 ≤ c) (hd : 1 ≤ d) : ((a ^ 2) ^ 2 * b ^ 2) / (c ^ 2 * (d ^ 2) ^ 2) ≤ 4096 := by
  have a1 : (a ^ 2) ^ 2 ≤ 16 := by
    have := pow_le_pow_left₀ ha ha2 4
    calc (a ^ 2) ^ 2 = a ^ 4 := by ring
      _ ≤ 2 ^ 4 := this
      _ = 16 := by norm_num
  have a2 : b ^ 2 ≤ 256 := by
    have := pow_le_pow_left₀ hb hb2 2
    calc b ^ 2 ≤ 16 ^ 2 := this
      _ = 256 := by norm_num
  have hn : (a ^ 2) ^ 2 * b ^ 2 ≤ 4096 :=
    (mul_le_mul a1 a2 (by positivity) (by norm_num)).trans (by norm_num)
  have h1 : 1 ≤ c ^ 2 * (d ^ 2) ^ 2 := by
    have e1 : 1 ≤ c ^ 2 := one_le_pow₀ hc
    have e2 : 1 ≤ (d ^ 2) ^ 2 := one_le_pow₀ (one_le_pow₀ hd)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ c ^ 2 * (d ^ 2) ^ 2 := mul_le_mul e1 e2 zero_le_one (by positivity)
  calc ((a ^ 2) ^ 2 * b ^ 2) / (c ^ 2 * (d ^ 2) ^ 2) ≤ ((a ^ 2) ^ 2 * b ^ 2) / 1 :=
        div_le_div_of_nonneg_left (by positivity) one_pos h1
    _ ≤ 4096 := by rw [div_one]; exact hn

/-- **`|x(γτ) − 2|⁴ ≤ K·e^{−π Im τ·S(γ)/96}`** for `Im τ ≥ 32`, uniformly in `γ ∈ SL₂(ℤ)` (`S = expS γ`). -/
theorem xC_sub_two_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane), 32 ≤ τ.im →
    ‖X0.xC ((γ • τ : UpperHalfPlane) : ℂ) - 2‖ ^ 4 ≤
      K * Real.exp (-(Real.pi * τ.im * expS γ / 96)) := by
  obtain ⟨m, M, hm, hM, hb⟩ := Hinv_exact
  refine ⟨64 * M ^ 3 / m ^ 3 * 64 * 4096, by positivity, fun γ τ hτ => ?_⟩
  have hT0 : 0 < τ.im := τ.im_pos
  set T := τ.im with hT
  have data : ∀ δ : ℕ, 0 < δ → δ ≤ 32 → ∃ P : ℝ, m ≤ P ∧ P ≤ M ∧
      ‖X0.etaD δ ((γ • τ : UpperHalfPlane) : ℂ)‖ ^ 4 * (δ * (γ • τ).im) =
        Real.exp (-(Real.pi * (((gδ δ γ : ℕ) : ℝ) ^ 2 * T / δ) / 3)) * P *
          (((gδ δ γ : ℕ) : ℝ) ^ 2 * T / δ) := by
    intro δ hδ hδ32
    obtain ⟨w, hw, hwim⟩ := etaD_norm_exact hδ γ τ
    have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
    have hwim' : w.im = ((gδ δ γ : ℕ) : ℝ) ^ 2 * T / δ := by
      rw [eq_div_iff hδR.ne']; exact hwim
    have hg1 : (1 : ℝ) ≤ ((gδ δ γ : ℕ) : ℝ) := by exact_mod_cast Nat.gcd_pos_of_pos_left _ hδ
    have hw1 : 1 ≤ w.im := by
      rw [hwim', le_div_iff₀ hδR]
      have : (δ : ℝ) ≤ 32 := by exact_mod_cast hδ32
      nlinarith
    obtain ⟨P, h1, h2, hH⟩ := hb w hw1
    exact ⟨P, h1, h2, by rw [hw, hH, hwim']⟩
  obtain ⟨P2, l2, u2, e2⟩ := data 2 (by norm_num) (by norm_num)
  obtain ⟨P4, l4, u4, e4⟩ := data 4 (by norm_num) (by norm_num)
  obtain ⟨P16, l16, u16, e16⟩ := data 16 (by norm_num) (by norm_num)
  obtain ⟨P32, l32, u32, e32⟩ := data 32 (by norm_num) (by norm_num)
  set z : ℂ := ((γ • τ : UpperHalfPlane) : ℂ)
  set I0 := (γ • τ).im
  have hI : 0 < I0 := (γ • τ).im_pos
  have n4 := X0.etaD_ne_zero (d := 4) (by norm_num) (γ • τ)
  have n32 := X0.etaD_ne_zero (d := 32) (by norm_num) (γ • τ)
  have hx : X0.xC z - 2 = X0.etaD 2 z ^ 2 * X0.etaD 16 z / (X0.etaD 4 z * X0.etaD 32 z ^ 2) := by
    unfold X0.xC; ring
  rw [hx]
  have hnorm : ‖X0.etaD 2 z ^ 2 * X0.etaD 16 z / (X0.etaD 4 z * X0.etaD 32 z ^ 2)‖ ^ 4 =
      (‖X0.etaD 2 z‖ ^ 4) ^ 2 * ‖X0.etaD 16 z‖ ^ 4 /
        (‖X0.etaD 4 z‖ ^ 4 * (‖X0.etaD 32 z‖ ^ 4) ^ 2) := by
    simp only [norm_div, norm_mul, norm_pow]
    ring
  rw [hnorm]
  set A2 := ‖X0.etaD 2 z‖ ^ 4
  set A4 := ‖X0.etaD 4 z‖ ^ 4
  set A16 := ‖X0.etaD 16 z‖ ^ 4
  set A32 := ‖X0.etaD 32 z‖ ^ 4
  have p4 : 0 < A4 := by have := norm_pos_iff.2 n4; positivity
  have p32 : 0 < A32 := by have := norm_pos_iff.2 n32; positivity
  set g2 : ℝ := ((gδ 2 γ : ℕ) : ℝ)
  set g4 : ℝ := ((gδ 4 γ : ℕ) : ℝ)
  set g16 : ℝ := ((gδ 16 γ : ℕ) : ℝ)
  set g32 : ℝ := ((gδ 32 γ : ℕ) : ℝ)
  have hg4 : 1 ≤ g4 := by
    show (1 : ℝ) ≤ ((Nat.gcd 4 (γ 1 0).natAbs : ℕ) : ℝ)
    exact_mod_cast Nat.gcd_pos_of_pos_left (γ 1 0).natAbs (by norm_num : 0 < 4)
  have hg32 : 1 ≤ g32 := by
    show (1 : ℝ) ≤ ((Nat.gcd 32 (γ 1 0).natAbs : ℕ) : ℝ)
    exact_mod_cast Nat.gcd_pos_of_pos_left (γ 1 0).natAbs (by norm_num : 0 < 32)
  have hg2 : 0 ≤ g2 ∧ g2 ≤ 2 := ⟨by positivity, by
    show ((Nat.gcd 2 (γ 1 0).natAbs : ℕ) : ℝ) ≤ 2
    exact_mod_cast Nat.gcd_le_left (γ 1 0).natAbs (by norm_num : 0 < 2)⟩
  have hg16 : 0 ≤ g16 ∧ g16 ≤ 16 := ⟨by positivity, by
    show ((Nat.gcd 16 (γ 1 0).natAbs : ℕ) : ℝ) ≤ 16
    exact_mod_cast Nat.gcd_le_left (γ 1 0).natAbs (by norm_num : 0 < 16)⟩
  set E2 := Real.exp (-(Real.pi * (g2 ^ 2 * T / (2 : ℕ)) / 3))
  set E4 := Real.exp (-(Real.pi * (g4 ^ 2 * T / (4 : ℕ)) / 3))
  set E16 := Real.exp (-(Real.pi * (g16 ^ 2 * T / (16 : ℕ)) / 3))
  set E32 := Real.exp (-(Real.pi * (g32 ^ 2 * T / (32 : ℕ)) / 3))
  set Ee := Real.exp (-(Real.pi * T * expS γ / 96))
  have hE : E2 ^ 2 * E16 = Ee * E4 * E32 ^ 2 := by
    simp only [E2, E4, E16, E32, Ee, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    simp only [expS, g2, g4, g16, g32]
    push_cast
    ring
  have hE2 : 0 < E2 := Real.exp_pos _
  have hE4 : 0 < E4 := Real.exp_pos _
  have hE16 : 0 < E16 := Real.exp_pos _
  have hE32 : 0 < E32 := Real.exp_pos _
  have hEe' : Ee = E2 ^ 2 * E16 / (E4 * E32 ^ 2) := by
    rw [hE]; field_simp
  have eA2 : A2 = E2 * P2 * (g2 ^ 2 * T / (2 : ℕ)) / ((2 : ℕ) * I0) := by
    rw [eq_div_iff (by positivity)]; exact e2
  have eA4 : A4 = E4 * P4 * (g4 ^ 2 * T / (4 : ℕ)) / ((4 : ℕ) * I0) := by
    rw [eq_div_iff (by positivity)]; exact e4
  have eA16 : A16 = E16 * P16 * (g16 ^ 2 * T / (16 : ℕ)) / ((16 : ℕ) * I0) := by
    rw [eq_div_iff (by positivity)]; exact e16
  have eA32 : A32 = E32 * P32 * (g32 ^ 2 * T / (32 : ℕ)) / ((32 : ℕ) * I0) := by
    rw [eq_div_iff (by positivity)]; exact e32
  have hP4 : 0 < P4 := lt_of_lt_of_le hm l4
  have hP32 : 0 < P32 := lt_of_lt_of_le hm l32
  have hg4' : 0 < g4 := by linarith
  have hg32' : 0 < g32 := by linarith
  have hiden : A2 ^ 2 * A16 / (A4 * A32 ^ 2) = E2 ^ 2 * E16 / (E4 * E32 ^ 2) *
      (4096 * ((P2 ^ 2 * P16) / (P4 * P32 ^ 2)) * (((g2 ^ 2) ^ 2 * g16 ^ 2) / (g4 ^ 2 * (g32 ^ 2) ^ 2))) := by
    rw [eA2, eA4, eA16, eA32]
    push_cast
    field_simp
    ring
  rw [hiden, hEe', mul_comm (64 * M ^ 3 / m ^ 3 * 64 * 4096)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hPr : (P2 ^ 2 * P16) / (P4 * P32 ^ 2) ≤ M ^ 3 / m ^ 3 := by
    have hPa : P2 ^ 2 * P16 ≤ M ^ 3 := by
      have : 0 ≤ P2 := (hm.trans_le l2).le
      have : 0 ≤ P16 := (hm.trans_le l16).le
      calc P2 ^ 2 * P16 ≤ M ^ 2 * M := by gcongr
        _ = M ^ 3 := by ring
    have hPb : m ^ 3 ≤ P4 * P32 ^ 2 := by
      calc m ^ 3 = m * m ^ 2 := by ring
        _ ≤ P4 * P32 ^ 2 := by gcongr
    exact div_le_div₀ (by positivity) hPa (by positivity) hPb
  have hgr := gratio_le hg2.1 hg2.2 hg16.1 hg16.2 hg4 hg32
  calc 4096 * ((P2 ^ 2 * P16) / (P4 * P32 ^ 2)) * (((g2 ^ 2) ^ 2 * g16 ^ 2) / (g4 ^ 2 * (g32 ^ 2) ^ 2))
      ≤ 4096 * (M ^ 3 / m ^ 3) * 4096 := by gcongr
    _ = 64 * M ^ 3 / m ^ 3 * 64 * 4096 := by ring

/-- `f =O[atImInfty] g` from `|f − c|⁴ ≤ K g⁴` for `Im τ ≥ 32` and `g ≥ 1` (Shimura's `bigO_of_pow4`,
for a general majorant). -/
theorem bigO_of_pow4' {f : UpperHalfPlane → ℂ} {g : UpperHalfPlane → ℝ} {K : ℝ} (hK : 0 ≤ K) (c : ℂ)
    (hg : ∀ τ, 1 ≤ g τ) (h : ∀ τ : UpperHalfPlane, 32 ≤ τ.im → ‖f τ - c‖ ^ 4 ≤ K * g τ ^ 4) :
    f =O[atImInfty] g := by
  refine Asymptotics.IsBigO.of_bound (K + 1 + ‖c‖) ?_
  rw [Filter.eventually_iff, atImInfty_mem]
  refine ⟨32, fun τ hτ => ?_⟩
  simp only [Set.mem_setOf_eq, Real.norm_eq_abs]
  set E := g τ
  have hE1 : 1 ≤ E := hg τ
  rw [abs_of_pos (lt_of_lt_of_le one_pos hE1)]
  have h1 : ‖f τ - c‖ ≤ (K + 1) * E := by
    refine le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by positivity) ?_
    calc ‖f τ - c‖ ^ 4 ≤ K * E ^ 4 := h τ hτ
      _ ≤ (K + 1) ^ 4 * E ^ 4 := by
          gcongr
          exact (by linarith : K ≤ K + 1).trans (le_self_pow₀ (by linarith) (by norm_num))
      _ = ((K + 1) * E) ^ 4 := by ring
  calc ‖f τ‖ = ‖(f τ - c) + c‖ := by ring_nf
    _ ≤ ‖f τ - c‖ + ‖c‖ := norm_add_le _ _
    _ ≤ (K + 1) * E + ‖c‖ * E := by gcongr; nlinarith [norm_nonneg c]
    _ = (K + 1 + ‖c‖) * E := by ring

theorem gcd_mod32 (δ n : ℕ) (hδ : δ ∣ 32) : Nat.gcd δ n = Nat.gcd δ (n % 32) := by
  calc Nat.gcd δ n = Nat.gcd (n % δ) δ := Nat.gcd_rec δ n
    _ = Nat.gcd (n % 32 % δ) δ := by rw [Nat.mod_mod_of_dvd n hδ]
    _ = Nat.gcd δ (n % 32) := (Nat.gcd_rec δ (n % 32)).symm

theorem expS_table : ∀ r : ℕ, r < 32 → r ≠ 0 →
    2 * Nat.gcd 32 r ^ 2 + 8 * Nat.gcd 4 r ^ 2 ≤ 32 * Nat.gcd 2 r ^ 2 + 2 * Nat.gcd 16 r ^ 2 := by
  decide +kernel

/-- **Ligozat's order of `x` at the cusp `γ∞` is `≥ 0` when `32 ∤ c`.** -/
theorem expS_nonneg (γ : SL(2, ℤ)) (h : ¬ (32 : ℤ) ∣ γ 1 0) : 0 ≤ expS γ := by
  set n := (γ 1 0).natAbs
  have hr : n % 32 ≠ 0 := by
    intro h0
    apply h
    exact Int.natCast_dvd.2 (Nat.dvd_of_mod_eq_zero h0)
  have ht := expS_table (n % 32) (Nat.mod_lt _ (by norm_num)) hr
  have e2 := gcd_mod32 2 n (by norm_num)
  have e4 := gcd_mod32 4 n (by norm_num)
  have e16 := gcd_mod32 16 n (by norm_num)
  have e32 := gcd_mod32 32 n (by norm_num)
  rw [← e2, ← e4, ← e16, ← e32] at ht
  have ht' : (2 * (Nat.gcd 32 n : ℝ) ^ 2 + 8 * (Nat.gcd 4 n : ℝ) ^ 2) ≤
      32 * (Nat.gcd 2 n : ℝ) ^ 2 + 2 * (Nat.gcd 16 n : ℝ) ^ 2 := by exact_mod_cast ht
  simp only [expS, gδ]
  linarith

theorem expS_one : expS 1 = -1536 := by
  simp only [expS, gδ]
  norm_num

/-- **`x` has at most a double pole at `∞`**: `x(τ) = O(e^{4π Im τ})`. -/
theorem xC_bigO_atImInfty : (fun τ : UpperHalfPlane => X0.xC τ) =O[atImInfty]
    fun τ => Real.exp (4 * Real.pi * τ.im) := by
  obtain ⟨K, hK, hb⟩ := xC_sub_two_bound
  refine bigO_of_pow4' hK 2 (fun τ => Real.one_le_exp (by have := τ.im_pos; positivity))
    fun τ hτ => ?_
  have h := hb 1 τ hτ
  rw [one_smul, expS_one] at h
  refine h.trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- **`x` is bounded at every cusp `γ∞` not equivalent to `∞`** (`32 ∤ c`). -/
theorem xC_bounded_cusp (γ : SL(2, ℤ)) (h : ¬ (32 : ℤ) ∣ γ 1 0) :
    IsBoundedAtImInfty (fun τ : UpperHalfPlane => X0.xC (γ • τ : UpperHalfPlane)) := by
  obtain ⟨K, hK, hb⟩ := xC_sub_two_bound
  have hS := expS_nonneg γ h
  have : (fun τ : UpperHalfPlane => X0.xC (γ • τ : UpperHalfPlane)) =O[atImInfty]
      fun _ => (1 : ℝ) := by
    refine bigO_of_pow4' hK 2 (fun _ => le_rfl) fun τ hτ => ?_
    refine (hb γ τ hτ).trans ?_
    rw [one_pow, mul_one]
    have : Real.exp (-(Real.pi * τ.im * expS γ / 96)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := τ.im_pos
      have := Real.pi_pos
      have : 0 ≤ Real.pi * τ.im * expS γ := by positivity
      linarith
    nlinarith
  exact this

end ZInQ.Contrib.TYZGenus.H33Dict

#print axioms ZInQ.Contrib.TYZGenus.H33Dict.xC_bigO_atImInfty
#print axioms ZInQ.Contrib.TYZGenus.H33Dict.xC_bounded_cusp
