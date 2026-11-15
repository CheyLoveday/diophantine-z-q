import ZInQKernel.OneProof.H.TailZ18

set_option linter.all false
open Complex Matrix
open scoped Real

noncomputable section

namespace GapTheta
open CM24

/-- Positive-definite imaginary part of the symmetric matrix `[[α, β], [β, γ]]`. -/
def PDq (α β γ : ℂ) : Prop := 0 < α.im ∧ 0 < α.im * γ.im - β.im ^ 2

theorem PDq.bound {α β γ : ℂ} (h : PDq α β γ) : ∃ δ : ℝ, 0 < δ ∧
    ∀ x y : ℝ, δ * (x ^ 2 + y ^ 2) ≤ α.im * x ^ 2 + 2 * β.im * x * y + γ.im * y ^ 2 := by
  obtain ⟨ha, hd⟩ := h
  have hc : 0 < γ.im := by nlinarith [sq_nonneg β.im]
  refine ⟨(α.im * γ.im - β.im ^ 2) / (α.im + γ.im), div_pos hd (by linarith), fun x y => ?_⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg (α.im * x + β.im * y), sq_nonneg (β.im * x + γ.im * y)]

theorem PDq.summable {α β γ : ℂ} (h : PDq α β γ) (c0 c1 d0 d1 : ℝ) :
    Summable (term2 α β γ c0 c1 d0 d1) := by
  obtain ⟨δ, hδ, hQ⟩ := h.bound
  exact summable_term2 hδ hQ c0 c1 d0 d1

theorem PDq.swap {α β γ : ℂ} (h : PDq α β γ) : PDq γ β α := by
  obtain ⟨ha, hd⟩ := h
  exact ⟨by nlinarith [sq_nonneg β.im], by linarith⟩

theorem PDq.ne_zero {α β γ : ℂ} (h : PDq α β γ) : α ≠ 0 := fun h0 => by
  have := h.1; rw [h0] at this; simp at this

theorem PDq.j1 {α β γ : ℂ} (h : PDq α β γ) : PDq (-1 / α) (β / α) (γ - β ^ 2 / α) := by
  obtain ⟨ha, hd⟩ := h
  have hn : 0 < Complex.normSq α := Complex.normSq_pos.2 (fun h0 => by rw [h0] at ha; simp at ha)
  have e1 : (-1 / α).im = α.im / Complex.normSq α := by
    rw [Complex.div_im]; simp [neg_div]
  have key : (-1 / α).im * (γ - β ^ 2 / α).im - (β / α).im ^ 2 =
      (α.im * γ.im - β.im ^ 2) / Complex.normSq α := by
    simp only [Complex.div_im, Complex.div_re, Complex.sub_im, pow_two, Complex.mul_im,
      Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im]
    rw [Complex.normSq_apply] at hn ⊢
    field_simp
    ring
  refine ⟨by rw [e1]; exact div_pos ha hn, by rw [key]; exact div_pos hd hn⟩

theorem PDq.det_ne {α β γ : ℂ} (h : PDq α β γ) : α * γ - β ^ 2 ≠ 0 := by
  have h1 := h.j1.swap.ne_zero
  have h0 := h.ne_zero
  have : α * γ - β ^ 2 = α * (γ - β ^ 2 / α) := by field_simp
  rw [this]; exact mul_ne_zero h0 h1

/-- **Full inversion `Ω ↦ −Ω⁻¹`**, squared (two partial inversions `pi0` and two swaps). -/
theorem inv_sq {α β γ : ℂ} (h : PDq α β γ) (c0 c1 d0 d1 : ℝ) :
    Th2 α β γ c0 c1 d0 d1 ^ 2 = -(1 / (α * γ - β ^ 2)) * cexp (4 * π * I * (c0 * d0 + c1 * d1)) *
      Th2 (-γ / (α * γ - β ^ 2)) (β / (α * γ - β ^ 2)) (-α / (α * γ - β ^ 2)) (-d0) (-d1) c0 c1 ^ 2 := by
  have h1 := h.j1
  have h1s := h1.swap
  have h2 := h1s.j1
  have hα := h.ne_zero
  have hγ1 := h1s.ne_zero
  have hΔ := h.det_ne
  rw [pi0 h.1 c0 c1 d0 d1 (h.summable _ _ _ _) (h1.summable _ _ _ _), th2_swap,
    pi0 h1s.1 _ _ _ _ (h1s.summable _ _ _ _) (h2.summable _ _ _ _), th2_swap]
  have e1 : -1 / α - (β / α) ^ 2 / (γ - β ^ 2 / α) = -γ / (α * γ - β ^ 2) := by
    field_simp; ring
  have e2 : β / α / (γ - β ^ 2 / α) = β / (α * γ - β ^ 2) := by
    field_simp
  have e3 : -1 / (γ - β ^ 2 / α) = -α / (α * γ - β ^ 2) := by
    field_simp
  rw [e1, e2, e3]
  simp only [mul_pow, cpow_half_sq]
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have ex : cexp (4 * π * I * (c0 * d0 + c1 * d1)) =
      cexp (((2 : ℕ) : ℂ) * (2 * π * I * c0 * d0)) * cexp (((2 : ℕ) : ℂ) * (2 * π * I * c1 * d1)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [ex]
  have : (γ - β ^ 2 / α) = (α * γ - β ^ 2) / α := by field_simp
  rw [this]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring


/-- `inv_sq` solved for the inverted side. -/
theorem inv_sq' {α β γ : ℂ} (h : PDq α β γ) (c0 c1 d0 d1 : ℝ) :
    Th2 (-γ / (α * γ - β ^ 2)) (β / (α * γ - β ^ 2)) (-α / (α * γ - β ^ 2)) c0 c1 d0 d1 ^ 2 =
      -(α * γ - β ^ 2) * cexp (4 * π * I * (c0 * d0 + c1 * d1)) * Th2 α β γ d0 d1 (-c0) (-c1) ^ 2 := by
  have e := inv_sq h d0 d1 (-c0) (-c1)
  simp only [neg_neg] at e
  rw [e]
  have hΔ := h.det_ne
  have hx : cexp (4 * π * I * (c0 * d0 + c1 * d1)) * cexp (4 * π * I * (d0 * ((-c0 : ℝ) : ℂ) + d1 * ((-c1 : ℝ) : ℂ))) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; push_cast; ring
  rw [show ∀ (D e1 e2 X : ℂ), -D * e1 * (-(1 / D) * e2 * X) = (D * (1 / D)) * (e1 * e2) * X from
    fun _ _ _ _ => by ring, hx, mul_one_div_cancel hΔ, one_mul, one_mul]

/-- **Translation `Ω ↦ Ω + S`** by an integral symmetric `S = [[s00, s01], [s01, s11]]`. -/
theorem th2_trans {α β γ α' β' γ' : ℂ} (s00 s01 s11 : ℤ) (hα : α' = α + s00) (hβ : β' = β + s01)
    (hγ : γ' = γ + s11) (c0 c1 d0 d1 : ℝ) :
    Th2 α' β' γ' c0 c1 d0 d1 =
      cexp (-(π * I * (s00 * ((c0 : ℂ) ^ 2 + c0) + s11 * ((c1 : ℂ) ^ 2 + c1) + 2 * s01 * c0 * c1))) *
      Th2 α β γ c0 c1 (d0 + s00 * (c0 + 1 / 2) + s01 * c1) (d1 + s11 * (c1 + 1 / 2) + s01 * c0) := by
  subst hα hβ hγ
  apply th2_phase
  intro n
  obtain ⟨t0, ht0⟩ := cast_even (n.1 - 1)
  obtain ⟨t1, ht1⟩ := cast_even (n.2 - 1)
  refine ⟨s00 * t0 + s11 * t1 + s01 * (n.1 * n.2), ?_⟩
  push_cast at ht0 ht1 ⊢
  linear_combination (π * I * s00) * ht0 + (π * I * s11) * ht1

/-- **Rotation by `diag(1, −1)`**: negating the off-diagonal entry. -/
theorem th2_neg (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) :
    Th2 α (-β) γ c0 c1 d0 d1 = Th2 α β γ c0 (-c1) d0 (-d1) := by
  rw [Th2, Th2, ← (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)).tsum_eq]
  congr 1; funext n
  simp only [term2, Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.neg_apply, Prod.map_fst, Prod.map_snd, id]
  congr 1; push_cast; ring

/-- **Reduction of half-integral characteristics mod `ℤ`**, squared (the sign `±1` squares away). -/
theorem th2_sq_red (α β γ : ℂ) {c0 c1 d0 d1 : ℝ} (x0 x1 y0 y1 : ℤ) (h0 : c0 = (x0 : ℝ) / 2)
    (h1 : c1 = (x1 : ℝ) / 2) (h2 : d0 = (y0 : ℝ) / 2) (h3 : d1 = (y1 : ℝ) / 2) :
    Th2 α β γ c0 c1 d0 d1 ^ 2 = Th2 α β γ (((x0 % 2 : ℤ) : ℝ) / 2) (((x1 % 2 : ℤ) : ℝ) / 2)
      (((y0 % 2 : ℤ) : ℝ) / 2) (((y1 % 2 : ℤ) : ℝ) / 2) ^ 2 := by
  have r : ∀ x : ℤ, (x : ℝ) / 2 = ((x % 2 : ℤ) : ℝ) / 2 + ((x / 2 : ℤ) : ℝ) := fun x => by
    have := Int.emod_add_mul_ediv x 2
    have : (x : ℝ) = ((x % 2 : ℤ) : ℝ) + 2 * ((x / 2 : ℤ) : ℝ) := by exact_mod_cast this.symm
    linarith
  rw [h0, h1, h2, h3, r x0, r x1, r y0, r y1, th2_shift_c, th2_shift_d, mul_pow, ← Complex.exp_nat_mul]
  have : cexp (((2 : ℕ) : ℂ) * (2 * π * I * ((((x0 % 2 : ℤ) : ℝ) / 2 : ℝ) * ((y0 / 2 : ℤ) : ℂ) +
      (((x1 % 2 : ℤ) : ℝ) / 2 : ℝ) * ((y1 / 2 : ℤ) : ℂ)))) = 1 := by
    rw [show ((2 : ℕ) : ℂ) * (2 * π * I * ((((x0 % 2 : ℤ) : ℝ) / 2 : ℝ) * ((y0 / 2 : ℤ) : ℂ) +
      (((x1 % 2 : ℤ) : ℝ) / 2 : ℝ) * ((y1 / 2 : ℤ) : ℂ))) =
      (((x0 % 2) * (y0 / 2) + (x1 % 2) * (y1 / 2) : ℤ) : ℂ) * (2 * π * I) by push_cast; ring]
    exact exp_int_mul_two_pi_mul_I _
  rw [this, one_mul]


/-! ## Siegel space, characteristics, assembly -/

open HDec.PkgI1 (SiegelH2 thetaConst evenChars thetaSum8 thetaProd2 spAct spFactor Char2 card_evenChars)

theorem pdq_of_siegel {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ SiegelH2) :
    Ω 1 0 = Ω 0 1 ∧ PDq (Ω 0 0) (Ω 0 1) (Ω 1 1) := by
  obtain ⟨hT, hP⟩ := hΩ
  have hs : Ω 1 0 = Ω 0 1 := by
    have := congrFun (congrFun hT 0) 1; simpa [Matrix.transpose_apply] using this
  refine ⟨hs, ?_, ?_⟩
  · have := hP.diag_pos (i := 0); simpa using this
  · have := hP.det_pos
    rw [Matrix.det_fin_two] at this
    simp only [Matrix.map_apply, hs] at this
    nlinarith

theorem PDq.add {α β γ : ℂ} (h : PDq α β γ) (s00 s01 s11 : ℤ) :
    PDq (α + s00) (β + s01) (γ + s11) := by
  simpa [PDq] using h

/-- The residue of an integer mod 2 as an element of `Fin 2`. -/
def fin2 (x : ℤ) : Fin 2 := ⟨(x % 2).toNat, by omega⟩

theorem fin2_cast (x : ℤ) : (((fin2 x : Fin 2) : ℕ) : ℝ) = ((x % 2 : ℤ) : ℝ) := by
  have h : (((x % 2).toNat : ℕ) : ℤ) = x % 2 := Int.toNat_of_nonneg (Int.emod_nonneg x (by norm_num))
  rw [fin2, Fin.val_mk, ← h]; norm_cast

theorem exp_quarter_pow4 (N : ℤ) (h : N % 2 = 0) : cexp (π * I * (N : ℂ) / 4) ^ 4 = 1 := by
  rw [← Complex.exp_nat_mul]
  obtain ⟨k, hk⟩ : ∃ k, N = 2 * k := ⟨N / 2, by omega⟩
  rw [show ((4 : ℕ) : ℂ) * (π * I * (N : ℂ) / 4) = (k : ℂ) * (2 * π * I) by rw [hk]; push_cast; ring]
  exact exp_int_mul_two_pi_mul_I k

/-- **Assembly.** A permutation of the even characteristics with quarter-root phases gives both
transformation laws. -/
theorem assemble {Ω Ω' : Matrix (Fin 2) (Fin 2) ℂ} (D : ℂ) (σ : Char2 → Char2) (N : Char2 → ℤ)
    (h : ∀ m ∈ evenChars, thetaConst m Ω' ^ 2 = -D * cexp (π * I * (N m : ℂ) / 4) * thetaConst (σ m) Ω ^ 2)
    (himg : evenChars.image σ = evenChars)
    (hinj : ∀ a ∈ evenChars, ∀ b ∈ evenChars, σ a = σ b → a = b)
    (hev : ∀ m ∈ evenChars, N m % 2 = 0) (hsum : (∑ m ∈ evenChars, N m) % 8 = 0) :
    thetaSum8 Ω' = D ^ 4 * thetaSum8 Ω ∧ thetaProd2 Ω' = D ^ 10 * thetaProd2 Ω := by
  have hinj' : Set.InjOn σ (evenChars : Set Char2) := fun a ha b hb e => hinj a ha b hb e
  have e8 : ∑ m ∈ evenChars, thetaConst m Ω ^ 8 = ∑ m ∈ evenChars, thetaConst (σ m) Ω ^ 8 := by
    rw [← Finset.sum_image (f := fun m => thetaConst m Ω ^ 8) hinj', himg]
  have e2 : ∏ m ∈ evenChars, thetaConst m Ω ^ 2 = ∏ m ∈ evenChars, thetaConst (σ m) Ω ^ 2 := by
    rw [← Finset.prod_image (f := fun m => thetaConst m Ω ^ 2) hinj', himg]
  constructor
  · rw [thetaSum8, thetaSum8, e8, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [show thetaConst m Ω' ^ 8 = (thetaConst m Ω' ^ 2) ^ 4 by ring, h m hm, mul_pow, mul_pow,
      exp_quarter_pow4 _ (hev m hm)]
    ring
  · rw [thetaProd2, thetaProd2, e2, Finset.prod_congr rfl h,
      Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, card_evenChars,
      ← Complex.exp_sum]
    obtain ⟨k, hk⟩ : ∃ k, ∑ m ∈ evenChars, N m = 8 * k := ⟨(∑ m ∈ evenChars, N m) / 8, by omega⟩
    have : ∑ m ∈ evenChars, π * I * (N m : ℂ) / 4 = (k : ℂ) * (2 * π * I) := by
      rw [← Finset.sum_div, ← Finset.mul_sum, ← Int.cast_sum, hk]; push_cast; ring
    rw [this, exp_int_mul_two_pi_mul_I]
    ring


/-! ## `M6` -/

open HDec.HSyn.G0Split.FibreQM.PeriodGlue (M4 M6 M4_map M6_map A4 B4 C4 D4 A6 B6 C6 D6)

theorem spAct_M6 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hs : Ω 1 0 = Ω 0 1)
    (hΔ : (Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2 ≠ 0) :
    spAct M6 Ω = !![-(Ω 0 0 + 1) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2),
      -((Ω 0 1 - 1) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2));
      -((Ω 0 1 - 1) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2)),
      -(Ω 1 1 + 2) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2)] := by
  unfold spAct
  simp only [M6_map, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  have hdet : (C6 * Ω + D6).det = (Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp [C6, D6, hs]
    ring
  letI := Matrix.invertibleOfIsUnitDet (C6 * Ω + D6) (isUnit_iff_ne_zero.mpr (hdet ▸ hΔ))
  rw [Matrix.mul_inv_eq_iff_eq_mul_of_invertible]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [A6, B6, C6, D6, hs] <;> field_simp <;> ring

theorem spFactor_M6 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hs : Ω 1 0 = Ω 0 1) :
    spFactor M6 Ω = (Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2 := by
  unfold spFactor
  simp only [M6_map, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
  simp [C6, D6, hs]
  ring

/-- The characteristic permutation of `M6`. -/
def σ6 (m : Char2) : Char2 :=
  (![fin2 (-((m.2 1 : ℕ) : ℤ)), fin2 ((m.2 0 : ℕ) : ℤ)],
   ![fin2 (((m.1 1 : ℕ) : ℤ) - ((m.2 1 : ℕ) : ℤ) + 1 - ((m.2 0 : ℕ) : ℤ)),
     fin2 (-((m.1 0 : ℕ) : ℤ) + 2 * ((m.2 0 : ℕ) : ℤ) + 2 + ((m.2 1 : ℕ) : ℤ))])

/-- The phase exponent of `M6` (in units of `πi/4`). -/
def N6 (m : Char2) : ℤ :=
  4 * ((m.1 0 : ℕ) : ℤ) * ((m.2 0 : ℕ) : ℤ) + 4 * ((m.1 1 : ℕ) : ℤ) * ((m.2 1 : ℕ) : ℤ)
    - 2 * ((m.2 1 : ℕ) : ℤ) ^ 2 + 4 * ((m.2 1 : ℕ) : ℤ) - 4 * ((m.2 0 : ℕ) : ℤ) ^ 2
    - 8 * ((m.2 0 : ℕ) : ℤ) - 4 * ((m.2 0 : ℕ) : ℤ) * ((m.2 1 : ℕ) : ℤ)

theorem sq6 (m : Char2) {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ SiegelH2) :
    thetaConst m (spAct M6 Ω) ^ 2 =
      -((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2) * cexp (π * I * (N6 m : ℂ) / 4) *
        thetaConst (σ6 m) Ω ^ 2 := by
  obtain ⟨hs, hpd⟩ := pdq_of_siegel hΩ
  have hpd1 : PDq (Ω 0 0 + 1) (Ω 0 1 - 1) (Ω 1 1 + 2) := by simpa [PDq] using hpd
  rw [spAct_M6 hs hpd1.det_ne, thetaConst_eq _ _ (by simp), thetaConst_eq _ _ hs]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  rw [th2_neg, th2_swap, inv_sq' hpd1,
    th2_trans (α := Ω 0 0) (β := Ω 0 1) (γ := Ω 1 1) 1 (-1) 2 (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring), mul_pow]
  rw [th2_sq_red _ _ _ (-((m.2 1 : ℕ) : ℤ)) ((m.2 0 : ℕ) : ℤ)
    (((m.1 1 : ℕ) : ℤ) - ((m.2 1 : ℕ) : ℤ) + 1 - ((m.2 0 : ℕ) : ℤ))
    (-((m.1 0 : ℕ) : ℤ) + 2 * ((m.2 0 : ℕ) : ℤ) + 2 + ((m.2 1 : ℕ) : ℤ))
    (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)]
  simp only [σ6, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, fin2_cast]
  rw [show ∀ (D e1 e2 T : ℂ), -D * e1 * (e2 ^ 2 * T) = -D * (e1 * e2 ^ 2) * T from
    fun _ _ _ _ => by ring]
  congr 2
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  simp only [N6]
  push_cast
  ring


theorem σ6_img : evenChars.image σ6 = evenChars := by decide
theorem σ6_inj : ∀ a ∈ evenChars, ∀ b ∈ evenChars, σ6 a = σ6 b → a = b := by decide
theorem N6_even : ∀ m ∈ evenChars, N6 m % 2 = 0 := by decide
theorem N6_sum : (∑ m ∈ evenChars, N6 m) % 8 = 0 := by decide

/-- **`M6` on the Siegel space.** -/
theorem thetaM6 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ SiegelH2) :
    thetaSum8 (spAct M6 Ω) = spFactor M6 Ω ^ 4 * thetaSum8 Ω ∧
      thetaProd2 (spAct M6 Ω) = spFactor M6 Ω ^ 10 * thetaProd2 Ω := by
  rw [spFactor_M6 (pdq_of_siegel hΩ).1]
  exact assemble _ σ6 N6 (fun m _ => sq6 m hΩ) σ6_img σ6_inj N6_even N6_sum

/-! ## `M4` -/

theorem spAct_M4 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hs : Ω 1 0 = Ω 0 1)
    (hΔ : (Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2 ≠ 0) :
    spAct M4 Ω = !![-(Ω 0 0 + 1) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2),
      (Ω 0 1 - 1) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2) + 1;
      (Ω 0 1 - 1) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2) + 1,
      -(Ω 1 1 + 2) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2)] := by
  unfold spAct
  simp only [M4_map, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  have hdet : (C4 * Ω + D4).det = -((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2) := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp [C4, D4, hs]
    ring
  letI := Matrix.invertibleOfIsUnitDet (C4 * Ω + D4) (isUnit_iff_ne_zero.mpr (hdet ▸ neg_ne_zero.2 hΔ))
  rw [Matrix.mul_inv_eq_iff_eq_mul_of_invertible]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [A4, B4, C4, D4, hs] <;> field_simp <;> ring

theorem spFactor_M4 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hs : Ω 1 0 = Ω 0 1) :
    spFactor M4 Ω = -((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2) := by
  unfold spFactor
  simp only [M4_map, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
  simp [C4, D4, hs]
  ring

/-- The characteristic permutation of `M4`. -/
def σ4 (m : Char2) : Char2 :=
  (![fin2 (((m.1 0 : ℕ) : ℤ) + ((m.2 1 : ℕ) : ℤ)), fin2 (((m.1 1 : ℕ) : ℤ) + ((m.2 0 : ℕ) : ℤ))],
   ![fin2 (((m.1 0 : ℕ) : ℤ) - 2 * ((m.1 1 : ℕ) : ℤ) + ((m.2 1 : ℕ) : ℤ) - ((m.2 0 : ℕ) : ℤ) + 1),
     fin2 (-2 * ((m.1 0 : ℕ) : ℤ) + 2 * ((m.1 1 : ℕ) : ℤ) + 2 * ((m.2 0 : ℕ) : ℤ) - ((m.2 1 : ℕ) : ℤ) + 2)])

/-- The phase exponent of `M4` (in units of `πi/4`). -/
def N4 (m : Char2) : ℤ :=
  4 * ((m.1 0 : ℕ) : ℤ) * ((m.1 1 : ℕ) : ℤ) + 4 * ((m.1 1 : ℕ) : ℤ) * ((m.2 1 : ℕ) : ℤ)
    + 4 * ((m.1 0 : ℕ) : ℤ) * ((m.2 0 : ℕ) : ℤ)
    - 2 * (((m.1 0 : ℕ) : ℤ) + ((m.2 1 : ℕ) : ℤ)) ^ 2 - 4 * (((m.1 0 : ℕ) : ℤ) + ((m.2 1 : ℕ) : ℤ))
    - 4 * (((m.1 1 : ℕ) : ℤ) + ((m.2 0 : ℕ) : ℤ)) ^ 2 - 8 * (((m.1 1 : ℕ) : ℤ) + ((m.2 0 : ℕ) : ℤ))
    + 4 * (((m.1 0 : ℕ) : ℤ) + ((m.2 1 : ℕ) : ℤ)) * (((m.1 1 : ℕ) : ℤ) + ((m.2 0 : ℕ) : ℤ))

theorem sq4 (m : Char2) {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ SiegelH2) :
    thetaConst m (spAct M4 Ω) ^ 2 =
      -((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2) * cexp (π * I * (N4 m : ℂ) / 4) *
        thetaConst (σ4 m) Ω ^ 2 := by
  obtain ⟨hs, hpd⟩ := pdq_of_siegel hΩ
  have hpd1 : PDq (Ω 0 0 + 1) (Ω 0 1 - 1) (Ω 1 1 + 2) := by simpa [PDq] using hpd
  rw [spAct_M4 hs hpd1.det_ne, thetaConst_eq _ _ (by simp), thetaConst_eq _ _ hs]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  rw [th2_trans (α := -(Ω 0 0 + 1) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2))
      (β := (Ω 0 1 - 1) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2))
      (γ := -(Ω 1 1 + 2) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2)) 0 1 0
      (by push_cast; ring) (by push_cast; ring) (by push_cast; ring),
    mul_pow, th2_swap, inv_sq' hpd1,
    th2_trans (α := Ω 0 0) (β := Ω 0 1) (γ := Ω 1 1) 1 (-1) 2 (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring), mul_pow]
  rw [th2_sq_red _ _ _ (((m.1 0 : ℕ) : ℤ) + ((m.2 1 : ℕ) : ℤ)) (((m.1 1 : ℕ) : ℤ) + ((m.2 0 : ℕ) : ℤ))
    (((m.1 0 : ℕ) : ℤ) - 2 * ((m.1 1 : ℕ) : ℤ) + ((m.2 1 : ℕ) : ℤ) - ((m.2 0 : ℕ) : ℤ) + 1)
    (-2 * ((m.1 0 : ℕ) : ℤ) + 2 * ((m.1 1 : ℕ) : ℤ) + 2 * ((m.2 0 : ℕ) : ℤ) - ((m.2 1 : ℕ) : ℤ) + 2)
    (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)]
  simp only [σ4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, fin2_cast]
  rw [show ∀ (D e0 e1 e2 T : ℂ), e0 ^ 2 * (-D * e1 * (e2 ^ 2 * T)) = -D * (e0 ^ 2 * e1 * e2 ^ 2) * T from
    fun _ _ _ _ _ => by ring]
  congr 2
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [N4]
  push_cast
  ring

theorem σ4_img : evenChars.image σ4 = evenChars := by decide
theorem σ4_inj : ∀ a ∈ evenChars, ∀ b ∈ evenChars, σ4 a = σ4 b → a = b := by decide
theorem N4_even : ∀ m ∈ evenChars, N4 m % 2 = 0 := by decide
theorem N4_sum : (∑ m ∈ evenChars, N4 m) % 8 = 0 := by decide

/-- **`M4` on the Siegel space.** -/
theorem thetaM4 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ SiegelH2) :
    thetaSum8 (spAct M4 Ω) = spFactor M4 Ω ^ 4 * thetaSum8 Ω ∧
      thetaProd2 (spAct M4 Ω) = spFactor M4 Ω ^ 10 * thetaProd2 Ω := by
  have h := assemble _ σ4 N4 (fun m _ => sq4 m hΩ) σ4_img σ4_inj N4_even N4_sum
  rw [spFactor_M4 (pdq_of_siegel hΩ).1, Even.neg_pow (by decide), Even.neg_pow (by decide)]
  exact h

end GapTheta
