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

end GapTheta
