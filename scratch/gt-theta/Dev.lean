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
    rw [Complex.div_im]; simp
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

end GapTheta
