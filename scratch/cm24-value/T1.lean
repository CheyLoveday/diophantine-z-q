import Mathlib

set_option linter.all false
open Complex
open scoped Real

noncomputable section
namespace CM24

/-- The general genus-2 theta term with real characteristics `c = (c0,c1)`, `d = (d0,d1)` at the symmetric
matrix `[[α, β], [β, γ]]`: `exp(πi vᵀΩv + 2πi v·d)`, `v = n + c`. -/
def term2 (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (n : ℤ × ℤ) : ℂ :=
  cexp (π * I * (α * (((n.1 : ℝ) + c0 : ℝ) : ℂ) ^ 2 + 2 * β * (((n.1 : ℝ) + c0 : ℝ) : ℂ) * (((n.2 : ℝ) + c1 : ℝ) : ℂ)
      + γ * (((n.2 : ℝ) + c1 : ℝ) : ℂ) ^ 2)
    + 2 * π * I * ((((n.1 : ℝ) + c0 : ℝ) : ℂ) * d0 + (((n.2 : ℝ) + c1 : ℝ) : ℂ) * d1))

def Th2 (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) : ℂ := ∑' n : ℤ × ℤ, term2 α β γ c0 c1 d0 d1 n

theorem re_exponent (α β γ : ℂ) (x y d0 d1 : ℝ) :
    (π * I * (α * (x : ℂ) ^ 2 + 2 * β * x * y + γ * (y : ℂ) ^ 2) + 2 * π * I * ((x : ℂ) * d0 + (y : ℂ) * d1)).re
      = -π * (α.im * x ^ 2 + 2 * β.im * x * y + γ.im * y ^ 2) := by
  simp [Complex.mul_re, Complex.mul_im, pow_two]

/-- 1D Gaussian summability. -/
theorem summable_gauss {δ : ℝ} (hδ : 0 < δ) (c : ℝ) :
    Summable (fun n : ℤ => Real.exp (-π * δ * ((n : ℝ) + c) ^ 2)) := by
  have h := ((summable_jacobiTheta₂_term_iff ((c * δ : ℝ) * I) ((δ : ℂ) * I)).2
    (by simpa using hδ)).norm.mul_left (Real.exp (-π * δ * c ^ 2))
  refine h.congr fun n => ?_
  rw [norm_jacobiTheta₂_term, ← Real.exp_add]
  congr 1
  simp
  ring

theorem norm_term2 (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (n : ℤ × ℤ) :
    ‖term2 α β γ c0 c1 d0 d1 n‖ = Real.exp (-π * (α.im * ((n.1 : ℝ) + c0) ^ 2
      + 2 * β.im * ((n.1 : ℝ) + c0) * ((n.2 : ℝ) + c1) + γ.im * ((n.2 : ℝ) + c1) ^ 2)) := by
  rw [term2, Complex.norm_exp, re_exponent]

theorem summable_norm_term2 {α β γ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hQ : ∀ x y : ℝ, δ * (x ^ 2 + y ^ 2) ≤ α.im * x ^ 2 + 2 * β.im * x * y + γ.im * y ^ 2)
    (c0 c1 d0 d1 : ℝ) : Summable (fun n => ‖term2 α β γ c0 c1 d0 d1 n‖) := by
  have h := (summable_gauss hδ c0).mul_of_nonneg (summable_gauss hδ c1)
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) h
  rw [norm_term2, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have := hQ ((n.1 : ℝ) + c0) ((n.2 : ℝ) + c1)
  nlinarith [Real.pi_pos]

theorem summable_term2 {α β γ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hQ : ∀ x y : ℝ, δ * (x ^ 2 + y ^ 2) ≤ α.im * x ^ 2 + 2 * β.im * x * y + γ.im * y ^ 2)
    (c0 c1 d0 d1 : ℝ) : Summable (term2 α β γ c0 c1 d0 d1) :=
  (summable_norm_term2 hδ hQ c0 c1 d0 d1).of_norm


/-- Sum over `ℤ × ℤ` as an iterated sum, inner over the first coordinate. -/
theorem tsum_swap_iter {f : ℤ × ℤ → ℂ} (hf : Summable f) :
    ∑' n, f n = ∑' n1 : ℤ, ∑' n0 : ℤ, f (n0, n1) := by
  rw [← (Equiv.prodComm ℤ ℤ).tsum_eq]
  exact ((Equiv.prodComm ℤ ℤ).summable_iff.2 hf).tsum_prod

theorem term2_eq_jt (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (n0 n1 : ℤ) :
    term2 α β γ c0 c1 d0 d1 (n0, n1) =
      cexp (π * I * (α * (c0 : ℂ) ^ 2 + 2 * β * c0 * ((n1 : ℂ) + c1) + γ * ((n1 : ℂ) + c1) ^ 2)
        + 2 * π * I * ((c0 : ℂ) * d0 + ((n1 : ℂ) + c1) * d1)) *
      jacobiTheta₂_term n0 (c0 * α + β * ((n1 : ℂ) + c1) + d0) α := by
  rw [term2, jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem jt_dual (α β γ : ℂ) (hα : α ≠ 0) (c0 c1 d0 d1 : ℝ) (m n1 : ℤ) :
    cexp (π * I * (α * (c0 : ℂ) ^ 2 + 2 * β * c0 * ((n1 : ℂ) + c1) + γ * ((n1 : ℂ) + c1) ^ 2)
        + 2 * π * I * ((c0 : ℂ) * d0 + ((n1 : ℂ) + c1) * d1)) *
      (cexp (-π * I * (c0 * α + β * ((n1 : ℂ) + c1) + d0) ^ 2 / α) *
        jacobiTheta₂_term m ((c0 * α + β * ((n1 : ℂ) + c1) + d0) / α) (-1 / α)) =
      cexp (2 * π * I * c0 * d0) * term2 (-1 / α) (β / α) (γ - β ^ 2 / α) (-d0) c1 c0 d1 (m, n1) := by
  rw [term2, jacobiTheta₂_term, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- **Partial inversion in the first coordinate** (two applications of Mathlib's
`jacobiTheta₂_functional_equation` give the full inversion `Ω ↦ −Ω⁻¹`). -/
theorem pi0 {α β γ : ℂ} (hα : 0 < α.im) (c0 c1 d0 d1 : ℝ)
    (hs : Summable (term2 α β γ c0 c1 d0 d1))
    (hs' : Summable (term2 (-1 / α) (β / α) (γ - β ^ 2 / α) (-d0) c1 c0 d1)) :
    Th2 α β γ c0 c1 d0 d1 = 1 / (-I * α) ^ (1 / 2 : ℂ) * cexp (2 * π * I * c0 * d0) *
      Th2 (-1 / α) (β / α) (γ - β ^ 2 / α) (-d0) c1 c0 d1 := by
  have hα0 : α ≠ 0 := fun h => by simp [h] at hα
  rw [Th2, Th2, tsum_swap_iter hs, tsum_swap_iter hs', ← tsum_mul_left]
  congr 1; funext n1
  conv_lhs => enter [1]; ext n0; rw [term2_eq_jt]
  rw [tsum_mul_left]
  change _ * jacobiTheta₂ _ _ = _
  rw [jacobiTheta₂_functional_equation, jacobiTheta₂, ← tsum_mul_left, ← tsum_mul_left,
    ← tsum_mul_left]
  congr 1; funext m
  conv_rhs => rw [mul_assoc, ← jt_dual α β γ hα0 c0 c1 d0 d1 m n1]
  ring


/-! ## Symmetries -/

theorem th2_swap (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) : Th2 α β γ c0 c1 d0 d1 = Th2 γ β α c1 c0 d1 d0 := by
  rw [Th2, Th2, ← (Equiv.prodComm ℤ ℤ).tsum_eq]
  congr 1; funext n
  simp only [term2, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  congr 1; ring

theorem th2_shift_c (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (k0 k1 : ℤ) :
    Th2 α β γ (c0 + k0) (c1 + k1) d0 d1 = Th2 α β γ c0 c1 d0 d1 := by
  rw [Th2, Th2]
  conv_rhs => rw [← (Equiv.addRight ((k0, k1) : ℤ × ℤ)).tsum_eq]
  congr 1; funext n
  simp only [term2, Equiv.coe_addRight, Prod.fst_add, Prod.snd_add]
  congr 1; push_cast; ring

theorem th2_shift_d (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (k0 k1 : ℤ) :
    Th2 α β γ c0 c1 (d0 + k0) (d1 + k1) =
      cexp (2 * π * I * (c0 * k0 + c1 * k1)) * Th2 α β γ c0 c1 d0 d1 := by
  rw [Th2, Th2, ← tsum_mul_left]
  congr 1; funext n
  have h : cexp (((-(n.1 * k0 + n.2 * k1) : ℤ) : ℂ) * (2 * π * I)) = 1 := exp_int_mul_two_pi_mul_I _
  rw [term2, term2, ← mul_one (cexp (_ + _)), ← h, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

/-! ## Duplication -/

/-- `(σ, p, q) ↦ (p + q + σ, p − q)`, a bijection `Fin 2 × ℤ × ℤ ≃ ℤ × ℤ`. -/
def dupE1 : Fin 2 × (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun w := (w.2.1 + w.2.2 + (w.1 : ℕ), w.2.1 - w.2.2)
  invFun mn := (if (mn.1 - mn.2) % 2 = 0 then 0 else 1,
    (mn.2 + (mn.1 - mn.2 - (if (mn.1 - mn.2) % 2 = 0 then 0 else 1)) / 2,
     (mn.1 - mn.2 - (if (mn.1 - mn.2) % 2 = 0 then 0 else 1)) / 2))
  left_inv w := by
    obtain ⟨σ, p, q⟩ := w
    fin_cases σ <;> simp <;> omega
  right_inv mn := by
    obtain ⟨m, n⟩ := mn
    by_cases h : (m - n) % 2 = 0 <;> simp [h] <;> omega

/-- The 2D version: `((σ₀,σ₁), (p, q)) ↦ (p + q + σ, p − q)` on `ℤ² × ℤ²`. -/
def dupE2 : (Fin 2 × Fin 2) × ((ℤ × ℤ) × (ℤ × ℤ)) ≃ (ℤ × ℤ) × (ℤ × ℤ) where
  toFun w := ((w.2.1.1 + w.2.2.1 + (w.1.1 : ℕ), w.2.1.2 + w.2.2.2 + (w.1.2 : ℕ)),
    (w.2.1.1 - w.2.2.1, w.2.1.2 - w.2.2.2))
  invFun mn :=
    let s0 : ℤ := if (mn.1.1 - mn.2.1) % 2 = 0 then 0 else 1
    let s1 : ℤ := if (mn.1.2 - mn.2.2) % 2 = 0 then 0 else 1
    ((if (mn.1.1 - mn.2.1) % 2 = 0 then 0 else 1, if (mn.1.2 - mn.2.2) % 2 = 0 then 0 else 1),
      ((mn.2.1 + (mn.1.1 - mn.2.1 - s0) / 2, mn.2.2 + (mn.1.2 - mn.2.2 - s1) / 2),
       ((mn.1.1 - mn.2.1 - s0) / 2, (mn.1.2 - mn.2.2 - s1) / 2)))
  left_inv w := by
    obtain ⟨⟨σ0, σ1⟩, ⟨p0, p1⟩, ⟨q0, q1⟩⟩ := w
    fin_cases σ0 <;> fin_cases σ1 <;> simp <;> omega
  right_inv mn := by
    obtain ⟨⟨m0, m1⟩, ⟨n0, n1⟩⟩ := mn
    by_cases h0 : (m0 - n0) % 2 = 0 <;> by_cases h1 : (m1 - n1) % 2 = 0 <;> simp [h0, h1] <;> omega

theorem dupE2_apply (σ0 σ1 : Fin 2) (p0 p1 q0 q1 : ℤ) :
    dupE2 ((σ0, σ1), ((p0, p1), (q0, q1))) =
      ((p0 + q0 + (σ0 : ℕ), p1 + q1 + (σ1 : ℕ)), (p0 - q0, p1 - q1)) := rfl

theorem dup2 {α β γ : ℂ} (c0 c1 d0 d1 : ℝ)
    (hs : Summable (fun n => ‖term2 α β γ c0 c1 d0 d1 n‖))
    (hs2 : ∀ c0' c1' d0' d1' : ℝ, Summable (fun n => ‖term2 (2 * α) (2 * β) (2 * γ) c0' c1' d0' d1' n‖)) :
    Th2 α β γ c0 c1 d0 d1 ^ 2 = ∑ σ : Fin 2 × Fin 2,
      Th2 (2 * α) (2 * β) (2 * γ) (((σ.1 : ℕ) : ℝ) / 2 + c0) (((σ.2 : ℕ) : ℝ) / 2 + c1) (2 * d0) (2 * d1) *
      Th2 (2 * α) (2 * β) (2 * γ) (((σ.1 : ℕ) : ℝ) / 2) (((σ.2 : ℕ) : ℝ) / 2) 0 0 := by
  have hprod := summable_mul_of_summable_norm hs hs
  have h2 : Summable (fun c => term2 α β γ c0 c1 d0 d1 (dupE2 c).1 *
      term2 α β γ c0 c1 d0 d1 (dupE2 c).2) := dupE2.summable_iff.2 hprod
  rw [sq, Th2, tsum_mul_tsum_of_summable_norm hs hs, ← dupE2.tsum_eq, h2.tsum_prod, tsum_fintype]
  congr 1; funext σ
  rw [Th2, Th2, tsum_mul_tsum_of_summable_norm (hs2 _ _ _ _) (hs2 _ _ _ _)]
  congr 1; funext w
  obtain ⟨σ0, σ1⟩ := σ
  obtain ⟨⟨p0, p1⟩, ⟨q0, q1⟩⟩ := w
  rw [dupE2_apply]
  simp only [term2, ← Complex.exp_add]
  congr 1; push_cast; ring

end CM24
