import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

open Complex
open scoped Real

noncomputable section

namespace ZInQ.JacobiLambda

lemma summable_norm_term (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ => ‖jacobiTheta₂_term n z τ‖) :=
  (summable_pow_mul_jacobiTheta₂_term_bound |z.im| hτ 0).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => by simpa using norm_jacobiTheta₂_term_le hτ (le_refl _) (le_refl _) n)

lemma hasSum_prod_term (z w : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun p : ℤ × ℤ => jacobiTheta₂_term p.1 z τ * jacobiTheta₂_term p.2 w τ)
      (jacobiTheta₂ z τ * jacobiTheta₂ w τ) := by
  have := summable_mul_of_summable_norm (summable_norm_term z hτ) (summable_norm_term w hτ)
  rw [jacobiTheta₂, jacobiTheta₂,
    tsum_mul_tsum_of_summable_norm (summable_norm_term z hτ) (summable_norm_term w hτ)]
  exact this.hasSum

/-- `(a, b) ↦ (a + b, a − b)` and `(a, b) ↦ (a + b + 1, a − b)`. -/
def dupMap : (ℤ × ℤ) ⊕ (ℤ × ℤ) → ℤ × ℤ
  | Sum.inl p => (p.1 + p.2, p.1 - p.2)
  | Sum.inr p => (p.1 + p.2 + 1, p.1 - p.2)

lemma dupMap_bijective : Function.Bijective dupMap := by
  constructor
  · rintro (⟨a, b⟩ | ⟨a, b⟩) (⟨c, d⟩ | ⟨c, d⟩) h <;>
      simp only [dupMap, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h ⊢ <;>
      omega
  · rintro ⟨n, m⟩
    rcases Int.even_or_odd (n + m) with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨Sum.inl (k, n - k), by simp only [dupMap, Prod.mk.injEq]; omega⟩
    · exact ⟨Sum.inr (k, n - k - 1), by simp only [dupMap, Prod.mk.injEq]; omega⟩

/-- **The duplication formula** for Mathlib's `jacobiTheta₂`:
`θ(z,τ) θ(w,τ) = θ(z+w,2τ) θ(z−w,2τ) + e^{2πiz+πiτ} θ(z+w+τ,2τ) θ(z−w+τ,2τ)`. -/
theorem jacobiTheta₂_mul_jacobiTheta₂ (z w : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta₂ z τ * jacobiTheta₂ w τ =
      jacobiTheta₂ (z + w) (2 * τ) * jacobiTheta₂ (z - w) (2 * τ) +
      cexp (2 * π * I * z + π * I * τ) *
        (jacobiTheta₂ (z + w + τ) (2 * τ) * jacobiTheta₂ (z - w + τ) (2 * τ)) := by
  have h2 : 0 < (2 * τ).im := by simp; linarith
  set f : ℤ × ℤ → ℂ := fun p => jacobiTheta₂_term p.1 z τ * jacobiTheta₂_term p.2 w τ with hf_def
  have hf := hasSum_prod_term z w hτ
  have hA := hasSum_prod_term (z + w) (z - w) h2
  have hB := (hasSum_prod_term (z + w + τ) (z - w + τ) h2).mul_left (cexp (2 * π * I * z + π * I * τ))
  have hS : HasSum (f ∘ dupMap) _ := HasSum.sum (f := f ∘ dupMap) (a := _) (b := _)
    (by
      convert hA using 1
      funext p
      simp only [Function.comp, dupMap, hf_def, jacobiTheta₂_term, ← Complex.exp_add]
      congr 1; push_cast; ring)
    (by
      convert hB using 1
      funext p
      simp only [Function.comp, dupMap, hf_def, jacobiTheta₂_term, ← Complex.exp_add]
      congr 1; push_cast; ring)
  have e := Equiv.ofBijective dupMap dupMap_bijective
  rw [show (f ∘ dupMap) = f ∘ (Equiv.ofBijective dupMap dupMap_bijective) from rfl,
    Equiv.hasSum_iff] at hS
  exact hf.unique hS

/-! ## Landen's transformation and Jacobi's quartic identity -/

/-- local copies of gz-weil's theta constants (identical definitions) -/
def thetaTwo (t : ℂ) : ℂ := cexp (π * I * t / 4) * jacobiTheta₂ (t / 2) t
def thetaThree (t : ℂ) : ℂ := jacobiTheta₂ 0 t
def thetaFour (t : ℂ) : ℂ := jacobiTheta₂ (1 / 2) t

lemma thetaTwo_two_mul (τ : ℂ) :
    thetaTwo (2 * τ) = cexp (π * I * τ / 2) * jacobiTheta₂ τ (2 * τ) := by
  rw [thetaTwo, mul_div_cancel_left₀ _ two_ne_zero]
  congr 2; ring

lemma thetaTwo_two_mul_sq (τ : ℂ) :
    thetaTwo (2 * τ) ^ 2 = cexp (π * I * τ) * jacobiTheta₂ τ (2 * τ) ^ 2 := by
  rw [thetaTwo_two_mul, mul_pow, ← Complex.exp_nat_mul]
  congr 2; push_cast; ring

/-- `θ(τ + 1/2, 2τ) = 0`. -/
lemma jacobiTheta₂_add_half_two_mul (τ : ℂ) : jacobiTheta₂ (τ + 1 / 2) (2 * τ) = 0 := by
  have h1 : jacobiTheta₂ (τ - 1 / 2) (2 * τ) = jacobiTheta₂ (τ + 1 / 2) (2 * τ) := by
    rw [← jacobiTheta₂_add_left]; congr 1; ring
  have h2 := jacobiTheta₂_add_left' (-(τ + 1 / 2)) (2 * τ)
  rw [jacobiTheta₂_neg_left, show -(τ + 1 / 2) + 2 * τ = τ - 1 / 2 by ring, h1,
    show -π * I * (2 * τ + 2 * -(τ + 1 / 2)) = π * I by ring, Complex.exp_pi_mul_I] at h2
  linear_combination h2 / 2

theorem landen_three {τ : ℂ} (hτ : 0 < τ.im) :
    thetaThree τ ^ 2 = thetaThree (2 * τ) ^ 2 + thetaTwo (2 * τ) ^ 2 := by
  have h := jacobiTheta₂_mul_jacobiTheta₂ 0 0 hτ
  simp only [add_zero, sub_zero, zero_add, mul_zero] at h
  rw [thetaTwo_two_mul_sq, thetaThree, thetaThree, sq, h]
  ring_nf

theorem landen_four {τ : ℂ} (hτ : 0 < τ.im) :
    thetaFour τ ^ 2 = thetaThree (2 * τ) ^ 2 - thetaTwo (2 * τ) ^ 2 := by
  have h := jacobiTheta₂_mul_jacobiTheta₂ (1 / 2) (1 / 2) hτ
  rw [show (1 / 2 : ℂ) + 1 / 2 = 0 + 1 by norm_num, sub_self, jacobiTheta₂_add_left,
    show (0 : ℂ) + 1 + τ = τ + 1 by ring, jacobiTheta₂_add_left, zero_add,
    show 2 * π * I * (1 / 2) + π * I * τ = π * I + π * I * τ by ring, Complex.exp_add,
    Complex.exp_pi_mul_I] at h
  rw [thetaTwo_two_mul_sq, thetaThree, thetaFour, sq, h]
  ring

theorem landen_two {τ : ℂ} (hτ : 0 < τ.im) :
    thetaTwo τ ^ 2 = 2 * thetaTwo (2 * τ) * thetaThree (2 * τ) := by
  have h := jacobiTheta₂_mul_jacobiTheta₂ (τ / 2) (τ / 2) hτ
  have h2 := jacobiTheta₂_add_left' 0 (2 * τ)
  rw [zero_add] at h2
  rw [show τ / 2 + τ / 2 = τ by ring, sub_self, zero_add,
    show τ + τ = 2 * τ by ring, h2] at h
  rw [thetaTwo, thetaTwo_two_mul, thetaThree, mul_pow, sq (jacobiTheta₂ (τ / 2) τ), h]
  have e1 : cexp (π * I * τ / 4) ^ 2 = cexp (π * I * τ / 2) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : cexp (2 * π * I * (τ / 2) + π * I * τ) * cexp (-π * I * (2 * τ + 2 * 0)) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; ring
  rw [e1]
  linear_combination (cexp (π * I * τ / 2) * jacobiTheta₂ τ (2 * τ) * jacobiTheta₂ 0 (2 * τ)) * e2

theorem landen_three_four {τ : ℂ} (hτ : 0 < τ.im) :
    thetaThree τ * thetaFour τ = thetaFour (2 * τ) ^ 2 := by
  have h := jacobiTheta₂_mul_jacobiTheta₂ 0 (1 / 2) hτ
  rw [zero_add, zero_sub, jacobiTheta₂_neg_left, show (1 / 2 : ℂ) + τ = τ + 1 / 2 by ring,
    jacobiTheta₂_add_half_two_mul] at h
  rw [thetaThree, thetaFour, thetaFour, h]
  ring

/-- **Jacobi's quartic identity** `θ₃⁴ = θ₂⁴ + θ₄⁴`. -/
theorem jacobi_quartic {σ : ℂ} (hσ : 0 < σ.im) :
    thetaThree σ ^ 4 = thetaTwo σ ^ 4 + thetaFour σ ^ 4 := by
  have hτ : 0 < (σ / 2).im := by simp; linarith
  have e : 2 * (σ / 2) = σ := by ring
  have h3 := landen_three hτ
  have h4 := landen_four hτ
  have h34 := landen_three_four hτ
  rw [e] at h3 h4 h34
  have : thetaFour σ ^ 4 = (thetaThree (σ / 2) * thetaFour (σ / 2)) ^ 2 := by rw [h34]; ring
  rw [this, mul_pow, h3, h4]
  ring

end ZInQ.JacobiLambda
