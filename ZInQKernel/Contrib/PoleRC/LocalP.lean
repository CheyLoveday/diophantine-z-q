import ZInQKernel.Contrib.PoleRC.Count
import ZInQKernel.RouteK.Selmer.Good

/-!
# The local images of the Kummer map of `E_ℓ`: the "only if" halves

`p`-adic proofs of the necessity directions of `LocalGood`, `LocalThree` and `LocalBad`
(Route K's `Selmer/Good.lean` is the model), and the square-class invariance of `LocM`.
-/

namespace ZInQ.Manuscript.PoleRC

open ZInQ.RouteK.Selmer

section Field

variable {K : Type*} [Field K]

theorem sqEq_of_isSquare_div {u a : K} (hu : u ≠ 0) (ha : a ≠ 0) (h : IsSquare (u / a)) :
    SqEq u a := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by rintro rfl; rw [mul_zero, div_eq_zero_iff] at hr; tauto
  exact ⟨r, hr0, by rw [sq, ← hr]; field_simp⟩

/-- **The torsion alternative for `LocM`**: a witness `x` is one of the roots `−3ℓ, ℓ, 0` (and then
`(a, b)` is a torsion class) or `x ≡ ab`, `x + 3ℓ ≡ a`, `x − ℓ ≡ b`. -/
theorem locM_torsion [CharZero K] {ℓ a b x : K} (hℓ : ℓ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : IsSquare ((x + 3 * ℓ) / a)) (h₂ : IsSquare ((x - ℓ) / b))
    (h₃ : IsSquare (x / (a * b))) :
    (x = -3 * ℓ ∧ SqEq b (-ℓ) ∧ SqEq (a * b) (-3 * ℓ)) ∨ (x = ℓ ∧ SqEq a ℓ ∧ SqEq (a * b) ℓ) ∨
      (x = 0 ∧ SqEq a (3 * ℓ) ∧ SqEq b (-ℓ)) ∨
      (x ≠ 0 ∧ x - ℓ ≠ 0 ∧ x + 3 * ℓ ≠ 0 ∧ SqEq (x + 3 * ℓ) a ∧ SqEq (x - ℓ) b ∧
        SqEq x (a * b)) := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hsq4 : ∀ (u : K), SqEq (4 * u) u := fun u => ⟨2, h2, by ring⟩
  by_cases hx3 : x = -3 * ℓ
  · left
    subst hx3
    have hm : -3 * ℓ - ℓ ≠ 0 := by
      rw [show -3 * ℓ - ℓ = -4 * ℓ by ring]; exact mul_ne_zero (by norm_num) hℓ
    have h3 : -3 * ℓ ≠ 0 := mul_ne_zero (by norm_num) hℓ
    refine ⟨rfl, ?_, (sqEq_of_isSquare_div h3 hab h₃).symm⟩
    exact (sqEq_of_isSquare_div hm hb h₂).symm.trans
      (by rw [show -3 * ℓ - ℓ = 4 * (-ℓ) by ring]; exact hsq4 _)
  by_cases hx1 : x = ℓ
  · right; left
    subst hx1
    have h4 : x + 3 * x ≠ 0 := by rw [show x + 3 * x = 4 * x by ring]; exact mul_ne_zero (by norm_num) hℓ
    refine ⟨rfl, ?_, (sqEq_of_isSquare_div hℓ hab h₃).symm⟩
    exact (sqEq_of_isSquare_div h4 ha h₁).symm.trans
      (by rw [show x + 3 * x = 4 * x by ring]; exact hsq4 _)
  by_cases hx0 : x = 0
  · right; right; left
    subst hx0
    refine ⟨rfl, ?_, ?_⟩
    · have h3 : (0 : K) + 3 * ℓ ≠ 0 := by rw [zero_add]; exact mul_ne_zero (by norm_num) hℓ
      have := (sqEq_of_isSquare_div h3 ha h₁).symm
      rwa [zero_add] at this
    · have hm : (0 : K) - ℓ ≠ 0 := by rw [zero_sub]; exact neg_ne_zero.mpr hℓ
      have := (sqEq_of_isSquare_div hm hb h₂).symm
      rwa [zero_sub] at this
  right; right; right
  have hxa : x + 3 * ℓ ≠ 0 := fun h => hx3 (by linear_combination h)
  have hxb : x - ℓ ≠ 0 := sub_ne_zero.mpr hx1
  exact ⟨hx0, hxb, hxa, sqEq_of_isSquare_div hxa ha h₁, sqEq_of_isSquare_div hxb hb h₂,
    sqEq_of_isSquare_div hx0 hab h₃⟩

end Field

end ZInQ.Manuscript.PoleRC
