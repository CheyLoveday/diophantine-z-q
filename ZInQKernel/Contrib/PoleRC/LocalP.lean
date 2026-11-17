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

section Padic

variable {p : ℕ} [hp : Fact p.Prime]

theorem padic_norm_three (hp3 : p ≠ 3) : ‖(3 : ℚ_[p])‖ = 1 := by
  have := padic_norm_intCast_eq_one (p := p) (c := 3) (by
    intro h
    have : p ∣ 3 := by exact_mod_cast h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp this))
  simpa using this

theorem padic_norm_mul_one {x y : ℚ_[p]} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ‖x * y‖ = 1 := by
  rw [norm_mul, hx, hy, one_mul]

/-- `LocM` at a good prime puts `a` and `b` in the square classes of units. -/
theorem locM_good_units (hp2 : p ≠ 2) (hp3 : p ≠ 3) {L A B : ℚ_[p]} (hL : ‖L‖ = 1)
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (h : LocM ℚ_[p] L A B) :
    ∃ u w : ℚ_[p], ‖u‖ = 1 ∧ ‖w‖ = 1 ∧ SqEq A u ∧ SqEq B w := by
  have hL0 : L ≠ 0 := by intro h0; rw [h0, norm_zero] at hL; exact zero_ne_one hL
  have hn3 := padic_norm_three (p := p) hp3
  have hn4 : ‖(4 : ℚ_[p])‖ = 1 := by
    rw [show (4 : ℚ_[p]) = 2 * 2 by norm_num, norm_mul, padic_norm_two hp2, one_mul]
  have hnL : ‖-L‖ = 1 := by rw [norm_neg, hL]
  have hn3L : ‖3 * L‖ = 1 := padic_norm_mul_one hn3 hL
  have hn4L : ‖4 * L‖ = 1 := padic_norm_mul_one hn4 hL
  rcases h with ⟨hsa, hsb⟩ | ⟨x, h₁, h₂, h₃⟩
  · exact ⟨1, 1, norm_one, norm_one, (sqEq_iff_isSquare_mul hA0 one_ne_zero).mpr (by simpa),
      (sqEq_iff_isSquare_mul hB0 one_ne_zero).mpr (by simpa)⟩
  rcases locM_torsion hL0 hA0 hB0 h₁ h₂ h₃ with ⟨-, hb', hab'⟩ | ⟨-, ha', hab'⟩ | ⟨-, ha', hb'⟩ |
    ⟨hx0, hxb, hxa, hxa', hxb', hxab⟩
  · have ha' : SqEq A (-3 * L * -L) := sqEq_of_mul_sqEq hab' hb' (neg_ne_zero.mpr hL0)
    exact ⟨_, _, by rw [show -3 * L * -L = 3 * L * L by ring, norm_mul, hn3L, hL, one_mul],
      hnL, ha', hb'⟩
  · have hba : SqEq (B * A) L := by rw [mul_comm]; exact hab'
    exact ⟨_, _, hL, padic_norm_mul_one hL hL, ha', sqEq_of_mul_sqEq hba ha' hL0⟩
  · exact ⟨_, _, hn3L, hnL, ha', hb'⟩
  rcases lt_trichotomy ‖x‖ 1 with hlt | heq | hgt
  · have e₂ : SqEq (x - L) (-L) := by
      rw [show x - L = -L + x by ring]; exact sqEq_add_of_norm_lt hp2 (by rwa [hnL])
    have e₃ : SqEq (x + 3 * L) (3 * L) := by
      rw [add_comm]; exact sqEq_add_of_norm_lt hp2 (by rwa [hn3L])
    exact ⟨_, _, hn3L, hnL, hxa'.symm.trans e₃, hxb'.symm.trans e₂⟩
  · have hle : ∀ c : ℚ_[p], ‖c‖ = 1 → ‖x + c‖ ≤ 1 := fun c hc =>
      (Padic.nonarchimedean _ _).trans (by rw [heq, hc, max_self])
    by_cases hm : ‖x - L‖ < 1
    · have hp1 : ‖x + 3 * L‖ = 1 := by
        refine le_antisymm (hle _ hn3L) (not_lt.mp fun hlt' => ?_)
        have := Padic.nonarchimedean (x + 3 * L) (-(x - L))
        rw [show x + 3 * L + -(x - L) = 4 * L by ring, hn4L, norm_neg] at this
        exact absurd this (not_le.mpr (max_lt hlt' hm))
      have hba : SqEq (B * A) x := by rw [mul_comm]; exact hxab.symm
      exact ⟨_, _, hp1, padic_norm_mul_one heq hp1, hxa'.symm,
        sqEq_of_mul_sqEq hba hxa'.symm hxa⟩
    · have hsub : ‖x - L‖ ≤ 1 := by rw [sub_eq_add_neg]; exact hle _ hnL
      have hxL : ‖x - L‖ = 1 := le_antisymm hsub (not_lt.mp hm)
      by_cases hm2 : ‖x + 3 * L‖ < 1
      · exact ⟨_, _, padic_norm_mul_one heq hxL, hxL,
          sqEq_of_mul_sqEq hxab.symm hxb'.symm hxb, hxb'.symm⟩
      · exact ⟨_, _, le_antisymm (hle _ hn3L) (not_lt.mp hm2), hxL, hxa'.symm, hxb'.symm⟩
  · have e₂ : SqEq (x - L) x := by
      rw [sub_eq_add_neg]; exact sqEq_add_of_norm_lt hp2 (by rwa [hnL])
    have e₃ : SqEq (x + 3 * L) x := sqEq_add_of_norm_lt hp2 (by rwa [hn3L])
    have hb' : SqEq B x := hxb'.symm.trans e₂
    have hab : SqEq (A * B) x := hxab.symm
    have ha' : SqEq A 1 := by
      have := sqEq_of_mul_sqEq hab hb' hx0
      exact (this.trans ⟨1, one_ne_zero, by ring⟩ : SqEq A (1 * x ^ 2)).of_mul_sq hx0
    exact ⟨1, 1, norm_one, norm_one, ha', hb'.trans ((hxa'.symm.trans e₃).symm.trans ha')⟩

end Padic

end ZInQ.Manuscript.PoleRC
