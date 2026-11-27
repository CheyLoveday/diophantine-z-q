import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Model
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Algebra.Polynomial.Splits

/-!
# Lane RC18-twist: split multiplicative reduction of a quadratic twist, over the residue field

Mathlib's `HasSplitMultiplicativeReduction` asks that `splitPoly` of the reduction splits. Over a
finite field of odd characteristic, the discriminant of `splitPoly V` is `−c₄ c₆`, and that of
`splitPoly (twistInt V D c)` is `D⁵ · (−c₄ c₆)`, so twisting by a non-square exchanges split and
non-split (`splits_splitPoly_twistInt_iff`). Over `𝔽₂` the twist by `c = 1` adds `1` to the
constant term of `T² + T + (a₂ + a₃)` (`splits_splitPoly_twistInt_zmod_two_iff`).
-/

namespace ZInQ.Manuscript.RC.TwistDictionary

open WeierstrassCurve Polynomial

/-- **The discriminant of `splitPoly`**: `(a₁ c₄)² + 4 c₄ (54 b₆ − 3 b₂ b₄ + a₂ c₄) = −c₄ c₆`, over
any commutative ring. -/
theorem splitPoly_discriminant {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    (W.a₁ * W.c₄) ^ 2 + 4 * W.c₄ * (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄) =
      -(W.c₄ * W.c₆) := by
  simp only [c₄, c₆, b₂]; ring

/-- Over a field with `2 ≠ 0`, the quadratic `a X² + b X − e` with `a ≠ 0` splits iff its
discriminant `b² + 4 a e` is a square. -/
private theorem splits_quadratic_iff {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {a b e : K}
    (ha : a ≠ 0) :
    Splits (C a * X ^ 2 + C b * X - C e) ↔ IsSquare (b ^ 2 + 4 * a * e) := by
  have : NeZero (2 : K) := ⟨h2⟩
  have hform : C a * X ^ 2 + C b * X - C e = C a * X ^ 2 + C b * X + C (-e) := by
    rw [C_neg, sub_eq_add_neg]
  have hdeg : (C a * X ^ 2 + C b * X - C e).natDegree = 2 := by
    rw [hform]; exact natDegree_quadratic ha
  have hdeg' : (C a * X ^ 2 + C b * X - C e).degree ≠ 0 := by
    rw [hform, degree_quadratic ha]; decide
  have heval : ∀ x, (C a * X ^ 2 + C b * X - C e).eval x = a * (x * x) + b * x + -e := by
    intro x; simp only [eval_sub, eval_add, eval_mul, eval_C, eval_pow, eval_X]; ring
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero hdeg'
    rw [heval] at hx
    have hd := discrim_eq_sq_of_quadratic_eq_zero hx
    rw [discrim] at hd
    exact ⟨2 * a * x + b, by linear_combination hd⟩
  · rintro ⟨s, hs⟩
    obtain ⟨x, hx⟩ := exists_quadratic_eq_zero (b := b) (c := -e) ha
      ⟨s, by rw [discrim]; linear_combination hs⟩
    exact Splits.of_natDegree_eq_two hdeg (by rw [heval]; exact hx)

/-- Over a field with `2 ≠ 0`, if `c₄ ≠ 0` then `splitPoly W` splits iff `−c₄ c₆` is a square. -/
theorem splits_splitPoly_iff_isSquare {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) (hc₄ : W.c₄ ≠ 0) :
    Splits (splitPoly W) ↔ IsSquare (-(W.c₄ * W.c₆)) := by
  rw [splitPoly, splits_quadratic_iff h2 hc₄, splitPoly_discriminant]

/-- In a finite field, for `D ≠ 0` and `z ≠ 0`, `D⁵ z` is a square iff (`z` is a square iff `D` is
a square): the quadratic character is multiplicative with values `±1`. -/
private theorem isSquare_pow_five_mul_iff {F : Type*} [Field F] [Fintype F] {D z : F}
    (hD : D ≠ 0) (hz : z ≠ 0) : IsSquare (D ^ 5 * z) ↔ (IsSquare z ↔ IsSquare D) := by
  classical
  have h5 : D ^ 5 * z ≠ 0 := mul_ne_zero (pow_ne_zero 5 hD) hz
  rw [← quadraticChar_one_iff_isSquare h5, ← quadraticChar_one_iff_isSquare hz,
    ← quadraticChar_one_iff_isSquare hD, map_mul, map_pow]
  rcases quadraticChar_dichotomy hD with h | h <;>
    rcases quadraticChar_dichotomy hz with h' | h' <;> rw [h, h'] <;> norm_num

/-- **Split versus non-split for a twist, odd characteristic** (PROVED): over a finite field of odd
characteristic, if `c₄ ≠ 0` and `c₆ ≠ 0` (a node), then `splitPoly` of the twist by `D = 1 + 4c ≠ 0`
splits iff (`splitPoly V` splits iff `D` is a square). -/
theorem splits_splitPoly_twistInt_iff {k : Type*} [Field k] [Fintype k] (hk : ringChar k ≠ 2)
    (V : WeierstrassCurve k) (hc₄ : V.c₄ ≠ 0) (hc₆ : V.c₆ ≠ 0) {D c : k} (h : D = 1 + 4 * c)
    (hD : D ≠ 0) :
    Splits (splitPoly (twistInt V D c)) ↔ (Splits (splitPoly V) ↔ IsSquare D) := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hc₄' : (twistInt V D c).c₄ ≠ 0 := by
    rw [twistInt_c₄ V h]; exact mul_ne_zero (pow_ne_zero 2 hD) hc₄
  rw [splits_splitPoly_iff_isSquare h2 _ hc₄', splits_splitPoly_iff_isSquare h2 V hc₄,
    twistInt_c₄ V h, twistInt_c₆ V h,
    show -(D ^ 2 * V.c₄ * (D ^ 3 * V.c₆)) = D ^ 5 * -(V.c₄ * V.c₆) by ring]
  exact isSquare_pow_five_mul_iff hD (neg_ne_zero.mpr (mul_ne_zero hc₄ hc₆))

/-- Every element of `ZMod 2` is `0` or `1` (PROVED). -/
private theorem zmod_two_eq_zero_or_eq_one : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by
  decide

/-- If `x² + x + t = 0` has a root in `ZMod 2`, then `t = 0` (PROVED). -/
private theorem zmod_two_eq_zero_of_sq_add_add : ∀ t x : ZMod 2, x ^ 2 + x + t = 0 → t = 0 := by
  decide

/-- Over `𝔽₂`, if `a₁ = 1` then `splitPoly W = X² + X + (a₂ + a₃)`. -/
theorem splitPoly_zmod_two (W : WeierstrassCurve (ZMod 2)) (h₁ : W.a₁ = 1) :
    splitPoly W = X ^ 2 + X + C (W.a₂ + W.a₃) := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  have hc₄ : W.c₄ = 1 := by
    simp only [c₄, b₂, b₄, h₁]
    linear_combination (4 * W.a₂ + 8 * W.a₂ ^ 2 - 24 * W.a₄ - 12 * W.a₃) * h2
  have hk : -(54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄) = W.a₂ + W.a₃ := by
    simp only [hc₄, b₂, b₄, b₆, h₁]
    linear_combination (-27 * W.a₃ ^ 2 - 108 * W.a₆ + 3 * W.a₄ + W.a₃ + 12 * W.a₂ * W.a₄ +
      6 * W.a₂ * W.a₃ - W.a₂) * h2
  rw [splitPoly, sub_eq_add_neg, ← C_neg, hk, hc₄, h₁]
  simp

/-- Over `𝔽₂`, `X² + X + t` splits iff `t = 0`. -/
theorem splits_X_sq_add_X_add_C_zmod_two (t : ZMod 2) :
    Splits (X ^ 2 + X + C t : (ZMod 2)[X]) ↔ t = 0 := by
  have hform : (X ^ 2 + X + C t : (ZMod 2)[X]) = C 1 * X ^ 2 + C 1 * X + C t := by simp
  have hdeg : (X ^ 2 + X + C t : (ZMod 2)[X]).natDegree = 2 := by
    rw [hform]; exact natDegree_quadratic one_ne_zero
  have hdeg' : (X ^ 2 + X + C t : (ZMod 2)[X]).degree ≠ 0 := by
    rw [hform, degree_quadratic one_ne_zero]; decide
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero hdeg'
    simp only [eval_add, eval_pow, eval_X, eval_C] at hx
    exact zmod_two_eq_zero_of_sq_add_add t x hx
  · rintro rfl
    exact Splits.of_natDegree_eq_two (x := 0) hdeg (by simp)

/-- **Split versus non-split for the Artin–Schreier twist over `𝔽₂`** (PROVED): if `c₄ ≠ 0`, then
`splitPoly (twistInt V 1 c)` splits iff (`splitPoly V` splits iff `c = 0`). -/
theorem splits_splitPoly_twistInt_zmod_two_iff (V : WeierstrassCurve (ZMod 2)) (hc₄ : V.c₄ ≠ 0)
    (c : ZMod 2) :
    Splits (splitPoly (twistInt V 1 c)) ↔ (Splits (splitPoly V) ↔ c = 0) := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  have h₁ : V.a₁ = 1 := by
    rcases zmod_two_eq_zero_or_eq_one V.a₁ with h | h
    · exfalso; apply hc₄
      simp only [c₄, b₂, b₄, h]
      linear_combination (8 * V.a₂ ^ 2 - 24 * V.a₄) * h2
    · exact h
  rw [splitPoly_zmod_two _ (by rw [twistInt_a₁]; exact h₁), splitPoly_zmod_two V h₁,
    splits_X_sq_add_X_add_C_zmod_two, splits_X_sq_add_X_add_C_zmod_two]
  simp only [twistInt, h₁]
  generalize V.a₂ = u
  generalize V.a₃ = v
  revert u v c
  decide

end ZInQ.Manuscript.RC.TwistDictionary
