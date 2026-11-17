import ZInQKernel.Contrib.OneProof.GrossZagierPlane

noncomputable section

namespace ZInQ.GZDict2

/-! ## D1 (algebraic): the rational map defined by `φ^*` extends to every place -/

section Center

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The Weierstrass equation of `E` for a pair `(x, y)` of elements of a `ℚ`-algebra. -/
def WEqK (E : WeierstrassCurve ℚ) (x y : K) : Prop :=
  y ^ 2 + algebraMap ℚ K E.a₁ * x * y + algebraMap ℚ K E.a₃ * y =
    x ^ 3 + algebraMap ℚ K E.a₂ * x ^ 2 + algebraMap ℚ K E.a₄ * x + algebraMap ℚ K E.a₆

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

omit [Algebra ℚ K] in
theorem v_mul_le_of_le_one {v : Valuation K Γ} {a b : K} (ha : v a ≤ 1) : v (a * b) ≤ v b := by
  rw [map_mul]; exact mul_le_of_le_one_left' ha

/-- **Hartshorne I.6.8 for a Weierstrass cubic, valuation form** (the valuative criterion of
properness for `E ⊂ ℙ²`). Let `v` be a valuation of a field `K ⊇ ℚ` that is `≤ 1` on `ℚ` (a place of
`K/ℚ`) and `(x, y) ∈ K²` a point of `E`. Then either `x` and `y` are integral (`v x ≤ 1`, `v y ≤ 1`:
the place has center the affine point `(x̄, ȳ)`), or `1 < v x < v y`, so `v (1/y) < 1` and
`v (x/y) < 1`: `[x : y : 1] = [x/y : 1 : 1/y]` reduces to `[0 : 1 : 0] = O`. -/
theorem center_of_wEq (E : WeierstrassCurve ℚ) (v : Valuation K Γ)
    (hv : ∀ c : ℚ, v (algebraMap ℚ K c) ≤ 1) {x y : K} (h : WEqK E x y) :
    (v x ≤ 1 ∧ v y ≤ 1) ∨ (1 < v x ∧ v x < v y) := by
  set A := algebraMap ℚ K E.a₁ * x + algebraMap ℚ K E.a₃
  set C := algebraMap ℚ K E.a₂ * x ^ 2 + algebraMap ℚ K E.a₄ * x + algebraMap ℚ K E.a₆
  have hyA : y ^ 2 = (x ^ 3 + C) - A * y := by
    simp only [A, C]; unfold WEqK at h; linear_combination h
  rcases le_or_gt (v x) 1 with hx | hx
  · -- integral case
    refine Or.inl ⟨hx, ?_⟩
    by_contra hy
    push Not at hy
    have hA : v A ≤ 1 := by
      refine (v.map_add _ _).trans (max_le ?_ (hv _))
      exact (v_mul_le_of_le_one (hv _)).trans hx
    have hx3 : v (x ^ 3) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ zero_le hx
    have hC : v C ≤ 1 := by
      refine (v.map_add _ _).trans (max_le ((v.map_add _ _).trans (max_le ?_ ?_)) (hv _))
      · exact (v_mul_le_of_le_one (hv _)).trans (by rw [map_pow]; exact pow_le_one₀ zero_le hx)
      · exact (v_mul_le_of_le_one (hv _)).trans hx
    have hy0 : 0 < v y := lt_trans zero_lt_one hy
    have h1 : v (y ^ 2) ≤ v y := by
      rw [hyA]
      refine (v.map_sub _ _).trans (max_le ((v.map_add _ _).trans (max_le ?_ ?_)) ?_)
      · exact hx3.trans hy.le
      · exact hC.trans hy.le
      · exact v_mul_le_of_le_one hA
    rw [map_pow, sq] at h1
    exact absurd h1 (not_le.2 (lt_mul_of_one_lt_left hy0 hy))
  · -- polar case
    refine Or.inr ⟨hx, ?_⟩
    by_contra hy
    push Not at hy
    have hx0 : 0 < v x := lt_trans zero_lt_one hx
    have hA : v A ≤ v x := by
      refine (v.map_add _ _).trans (max_le (v_mul_le_of_le_one (hv _)) ((hv _).trans hx.le))
    have hx2 : v x ≤ v x ^ 2 := by
      rw [sq]; exact le_mul_of_one_le_left' hx.le
    have hC : v C ≤ v x ^ 2 := by
      refine (v.map_add _ _).trans (max_le ((v.map_add _ _).trans (max_le ?_ ?_)) ?_)
      · rw [← map_pow]; exact v_mul_le_of_le_one (hv _)
      · exact (v_mul_le_of_le_one (hv _)).trans hx2
      · exact (hv _).trans (hx.le.trans hx2)
    have hx23 : v x ^ 2 < v x ^ 3 := by
      rw [pow_succ (v x) 2]; exact lt_mul_of_one_lt_right (pow_pos hx0 2) hx
    have hB : v (x ^ 3 + C) = v x ^ 3 := by
      rw [← map_pow, add_comm]
      exact v.map_add_eq_of_lt_right (by rw [map_pow]; exact lt_of_le_of_lt hC hx23)
    have hle : v (x ^ 3 + C) ≤ v x ^ 2 := by
      rw [show x ^ 3 + C = y ^ 2 + A * y by rw [hyA]; ring]
      refine (v.map_add _ _).trans (max_le ?_ ?_)
      · rw [map_pow]; exact pow_le_pow_left₀ zero_le hy 2
      · rw [map_mul, sq]; exact mul_le_mul' hA hy
    rw [hB] at hle
    exact absurd hle (not_le.2 hx23)

/-- The place form for a valuation subring `O ⊇ ℚ` of `K`: either `x, y ∈ O`, or `1/y` and `x/y` lie in
the maximal ideal (`v < 1`). -/
theorem center_of_wEq_subring (E : WeierstrassCurve ℚ) (O : ValuationSubring K)
    (hO : ∀ c : ℚ, algebraMap ℚ K c ∈ O) {x y : K} (h : WEqK E x y) :
    (x ∈ O ∧ y ∈ O) ∨
      (x ∉ O ∧ y ≠ 0 ∧ O.valuation y⁻¹ < 1 ∧ O.valuation (x * y⁻¹) < 1) := by
  rcases center_of_wEq E O.valuation (fun c => O.valuation_le_one ⟨_, hO c⟩) h with
    ⟨hx, hy⟩ | ⟨hx, hxy⟩
  · exact Or.inl ⟨(O.valuation_le_one_iff x).1 hx, (O.valuation_le_one_iff y).1 hy⟩
  · have hy1 : 1 < O.valuation y := lt_trans hx hxy
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy1
    refine Or.inr ⟨fun hxO => absurd ((O.valuation_le_one_iff x).2 hxO) (not_le.2 hx), hy0, ?_, ?_⟩
    · rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hy1
    · rw [map_mul, map_inv₀, ← div_eq_mul_inv]
      exact (div_lt_one₀ (lt_trans zero_lt_one hy1)).2 hxy

end Center

end ZInQ.GZDict2
