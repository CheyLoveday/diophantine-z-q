import ZInQKernel.Contrib.OneProof.GrossZagierPlane

/-!
# gz-dict2: dictionary step D1 — the rational map defined by `φ^*` extends at every place

Task gz-dict2 (2026-11-16/17). Report: `docs/research/gz-dict2.md`.

The leaf `GZDict2.GrossZagierPlaneOptCd` gives `φ : X₀(N) → E` by `φ^* : ℚ(E) →ₐ[ℚ] ℚ(X₀(N))`.
Hartshorne I.6.12 identifies such embeddings with nonconstant morphisms of the smooth projective
curves; the direction the leaf needs (an embedding comes from a morphism) is Hartshorne I.6.8 for
the target `E`: the rational map extends at every point of the source. `X₀(N)` is not a scheme in
this tree, so this file proves that extension in the two models of the source that the tree has.

* **Places of `ℚ(X₀(N))`** (Hartshorne I.6: the abstract curve of a function field is its set of
  places): `center_of_wEq`, `center_of_wEq_subring`, `phi_center`. For every valuation `v` of a
  field `K ⊇ ℚ` trivial on `ℚ` and every point `(x, y) ∈ E(K)`, either `x, y` are `v`-integral (the
  center is the affine point `(x̄, ȳ)`) or `1 < v x < v y` (the center is `O = [0 : 1 : 0]`).
* **Points `τ ∈ ℍ` of `X₀(N)(ℂ)`** (the uniformization): `modPt_cases`, `modPt_plane_cases`. The
  leaf's value `modPt E (ratFn Px Qx) (ratFn Py Qy) τ` is `(lim x, lim y)` when `φ^*(x)` has a
  finite limit at `τ` (then so does `φ^*(y)`, and the limit lies on `E`), and `O` exactly when
  `φ^*(x)` has a pole at `τ`: the continuous extension of `τ ↦ φ(τ)`, with no junk values.

No `sorry`, no `axiom`.
-/

noncomputable section

open UpperHalfPlane Filter Topology
open scoped WeierstrassCurve.Affine

namespace ZInQ.GZDict2

open ZInQ.GZAlg

/-- The Weierstrass equation of `E` for a pair `(x, y)` of elements of a field (coefficients `ℚ → K`
by the cast). -/
def WEqR {K : Type*} [Field K] (E : WeierstrassCurve ℚ) (x y : K) : Prop :=
  y ^ 2 + (E.a₁ : K) * x * y + (E.a₃ : K) * y =
    x ^ 3 + (E.a₂ : K) * x ^ 2 + (E.a₄ : K) * x + (E.a₆ : K)

theorem WEqR.map {K L : Type*} [Field K] [Field L] {E : WeierstrassCurve ℚ} {x y : K}
    (h : WEqR E x y) (f : K →+* L) : WEqR E (f x) (f y) := by
  have := congrArg f h
  simp only [map_add, map_mul, map_pow, map_ratCast] at this
  exact this

/-! ## D1 (algebraic): every place of `K ⊇ ℚ` has a center on `E` -/

section Center

variable {K : Type*} [Field K]

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

theorem v_mul_le_of_le_one {v : Valuation K Γ} {a b : K} (ha : v a ≤ 1) : v (a * b) ≤ v b := by
  rw [map_mul]; exact mul_le_of_le_one_left' ha

/-- **Hartshorne I.6.8 for a Weierstrass cubic, valuation form** (the valuative criterion of
properness for `E ⊂ ℙ²`). Let `v` be a valuation of a field `K ⊇ ℚ` that is `≤ 1` on `ℚ` (a place of
`K/ℚ`) and `(x, y) ∈ K²` a point of `E`. Then either `x` and `y` are integral (`v x ≤ 1`, `v y ≤ 1`:
the place has center the affine point `(x̄, ȳ)`), or `1 < v x < v y`, so `v (1/y) < 1` and
`v (x/y) < 1`: `[x : y : 1] = [x/y : 1 : 1/y]` reduces to `[0 : 1 : 0] = O`. -/
theorem center_of_wEq (E : WeierstrassCurve ℚ) (v : Valuation K Γ)
    (hv : ∀ c : ℚ, v (c : K) ≤ 1) {x y : K} (h : WEqR E x y) :
    (v x ≤ 1 ∧ v y ≤ 1) ∨ (1 < v x ∧ v x < v y) := by
  set A := (E.a₁ : K) * x + (E.a₃ : K)
  set C := (E.a₂ : K) * x ^ 2 + (E.a₄ : K) * x + (E.a₆ : K)
  have hyA : y ^ 2 = (x ^ 3 + C) - A * y := by
    simp only [A, C]; unfold WEqR at h; linear_combination h
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
    (hO : ∀ c : ℚ, (c : K) ∈ O) {x y : K} (h : WEqR E x y) :
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

/-! ## D1 (analytic): `modPt` is the extension of the rational map `(X, Y)` at every point -/

/-- **The value of `φ = (X, Y)` at `τ` is the center of the place `ord_τ`.** Let `E` be elliptic and
`X, Y` meromorphic at `τ ∈ ℍ`, satisfying the Weierstrass equation of `E` on a punctured
neighbourhood of `τ`. Either `X` has a finite limit `x₀` at `τ`; then `Y` has a finite limit `y₀`,
`(x₀, y₀)` is a point of `E(ℂ)`, and `modPt E X Y τ = (x₀, y₀)`. Or `X` has a pole at `τ`
(`‖X‖ → ∞`), and `modPt E X Y τ = O`. So `modPt` takes no junk value: it is the continuous
extension of the rational map `τ ↦ (X(τ), Y(τ))` (Hartshorne I.6.8 / Silverman II.2.1 on the
Riemann surface). -/
theorem modPt_cases (E : WeierstrassCurve ℚ) [E.IsElliptic] {X Y : ℍ → ℂ} {τ : ℍ}
    (hX : MeromorphicAt (X ∘ ofComplex) (τ : ℂ)) (hY : MeromorphicAt (Y ∘ ofComplex) (τ : ℂ))
    (heq : ∀ᶠ z in 𝓝[≠] (τ : ℂ), (E⁄ℂ).Equation (X (ofComplex z)) (Y (ofComplex z))) :
    (∃ (x₀ y₀ : ℂ) (h : (E⁄ℂ).Nonsingular x₀ y₀),
        Tendsto (X ∘ ofComplex) (𝓝[≠] (τ : ℂ)) (𝓝 x₀) ∧
        Tendsto (Y ∘ ofComplex) (𝓝[≠] (τ : ℂ)) (𝓝 y₀) ∧
        ZInQ.GZModuli.modPt E X Y τ = .some x₀ y₀ h) ∨
    (Tendsto (fun z => ‖X (ofComplex z)‖) (𝓝[≠] (τ : ℂ)) atTop ∧
        ZInQ.GZModuli.modPt E X Y τ = 0) := by
  rcases lt_or_ge (meromorphicOrderAt (X ∘ ofComplex) (τ : ℂ)) 0 with ho | ho
  · -- pole
    have hcob : Tendsto (fun z => ‖X (ofComplex z)‖) (𝓝[≠] (τ : ℂ)) atTop := by
      have := tendsto_cobounded_of_meromorphicOrderAt_neg ho
      rw [← tendsto_norm_atTop_iff_cobounded] at this
      exact this
    refine Or.inr ⟨hcob, ?_⟩
    unfold ZInQ.GZModuli.modPt
    split_ifs with h
    · obtain ⟨p, -, hp, -⟩ := h
      exact absurd hcob (not_tendsto_atTop_of_tendsto_nhds hp.norm)
    · rfl
  · -- finite limit
    obtain ⟨x₀, hx₀⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hX ho
    -- `Y` has a finite limit
    have hoY : 0 ≤ meromorphicOrderAt (Y ∘ ofComplex) (τ : ℂ) := by
      by_contra hneg
      push Not at hneg
      have hcob := tendsto_cobounded_of_meromorphicOrderAt_neg hneg
      rw [← tendsto_norm_atTop_iff_cobounded] at hcob
      set e := E⁄ℂ
      -- bounds for the coefficients of the equation in `Y`
      have hA : Tendsto (fun z => e.a₁ * X (ofComplex z) + e.a₃) (𝓝[≠] (τ : ℂ))
          (𝓝 (e.a₁ * x₀ + e.a₃)) := (hx₀.const_mul _).add_const _
      have hB : Tendsto (fun z => X (ofComplex z) ^ 3 + e.a₂ * X (ofComplex z) ^ 2 +
          e.a₄ * X (ofComplex z) + e.a₆) (𝓝[≠] (τ : ℂ))
          (𝓝 (x₀ ^ 3 + e.a₂ * x₀ ^ 2 + e.a₄ * x₀ + e.a₆)) := by
        have := hx₀
        exact ((((this.pow 3).add ((this.pow 2).const_mul _)).add (this.const_mul _)).add_const _)
      set M := ‖e.a₁ * x₀ + e.a₃‖ + 1
      set M' := ‖x₀ ^ 3 + e.a₂ * x₀ ^ 2 + e.a₄ * x₀ + e.a₆‖ + 1
      have hA' := hA.norm.eventually (gt_mem_nhds (lt_add_one ‖e.a₁ * x₀ + e.a₃‖))
      have hB' := hB.norm.eventually
        (gt_mem_nhds (lt_add_one ‖x₀ ^ 3 + e.a₂ * x₀ ^ 2 + e.a₄ * x₀ + e.a₆‖))
      have hbig := hcob.eventually (eventually_gt_atTop (M + M' + 1))
      obtain ⟨z, hz1, hz2, hz3, hz4⟩ := (heq.and (hA'.and (hB'.and hbig))).exists
      simp only [Function.comp_apply] at hz2 hz3 hz4
      rw [WeierstrassCurve.Affine.equation_iff] at hz1
      set y := Y (ofComplex z)
      set x := X (ofComplex z)
      have hy2 : y ^ 2 = (x ^ 3 + e.a₂ * x ^ 2 + e.a₄ * x + e.a₆) - (e.a₁ * x + e.a₃) * y := by
        linear_combination hz1
      have hn : ‖y‖ ^ 2 ≤ M * ‖y‖ + M' := by
        rw [← norm_pow, hy2]
        calc ‖(x ^ 3 + e.a₂ * x ^ 2 + e.a₄ * x + e.a₆) - (e.a₁ * x + e.a₃) * y‖
            ≤ ‖x ^ 3 + e.a₂ * x ^ 2 + e.a₄ * x + e.a₆‖ + ‖(e.a₁ * x + e.a₃) * y‖ := norm_sub_le _ _
          _ ≤ M' + M * ‖y‖ := by
            rw [norm_mul]
            gcongr
          _ = M * ‖y‖ + M' := by ring
      have hM : 0 ≤ M := by positivity
      have hM' : 0 ≤ M' := by positivity
      nlinarith
    obtain ⟨y₀, hy₀⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hY hoY
    -- the limit point is on `E`
    have hEq : (E⁄ℂ).Equation x₀ y₀ := by
      rw [WeierstrassCurve.Affine.equation_iff']
      have hlim : Tendsto (fun z => Y (ofComplex z) ^ 2 + (E⁄ℂ).a₁ * X (ofComplex z) *
          Y (ofComplex z) + (E⁄ℂ).a₃ * Y (ofComplex z) - (X (ofComplex z) ^ 3 +
          (E⁄ℂ).a₂ * X (ofComplex z) ^ 2 + (E⁄ℂ).a₄ * X (ofComplex z) + (E⁄ℂ).a₆))
          (𝓝[≠] (τ : ℂ)) (𝓝 (y₀ ^ 2 + (E⁄ℂ).a₁ * x₀ * y₀ + (E⁄ℂ).a₃ * y₀ -
            (x₀ ^ 3 + (E⁄ℂ).a₂ * x₀ ^ 2 + (E⁄ℂ).a₄ * x₀ + (E⁄ℂ).a₆))) := by
        have hx := hx₀
        have hy := hy₀
        exact ((((hy.pow 2).add ((hx.const_mul _).mul hy)).add (hy.const_mul _)).sub
          ((((hx.pow 3).add ((hx.pow 2).const_mul _)).add (hx.const_mul _)).add_const _))
      have h0 : Tendsto (fun z => Y (ofComplex z) ^ 2 + (E⁄ℂ).a₁ * X (ofComplex z) *
          Y (ofComplex z) + (E⁄ℂ).a₃ * Y (ofComplex z) - (X (ofComplex z) ^ 3 +
          (E⁄ℂ).a₂ * X (ofComplex z) ^ 2 + (E⁄ℂ).a₄ * X (ofComplex z) + (E⁄ℂ).a₆))
          (𝓝[≠] (τ : ℂ)) (𝓝 0) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [heq] with z hz
        exact ((WeierstrassCurve.Affine.equation_iff' _ _).1 hz).symm
      exact tendsto_nhds_unique hlim h0
    have hNS : (E⁄ℂ).Nonsingular x₀ y₀ :=
      (WeierstrassCurve.Affine.equation_iff_nonsingular).1 hEq
    refine Or.inl ⟨x₀, y₀, hNS, hx₀, hy₀, ?_⟩
    unfold ZInQ.GZModuli.modPt
    have hex : ∃ p : ℂ × ℂ, (E⁄ℂ).Nonsingular p.1 p.2 ∧
        Tendsto (X ∘ ofComplex) (𝓝[≠] (τ : ℂ)) (𝓝 p.1) ∧
        Tendsto (Y ∘ ofComplex) (𝓝[≠] (τ : ℂ)) (𝓝 p.2) := ⟨(x₀, y₀), hNS, hx₀, hy₀⟩
    split_ifs
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨tendsto_nhds_unique hex.choose_spec.2.1 hx₀, tendsto_nhds_unique hex.choose_spec.2.2 hy₀⟩


/-! ## The leaf's `φ`: the equation on `ℍ` and the value at every `τ` -/

/-- The generic point `(x, y)` of `E` satisfies the equation of `E` in `ℚ(E)`. -/
theorem wEqR_gen (E : WeierstrassCurve ℚ) : WEqR E (genX E) (genY E) := by
  set CR := E.toAffine.CoordinateRing
  have hmk : ∀ a : ℚ, WeierstrassCurve.Affine.CoordinateRing.mk E.toAffine
      (Polynomial.C (Polynomial.C a)) = algebraMap ℚ CR a := by
    intro a
    rw [IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) CR]
    rfl
  have h0 : WeierstrassCurve.Affine.CoordinateRing.mk E.toAffine E.toAffine.polynomial = 0 :=
    AdjoinRoot.mk_self
  simp only [WeierstrassCurve.Affine.polynomial, map_sub, map_add, map_mul, map_pow, hmk] at h0
  have h1 := congrArg (algebraMap CR E.toAffine.FunctionField) h0
  have hc : ∀ a : ℚ, algebraMap CR E.toAffine.FunctionField (algebraMap ℚ CR a) =
      (a : E.toAffine.FunctionField) := fun a =>
    eq_ratCast ((algebraMap CR E.toAffine.FunctionField).comp (algebraMap ℚ CR)) a
  simp only [map_sub, map_add, map_mul, map_pow, map_zero, hc] at h1
  unfold WEqR genX genY
  linear_combination h1

/-- `φ^*(x), φ^*(y)` satisfy the equation of `E` in `ℚ((q))`. -/
theorem wEqR_phi {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N]
    (φ : E.toAffine.FunctionField →ₐ[ℚ] X0Field N) :
    WEqR E ((φ (genX E) : X0Field N) : LaurentSeries ℚ)
      ((φ (genY E) : X0Field N) : LaurentSeries ℚ) :=
  ((wEqR_gen E).map (φ : E.toAffine.FunctionField →+* X0Field N)).map
    ((X0Field N).val : X0Field N →+* LaurentSeries ℚ)


/-- **The rational map `(Px/Qx, Py/Qy)` satisfies the equation of `E` on a punctured neighbourhood of
every `τ ∈ ℍ`.** -/
theorem eventually_equation_ratFn {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N]
    (φ : E.toAffine.FunctionField →ₐ[ℚ] X0Field N) {Px Qx Py Qy : MvPolynomial (Fin 2) ℚ}
    (hrx : IsRatRep N (φ (genX E) : LaurentSeries ℚ) Px Qx)
    (hry : IsRatRep N (φ (genY E) : LaurentSeries ℚ) Py Qy) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ),
      (E⁄ℂ).Equation (ratFn N Px Qx (ofComplex z)) (ratFn N Py Qy (ofComplex z)) := by
  obtain ⟨hQx, hx⟩ := hrx
  obtain ⟨hQy, hy⟩ := hry
  have hW := wEqR_phi φ
  rw [hx, hy] at hW
  open MvPolynomial in
  set Wt : MvPolynomial (Fin 2) ℚ :=
    (Py ^ 2 * Qx ^ 3 + C E.a₁ * Px * Py * Qx ^ 2 * Qy + C E.a₃ * Py * Qx ^ 3 * Qy) -
    (Px ^ 3 * Qy ^ 2 + C E.a₂ * Px ^ 2 * Qx * Qy ^ 2 + C E.a₄ * Px * Qx ^ 2 * Qy ^ 2 +
      C E.a₆ * Qx ^ 3 * Qy ^ 2) with hWt
  have hWQ : polyQ N Wt = 0 := by
    have e : polyQ N Wt = polyQ N Qx ^ 3 * polyQ N Qy ^ 2 *
        (((polyQ N Py / polyQ N Qy) ^ 2 + (E.a₁ : LaurentSeries ℚ) * (polyQ N Px / polyQ N Qx) *
          (polyQ N Py / polyQ N Qy) + (E.a₃ : LaurentSeries ℚ) * (polyQ N Py / polyQ N Qy)) -
         ((polyQ N Px / polyQ N Qx) ^ 3 + (E.a₂ : LaurentSeries ℚ) * (polyQ N Px / polyQ N Qx) ^ 2 +
          (E.a₄ : LaurentSeries ℚ) * (polyQ N Px / polyQ N Qx) + (E.a₆ : LaurentSeries ℚ))) := by
      have hQx' : MvPolynomial.aeval (ptQ N) Qx ≠ 0 := hQx
      have hQy' : MvPolynomial.aeval (ptQ N) Qy ≠ 0 := hQy
      simp only [hWt, polyQ, map_sub, map_add, map_mul, map_pow, MvPolynomial.aeval_C, eq_ratCast]
      field_simp
    rw [e, sub_eq_zero.2 hW, mul_zero]
  have hq := hasQExp_polyFn N Wt
  rw [hWQ] at hq
  obtain ⟨T, hT⟩ := HasQExp.eq_zero hq
  have hz := eventuallyEq_zero_of_im_gt (fun τ => (holoH_polyFn N Wt τ).meromorphicAt) hT τ
  obtain ⟨Tx, hTx⟩ := HasQExp.exists_ne_zero (hasQExp_polyFn N Qx) hQx
  obtain ⟨Ty, hTy⟩ := HasQExp.exists_ne_zero (hasQExp_polyFn N Qy) hQy
  have hnx := eventually_ne_zero_of_im_gt (fun τ => (holoH_polyFn N Qx τ).meromorphicAt) hTx τ
  have hny := eventually_ne_zero_of_im_gt (fun τ => (holoH_polyFn N Qy τ).meromorphicAt) hTy τ
  filter_upwards [hz, hnx, hny] with z h0 h1 h2
  simp only [Function.comp_apply, Pi.zero_apply, hWt, polyFn, map_sub, map_add, map_mul, map_pow,
    MvPolynomial.aeval_C, eq_ratCast] at h0
  simp only [polyFn] at h1 h2
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [ratFn, polyFn, WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, eq_ratCast]
  field_simp
  linear_combination h0

/-- **The value of the leaf's `φ` at every `τ ∈ ℍ` is the center of `ord_τ`** (no junk values):
`modPt_cases` for `(ratFn Px Qx, ratFn Py Qy)`. -/
theorem modPt_plane_cases (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ} [NeZero N]
    (φ : E.toAffine.FunctionField →ₐ[ℚ] X0Field N) {Px Qx Py Qy : MvPolynomial (Fin 2) ℚ}
    (hrx : IsRatRep N (φ (genX E) : LaurentSeries ℚ) Px Qx)
    (hry : IsRatRep N (φ (genY E) : LaurentSeries ℚ) Py Qy) (τ : ℍ) :
    (∃ (x₀ y₀ : ℂ) (h : (E⁄ℂ).Nonsingular x₀ y₀),
        Tendsto (ratFn N Px Qx ∘ ofComplex) (𝓝[≠] (τ : ℂ)) (𝓝 x₀) ∧
        Tendsto (ratFn N Py Qy ∘ ofComplex) (𝓝[≠] (τ : ℂ)) (𝓝 y₀) ∧
        ZInQ.GZModuli.modPt E (ratFn N Px Qx) (ratFn N Py Qy) τ = .some x₀ y₀ h) ∨
    (Tendsto (fun z => ‖ratFn N Px Qx (ofComplex z)‖) (𝓝[≠] (τ : ℂ)) atTop ∧
        ZInQ.GZModuli.modPt E (ratFn N Px Qx) (ratFn N Py Qy) τ = 0) :=
  modPt_cases E (meromorphic_ratFn N Px Qx τ) (meromorphic_ratFn N Py Qy τ)
    (eventually_equation_ratFn φ hrx hry τ)

/-- **The leaf's `φ` has a center at every place of `ℚ(X₀(N))`** (every valuation subring `O ⊇ ℚ`). -/
theorem phi_center {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N]
    (φ : E.toAffine.FunctionField →ₐ[ℚ] X0Field N) (O : ValuationSubring (X0Field N))
    (hO : ∀ c : ℚ, (c : X0Field N) ∈ O) :
    (φ (genX E) ∈ O ∧ φ (genY E) ∈ O) ∨
      (φ (genX E) ∉ O ∧ φ (genY E) ≠ 0 ∧ O.valuation (φ (genY E))⁻¹ < 1 ∧
        O.valuation (φ (genX E) * (φ (genY E))⁻¹) < 1) :=
  center_of_wEq_subring E O hO ((wEqR_gen E).map (φ : E.toAffine.FunctionField →+* X0Field N))

end ZInQ.GZDict2
