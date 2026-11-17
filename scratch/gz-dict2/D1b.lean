import ZInQKernel.Contrib.OneProof.GrossZagierPlane

noncomputable section

open UpperHalfPlane Filter Topology
open scoped WeierstrassCurve.Affine

namespace ZInQ.GZDict2

open ZInQ.GZAlg

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
    rw [dif_neg]
    rintro ⟨p, -, hp, -⟩
    exact not_tendsto_atTop_of_tendsto_nhds hp.norm hcob
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
    rw [dif_pos hex]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨tendsto_nhds_unique hex.choose_spec.2.1 hx₀, tendsto_nhds_unique hex.choose_spec.2.2 hy₀⟩


/-! ## The leaf's `φ`: the equation on `ℍ` and the value at every `τ` -/

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

end ZInQ.GZDict2
