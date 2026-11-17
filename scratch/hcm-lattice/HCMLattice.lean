import ZInQKernel.Contrib.OneProof.ShimuraMainCM

noncomputable section

open Complex Topology Filter
open scoped PeriodPair

namespace ZInQ.Contrib.HCMLattice

open WeierstrassCurve.Affine (Point)

/-! ## §A. Analytic isomorphisms `ℂ/Λ → E(ℂ) ⊂ ℙ²(ℂ)` -/

/-- `[X : Y : Z]` are homogeneous coordinates of the point `P ∈ E(ℂ) ⊂ ℙ²(ℂ)` (`E(ℂ) = W.toAffine.Point`:
the affine point `(x, y)` is `[x : y : 1]` and `O` is `[0 : 1 : 0]`). -/
def IsProjCoord (W : WeierstrassCurve ℂ) (P : W.toAffine.Point) (X Y Z : ℂ) : Prop :=
  (Z ≠ 0 ∧ ∃ h : W.toAffine.Nonsingular (X / Z) (Y / Z), P = .some _ _ h) ∨
    (X = 0 ∧ Y ≠ 0 ∧ Z = 0 ∧ P = 0)

/-- `(X, Y, Z) : U → ℂ³ ∖ 0` is a holomorphic lift of `ξ : ℂ → E(ℂ) ⊂ ℙ²(ℂ)` on the open set `U`. -/
def IsHoloLift (W : WeierstrassCurve ℂ) (ξ : ℂ → W.toAffine.Point) (U : Set ℂ) (X Y Z : ℂ → ℂ) : Prop :=
  IsOpen U ∧ DifferentiableOn ℂ X U ∧ DifferentiableOn ℂ Y U ∧ DifferentiableOn ℂ Z U ∧
    ∀ z ∈ U, IsProjCoord W (ξ z) (X z) (Y z) (Z z)

/-- `ξ : ℂ → E(ℂ) ⊂ ℙ²(ℂ)` is holomorphic: near every point it lifts holomorphically to `ℂ³ ∖ 0`
(the complex structure of `ℙ²(ℂ)`, restricted to the closed curve `E(ℂ)`). -/
def IsHolomorphicMap (W : WeierstrassCurve ℂ) (ξ : ℂ → W.toAffine.Point) : Prop :=
  ∀ z₀ : ℂ, ∃ (U : Set ℂ) (X Y Z : ℂ → ℂ), z₀ ∈ U ∧ IsHoloLift W ξ U X Y Z

/-- `F ∧ F'` for a lift `F = (X, Y, Z)`: it vanishes at `z` iff the differential of `[X : Y : Z]` vanishes at `z`. -/
def wedge (X Y Z : ℂ → ℂ) (z : ℂ) : Fin 3 → ℂ :=
  ![Y z * deriv Z z - Z z * deriv Y z, Z z * deriv X z - X z * deriv Z z,
    X z * deriv Y z - Y z * deriv X z]

/-- `ξ` has nowhere vanishing differential (as a map into `ℙ²(ℂ)`). -/
def IsImmersion (W : WeierstrassCurve ℂ) (ξ : ℂ → W.toAffine.Point) : Prop :=
  ∀ z₀ : ℂ, ∃ (U : Set ℂ) (X Y Z : ℂ → ℂ), z₀ ∈ U ∧ IsHoloLift W ξ U X Y Z ∧ wedge X Y Z z₀ ≠ 0

/-- `ξ : ℂ → E(ℂ)` induces a bijection `ℂ/Λ → E(ℂ)`. -/
def InducesBij (W : WeierstrassCurve ℂ) (Λ : Set ℂ) (ξ : ℂ → W.toAffine.Point) : Prop :=
  (∀ z, ∀ l ∈ Λ, ξ (z + l) = ξ z) ∧ (∀ z w, ξ z = ξ w → z - w ∈ Λ) ∧ Function.Surjective ξ

/-- **Analytic isomorphism `ℂ/Λ → E(ℂ)`**, read on `ℂ`: `ξ` induces a bijection `ℂ/Λ → E(ℂ)`, is holomorphic
into `E(ℂ) ⊂ ℙ²(ℂ)` and has nowhere vanishing differential; i.e. a biholomorphism of the Riemann surfaces
`ℂ/Λ` and `E(ℂ)` (a bijective holomorphic map with nonvanishing differential has a holomorphic inverse). -/
def IsAnalyticIso (W : WeierstrassCurve ℂ) (Λ : Set ℂ) (ξ : ℂ → W.toAffine.Point) : Prop :=
  InducesBij W Λ ξ ∧ IsHolomorphicMap W ξ ∧ IsImmersion W ξ

theorem isProjCoord_some {W : WeierstrassCurve ℂ} {x y X Y Z : ℂ} (h : W.toAffine.Nonsingular x y)
    (hZ : Z ≠ 0) (hX : X / Z = x) (hY : Y / Z = y) : IsProjCoord W (.some x y h) X Y Z := by
  subst hX hY; exact Or.inl ⟨hZ, h, rfl⟩

theorem isProjCoord_zero {W : WeierstrassCurve ℂ} {Y : ℂ} (hY : Y ≠ 0) : IsProjCoord W 0 0 Y 0 :=
  Or.inr ⟨rfl, hY, rfl, rfl⟩

/-! ## §B. The Weierstrass map is an analytic isomorphism -/

section Weierstrass

variable (L : PeriodPair)

theorem toPoint_sub (z w : ℂ) :
    L.toPoint L.discriminant_ne_zero (z - w) =
      L.toPoint L.discriminant_ne_zero z - L.toPoint L.discriminant_ne_zero w := by
  have hU := L.isUniformization_toPoint L.discriminant_ne_zero
  let f : ℂ →+ L.weierstrassCurve.toAffine.Point := AddMonoidHom.mk' (L.toPoint _) hU.1
  exact map_sub f z w

theorem toPoint_inducesBij : InducesBij L.weierstrassCurve L.lattice (L.toPoint L.discriminant_ne_zero) := by
  have hU := L.isUniformization_toPoint L.discriminant_ne_zero
  refine ⟨fun z l hl => ?_, fun z w h => hU.2.2 _ ?_, hU.2.1⟩
  · rw [hU.1, L.toPoint_of_mem _ hl, add_zero]
  · rw [toPoint_sub, h, sub_self]

/-- `℘'(z₀) = 0` forces `℘''(z₀) ≠ 0` (the roots of `4x³ − g₂x − g₃` are simple). -/
theorem deriv_derivWeierstrassP_ne {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice) (h0 : ℘'[L] z₀ = 0) :
    deriv ℘'[L] z₀ ≠ 0 := by
  have hopen : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have hP'a : AnalyticAt ℂ ℘'[L] z₀ := L.analyticOnNhd_derivWeierstrassP z₀ hz₀
  rcases hP'a.eventually_eq_zero_or_eventually_ne_zero with hz | hnz
  · -- `℘' ≡ 0` near `z₀`: `℘` is constant near `z₀`, so the Weierstrass map is not injective mod `L`
    exfalso
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hz.and (hopen.mem_nhds hz₀))
    have hconst : ∀ z ∈ Metric.ball z₀ r, ℘[L] z = ℘[L] z₀ := by
      intro z hz
      refine IsOpen.is_const_of_deriv_eq_zero (f := ℘[L]) Metric.isOpen_ball
        (convex_ball z₀ r).isPreconnected
        (fun w hw => ((L.analyticOnNhd_weierstrassP w (hball w hw).2).differentiableAt).differentiableWithinAt)
        (fun w hw => by rw [PeriodPair.deriv_weierstrassP]; exact (hball w hw).1) hz
        (Metric.mem_ball_self hr)
    obtain ⟨ε, hε, hsmall⟩ := ZInQ.Contrib.HCMDict.exists_lattice_small L
    set t : ℂ := ((min r ε / 2 : ℝ) : ℂ)
    have ht0 : t ≠ 0 := by
      simp only [t, ne_eq, Complex.ofReal_eq_zero]; positivity
    have htn : ‖t‖ = min r ε / 2 := by
      simp only [t, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_pos (by positivity)
    have htr : z₀ + t ∈ Metric.ball z₀ r := by
      simp only [Metric.mem_ball, dist_self_add_left, htn]
      linarith [min_le_left r ε]
    have hpt : L.toPoint L.discriminant_ne_zero (z₀ + t) = L.toPoint L.discriminant_ne_zero z₀ := by
      rw [L.toPoint_of_notMem _ (hball _ htr).2, L.toPoint_of_notMem _ hz₀, Point.some.injEq]
      exact ⟨hconst _ htr, by rw [(hball _ htr).1, h0]⟩
    have hl := (toPoint_inducesBij L).2.1 _ _ hpt
    rw [add_sub_cancel_left] at hl
    exact ht0 (hsmall t hl (by rw [htn]; linarith [min_le_right r ε]))
  · intro hd
    -- `h = 2℘'' − 12℘² + g₂` vanishes off the zeros of `℘'`, hence at `z₀`
    set h : ℂ → ℂ := fun z => 2 * deriv ℘'[L] z - 12 * ℘[L] z ^ 2 + L.g₂
    have hha : ContinuousAt h z₀ :=
      (((hP'a.deriv.continuousAt.const_mul 2).sub
        (((L.analyticOnNhd_weierstrassP z₀ hz₀).continuousAt.pow 2).const_mul 12)).add
        continuousAt_const)
    have hev : ∀ᶠ z in 𝓝[≠] z₀, h z = 0 := by
      have hn : ∀ᶠ z in 𝓝[≠] z₀, z ∈ (L.lattice : Set ℂ)ᶜ :=
        nhdsWithin_le_nhds (hopen.mem_nhds hz₀)
      filter_upwards [hnz, hn] with z hzne hzL
      have hzo : (L.lattice : Set ℂ)ᶜ ∈ 𝓝 z := hopen.mem_nhds hzL
      have heq : (fun w => ℘'[L] w ^ 2) =ᶠ[𝓝 z] fun w => 4 * ℘[L] w ^ 3 - L.g₂ * ℘[L] w - L.g₃ :=
        Filter.eventually_of_mem hzo fun w hw => L.derivWeierstrassP_sq w hw
      have hPd : DifferentiableAt ℂ ℘[L] z := (L.analyticOnNhd_weierstrassP z hzL).differentiableAt
      have hP'd : DifferentiableAt ℂ ℘'[L] z := (L.analyticOnNhd_derivWeierstrassP z hzL).differentiableAt
      have d1 : HasDerivAt (fun w => ℘'[L] w ^ 2) (2 * ℘'[L] z * deriv ℘'[L] z) z := by
        have := (hasDerivAt_pow 2 (℘'[L] z)).comp z hP'd.hasDerivAt
        convert this using 1
        · rfl
        · push_cast; ring
      have d2 : HasDerivAt (fun w => 4 * ℘[L] w ^ 3 - L.g₂ * ℘[L] w - L.g₃)
          (4 * (3 * ℘[L] z ^ 2 * ℘'[L] z) - L.g₂ * ℘'[L] z) z := by
        have hp : HasDerivAt ℘[L] (℘'[L] z) z := by
          rw [← PeriodPair.deriv_weierstrassP]; exact hPd.hasDerivAt
        have := (((hp.pow 3).const_mul 4).sub (hp.const_mul L.g₂)).sub_const L.g₃
        simpa using this
      have hu := (d1.congr_of_eventuallyEq heq.symm).unique d2
      have : ℘'[L] z * h z = 0 := by simp only [h]; linear_combination hu
      exact (mul_eq_zero.1 this).resolve_left hzne
    have hz0 : h z₀ = 0 := by
      have t1 : Tendsto h (𝓝[≠] z₀) (𝓝 (h z₀)) := hha.tendsto.mono_left nhdsWithin_le_nhds
      have t2 : Tendsto h (𝓝[≠] z₀) (𝓝 0) := tendsto_const_nhds.congr' (hev.mono fun z hz => hz.symm)
      exact tendsto_nhds_unique t1 t2
    simp only [h, hd, mul_zero, zero_sub] at hz0
    have hsq := L.derivWeierstrassP_sq z₀ hz₀
    rw [h0] at hsq
    apply L.discriminant_ne_zero
    have hg₂ : L.g₂ = 12 * ℘[L] z₀ ^ 2 := by linear_combination hz0
    have hg₃ : L.g₃ = -8 * ℘[L] z₀ ^ 3 := by
      linear_combination hsq - ℘[L] z₀ * hg₂
    show L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 0
    rw [hg₂, hg₃]; ring

theorem IsImmersion.isHolomorphicMap {W : WeierstrassCurve ℂ} {ξ : ℂ → W.toAffine.Point}
    (h : IsImmersion W ξ) : IsHolomorphicMap W ξ := fun z₀ => by
  obtain ⟨U, X, Y, Z, hz, hL, -⟩ := h z₀
  exact ⟨U, X, Y, Z, hz, hL⟩

/-- **The Weierstrass map `z ↦ [℘(z) : ℘'(z)/2 : 1]` has nowhere vanishing differential** into `ℙ²(ℂ)`:
off `L` because `℘'` and `℘''` have no common zero, at `l₀ ∈ L` through the lift
`[w + w³h : (−2 + w³k)/2 : w³]` (`w = z − l₀`, `℘ = w⁻² + h`, `℘' = −2w⁻³ + k`), whose third wedge component is `1`. -/
theorem toPoint_isImmersion : IsImmersion L.weierstrassCurve (L.toPoint L.discriminant_ne_zero) := by
  intro z₀
  by_cases hz₀ : z₀ ∈ L.lattice
  · set l₀ : L.lattice := ⟨z₀, hz₀⟩
    set U : Set ℂ := ((L.lattice : Set ℂ) \ {z₀})ᶜ with hU
    have hUo : IsOpen U := L.isOpen_compl_lattice_sdiff
    have hz₀U : z₀ ∈ U := by simp [hU]
    set h : ℂ → ℂ := fun z => ℘[L - z₀] z - 1 / z₀ ^ 2
    set k : ℂ → ℂ := ℘'[L - z₀]
    have hhd : DifferentiableOn ℂ h U := (L.differentiableOn_weierstrassPExcept z₀).sub_const _
    have hkd : DifferentiableOn ℂ k U := L.differentiableOn_derivWeierstrassPExcept z₀
    have hwd : Differentiable ℂ fun z : ℂ => z - z₀ := differentiable_id.sub_const _
    set X : ℂ → ℂ := fun z => (z - z₀) + (z - z₀) ^ 3 * h z
    set Y : ℂ → ℂ := fun z => (-2 + (z - z₀) ^ 3 * k z) / 2
    set Z : ℂ → ℂ := fun z => (z - z₀) ^ 3
    have hXd : DifferentiableOn ℂ X U :=
      hwd.differentiableOn.add ((hwd.pow 3).differentiableOn.mul hhd)
    have hYd : DifferentiableOn ℂ Y U :=
      ((differentiableOn_const _).add ((hwd.pow 3).differentiableOn.mul hkd)).div_const 2
    have hZd : DifferentiableOn ℂ Z U := (hwd.pow 3).differentiableOn
    refine ⟨U, X, Y, Z, hz₀U, ⟨hUo, hXd, hYd, hZd, fun z hz => ?_⟩, ?_⟩
    · by_cases hzz : z = z₀
      · subst hzz
        rw [L.toPoint_of_mem _ hz₀]
        have hX : X z = 0 := by simp [X]
        have hY : Y z = -1 := by norm_num [Y]
        have hZ : Z z = 0 := by simp [Z]
        rw [hX, hY, hZ]
        exact isProjCoord_zero (by norm_num)
      · have hzL : z ∉ L.lattice := fun hl => hz ⟨hl, hzz⟩
        have hw : z - z₀ ≠ 0 := sub_ne_zero.2 hzz
        rw [L.toPoint_of_notMem _ hzL]
        refine isProjCoord_some _ (pow_ne_zero 3 hw) ?_ ?_
        · have e := L.weierstrassPExcept_add l₀ z
          simp only [l₀] at e
          simp only [X, Z, h]
          rw [← e]
          field_simp
          ring
        · have e := L.derivWeierstrassPExcept_sub l₀ z
          simp only [l₀] at e
          simp only [Y, Z, k]
          rw [← e]
          field_simp
          ring
    · intro hw
      have h3 := congrFun hw 2
      have hU' : U ∈ 𝓝 z₀ := hUo.mem_nhds hz₀U
      have dX : HasDerivAt X 1 z₀ := by
        have h1 : HasDerivAt (fun z : ℂ => z - z₀) 1 z₀ := (hasDerivAt_id z₀).sub_const z₀
        have h2 : HasDerivAt (fun z : ℂ => (z - z₀) ^ 3) (3 * (z₀ - z₀) ^ 2 * 1) z₀ := by
          have hp := hasDerivAt_pow 3 ((fun z : ℂ => z - z₀) z₀)
          have := HasDerivAt.comp (h := fun z : ℂ => z - z₀) z₀ hp h1
          convert this using 1
          rfl
        have h4 := (h2.mul (hhd.differentiableAt hU').hasDerivAt)
        have := h1.add h4
        convert this using 1; simp
      have hXz : X z₀ = 0 := by simp [X]
      have hYz : Y z₀ = -1 := by norm_num [Y]
      simp only [wedge, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.zero_apply,
        hXz, hYz, dX.deriv] at h3
      norm_num at h3
  · refine ⟨(L.lattice : Set ℂ)ᶜ, ℘[L], fun z => ℘'[L] z / 2, fun _ => 1, hz₀,
      ⟨L.isClosed_lattice.isOpen_compl, L.analyticOnNhd_weierstrassP.differentiableOn,
        (L.analyticOnNhd_derivWeierstrassP.differentiableOn).div_const 2, differentiableOn_const 1,
        fun z hz => ?_⟩, ?_⟩
    · rw [L.toPoint_of_notMem _ hz]
      exact isProjCoord_some _ one_ne_zero (div_one _) (div_one _)
    · intro hw
      have h1 := congrFun hw 0
      have h2 := congrFun hw 1
      simp only [wedge, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply,
        deriv_const, PeriodPair.deriv_weierstrassP, deriv_div_const, mul_zero, one_mul, zero_sub,
        sub_zero, neg_eq_zero, div_eq_zero_iff, two_ne_zero, or_false] at h1 h2
      exact deriv_derivWeierstrassP_ne L hz₀ h2 h1

/-- **The Weierstrass map is an analytic isomorphism `ℂ/L → E_L(ℂ)`.** -/
theorem toPoint_isAnalyticIso :
    IsAnalyticIso L.weierstrassCurve L.lattice (L.toPoint L.discriminant_ne_zero) :=
  ⟨toPoint_inducesBij L, (toPoint_isImmersion L).isHolomorphicMap, toPoint_isImmersion L⟩

end Weierstrass

/-! ## §C. A holomorphic bijection `ℂ/Λ → E_{L₀}(ℂ)` with `0 ↦ O` is `z ↦ ξ_{L₀}(αz)` -/

section Liouville

/-- The affine `x`-coordinate of a point (junk value `0` at `O`). -/
def xP {W : WeierstrassCurve ℂ} : W.toAffine.Point → ℂ
  | .zero => 0
  | .some x _ _ => x

/-- The affine `y`-coordinate of a point (junk value `0` at `O`). -/
def yP {W : WeierstrassCurve ℂ} : W.toAffine.Point → ℂ
  | .zero => 0
  | .some _ y _ => y

theorem eq_some_of_ne_zero {W : WeierstrassCurve ℂ} {P : W.toAffine.Point} (hP : P ≠ 0) :
    ∃ h : W.toAffine.Nonsingular (xP P) (yP P), P = .some _ _ h := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact ⟨h, rfl⟩

theorem IsProjCoord.ne_zero_iff {W : WeierstrassCurve ℂ} {P : W.toAffine.Point} {X Y Z : ℂ}
    (h : IsProjCoord W P X Y Z) : P ≠ 0 ↔ Z ≠ 0 := by
  rcases h with ⟨hZ, hns, rfl⟩ | ⟨-, -, hZ, rfl⟩
  · exact ⟨fun _ => hZ, fun _ => Point.some_ne_zero hns⟩
  · simp [hZ]

theorem IsProjCoord.coords {W : WeierstrassCurve ℂ} {P : W.toAffine.Point} {X Y Z : ℂ}
    (h : IsProjCoord W P X Y Z) (hP : P ≠ 0) : xP P = X / Z ∧ yP P = Y / Z := by
  rcases h with ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd rfl hP

theorem IsProjCoord.of_zero {W : WeierstrassCurve ℂ} {X Y Z : ℂ} (h : IsProjCoord W 0 X Y Z) :
    X = 0 ∧ Y ≠ 0 ∧ Z = 0 := by
  rcases h with ⟨-, hns, he⟩ | ⟨hX, hY, hZ, -⟩
  · exact absurd he.symm (Point.some_ne_zero hns)
  · exact ⟨hX, hY, hZ⟩

/-- Homogeneous coordinates satisfy the homogeneous short Weierstrass equation. -/
theorem IsProjCoord.homog {W : WeierstrassCurve ℂ} {P : W.toAffine.Point} {X Y Z : ℂ}
    (h : IsProjCoord W P X Y Z) (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) :
    Y ^ 2 * Z = X ^ 3 + W.a₄ * X * Z ^ 2 + W.a₆ * Z ^ 3 := by
  rcases h with ⟨hZ, hns, -⟩ | ⟨hX, -, hZ, -⟩
  · have e := (WeierstrassCurve.Affine.equation_iff _ _).1 hns.1
    rw [h₁, h₂, h₃] at e
    have key : Y ^ 2 * Z - (X ^ 3 + W.a₄ * X * Z ^ 2 + W.a₆ * Z ^ 3) =
        Z ^ 3 * ((Y / Z) ^ 2 + 0 * (X / Z) * (Y / Z) + 0 * (Y / Z) -
          ((X / Z) ^ 3 + 0 * (X / Z) ^ 2 + W.a₄ * (X / Z) + W.a₆)) := by
      field_simp; ring
    rw [e, sub_self, mul_zero] at key
    linear_combination key
  · rw [hX, hZ]; ring

/-- Two homogeneous coordinate vectors of the same point are proportional. -/
theorem IsProjCoord.cross_eq_zero {W : WeierstrassCurve ℂ} {P : W.toAffine.Point} {X Y Z X' Y' Z' : ℂ}
    (h : IsProjCoord W P X Y Z) (h' : IsProjCoord W P X' Y' Z') :
    Y * Z' - Z * Y' = 0 ∧ Z * X' - X * Z' = 0 ∧ X * Y' - Y * X' = 0 := by
  rcases h with ⟨hZ, hns, rfl⟩ | ⟨hX, -, hZ, rfl⟩ <;>
    rcases h' with ⟨hZ', hns', he⟩ | ⟨hX', -, hZ', he⟩
  · simp only [Point.some.injEq] at he
    obtain ⟨ex, ey⟩ := he
    field_simp at ex ey
    refine ⟨by linear_combination ey, by linear_combination -ex, ?_⟩
    have : X * Y' * Z' * Z = Y * X' * Z' * Z := by linear_combination Y' * Z * ex - X' * Z * ey
    have hZZ : Z' * Z ≠ 0 := mul_ne_zero hZ' hZ
    have h2 : (X * Y' - Y * X') * (Z' * Z) = 0 := by linear_combination this
    exact (mul_eq_zero.1 h2).resolve_right hZZ
  · exact absurd he (Point.some_ne_zero hns)
  · exact absurd he.symm (Point.some_ne_zero hns')
  · rw [hX, hZ, hX', hZ']; simp

/-- Proportional homogeneous coordinate vectors give the same point. -/
theorem IsProjCoord.eq_of_cross {W : WeierstrassCurve ℂ} {P Q : W.toAffine.Point} {X Y Z X' Y' Z' : ℂ}
    (h : IsProjCoord W P X Y Z) (h' : IsProjCoord W Q X' Y' Z')
    (c₀ : Y * Z' - Z * Y' = 0) (c₁ : Z * X' - X * Z' = 0) : P = Q := by
  rcases h with ⟨hZ, hns, rfl⟩ | ⟨hX, hY, hZ, rfl⟩ <;>
    rcases h' with ⟨hZ', hns', rfl⟩ | ⟨hX', hY', hZ', rfl⟩
  · have ex : X / Z = X' / Z' := by field_simp; linear_combination -c₁
    have ey : Y / Z = Y' / Z' := by field_simp; linear_combination c₀
    simp only [Point.some.injEq]; exact ⟨ex, ey⟩
  · rw [hZ'] at c₀; simp only [mul_zero, zero_sub, neg_eq_zero, mul_eq_zero] at c₀
    exact absurd (c₀.resolve_left hZ) hY'
  · rw [hZ] at c₀; simp only [zero_mul, sub_zero, mul_eq_zero] at c₀
    exact absurd (c₀.resolve_left hY) hZ'
  · rfl

variable {W : WeierstrassCurve ℂ}

/-- The `x`-coordinate of `ξ`. -/
def xc (ξ : ℂ → W.toAffine.Point) (z : ℂ) : ℂ := xP (ξ z)

/-- The `y`-coordinate of `ξ`. -/
def yc (ξ : ℂ → W.toAffine.Point) (z : ℂ) : ℂ := yP (ξ z)

/-- Affine holomorphic coordinates near a point not sent to `O`. -/
theorem exists_affine_chart {ξ : ℂ → W.toAffine.Point} (hh : IsHolomorphicMap W ξ) {z₀ : ℂ}
    (hz : ξ z₀ ≠ 0) : ∃ V : Set ℂ, IsOpen V ∧ z₀ ∈ V ∧ ∃ X Y Z : ℂ → ℂ, DifferentiableOn ℂ X V ∧
      DifferentiableOn ℂ Y V ∧ DifferentiableOn ℂ Z V ∧
      ∀ z ∈ V, Z z ≠ 0 ∧ ξ z ≠ 0 ∧ xc ξ z = X z / Z z ∧ yc ξ z = Y z / Z z := by
  obtain ⟨U, X, Y, Z, hzU, hUo, hXd, hYd, hZd, hc⟩ := hh z₀
  refine ⟨U ∩ Z ⁻¹' {0}ᶜ, hZd.continuousOn.isOpen_inter_preimage hUo isOpen_compl_singleton,
    ⟨hzU, (hc z₀ hzU).ne_zero_iff.1 hz⟩, X, Y, Z, hXd.mono Set.inter_subset_left,
    hYd.mono Set.inter_subset_left, hZd.mono Set.inter_subset_left, fun z hz => ?_⟩
  have hξz : ξ z ≠ 0 := (hc z hz.1).ne_zero_iff.2 hz.2
  exact ⟨hz.2, hξz, ((hc z hz.1).coords hξz).1, ((hc z hz.1).coords hξz).2⟩

theorem isOpen_ne_zero {ξ : ℂ → W.toAffine.Point} (hh : IsHolomorphicMap W ξ) :
    IsOpen {z | ξ z ≠ 0} := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨V, hVo, hzV, X, Y, Z, -, -, -, hV⟩ := exists_affine_chart hh hz
  exact ⟨V, fun w hw => (hV w hw).2.1, hVo, hzV⟩

theorem differentiableOn_xc {ξ : ℂ → W.toAffine.Point} (hh : IsHolomorphicMap W ξ) :
    DifferentiableOn ℂ (xc ξ) {z | ξ z ≠ 0} := by
  intro z hz
  obtain ⟨V, hVo, hzV, X, Y, Z, hXd, -, hZd, hV⟩ := exists_affine_chart hh hz
  have hV' : V ∈ 𝓝 z := hVo.mem_nhds hzV
  have hd : DifferentiableAt ℂ (fun w => X w / Z w) z :=
    (hXd.differentiableAt hV').div (hZd.differentiableAt hV') (hV z hzV).1
  exact (hd.congr_of_eventuallyEq (Filter.eventually_of_mem hV' fun w hw => (hV w hw).2.2.1)).differentiableWithinAt

theorem differentiableOn_yc {ξ : ℂ → W.toAffine.Point} (hh : IsHolomorphicMap W ξ) :
    DifferentiableOn ℂ (yc ξ) {z | ξ z ≠ 0} := by
  intro z hz
  obtain ⟨V, hVo, hzV, X, Y, Z, -, hYd, hZd, hV⟩ := exists_affine_chart hh hz
  have hV' : V ∈ 𝓝 z := hVo.mem_nhds hzV
  have hd : DifferentiableAt ℂ (fun w => Y w / Z w) z :=
    (hYd.differentiableAt hV').div (hZd.differentiableAt hV') (hV z hzV).1
  exact (hd.congr_of_eventuallyEq (Filter.eventually_of_mem hV' fun w hw => (hV w hw).2.2.2)).differentiableWithinAt

end Liouville

end ZInQ.Contrib.HCMLattice
