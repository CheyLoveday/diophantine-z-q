import ZInQKernel.Contrib.OneProof.JavanpeykarRebase

open CategoryTheory AlgebraicGeometry MeasureTheory Topology Set MonObj Filter
open ZInQ.DefFaltings ZInQ.HeightSplit ZInQ.HeightGlue ZInQ.HeightDict ZInQ.HeightFix
open scoped NumberField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace ZInQ.R3Residual

/-! ## §1. Generic: charts from a uniformized group and holomorphic maps of `ℂ^g` -/

section Generic

variable {g : ℕ}

/-- The determinant of the derivative of a holomorphic map is nonzero near a point where it is. -/
theorem eventually_det_ne {f : (Fin g → ℂ) → (Fin g → ℂ)} {V : Set (Fin g → ℂ)} (hV : IsOpen V)
    (hf : DifferentiableOn ℂ f V) {z : Fin g → ℂ} (hz : z ∈ V) (hdet : (fderiv ℂ f z).det ≠ 0) :
    ∀ᶠ w in 𝓝 z, w ∈ V ∧ (fderiv ℂ f w).det ≠ 0 := by
  have hc : ContinuousAt (fun w => (fderiv ℂ f w).det) z :=
    ContinuousLinearMap.continuous_det.continuousAt.comp (Holomorphic.continuousAt_fderiv hV hf hz)
  exact Filter.Eventually.and (show ∀ᶠ w in 𝓝 z, w ∈ V from hV.mem_nhds hz)
    (hc.eventually (isOpen_ne.mem_nhds hdet))

/-- A continuous linear equivalence with a given underlying map, from a nonzero determinant. -/
noncomputable def equivOfDet (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) (h : D.det ≠ 0) :
    (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) :=
  (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr h)).toContinuousLinearEquiv

@[simp] theorem equivOfDet_coe (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) (h : D.det ≠ 0) :
    ((equivOfDet D h : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) = D := by
  ext x; simp [equivOfDet]

variable {X : Type*} [Group X] [TopologicalSpace X] [T2Space X]
variable {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
variable {Φ : (Fin g → ℂ) → X}

/-- **Charts on a uniformized group from a map with invertible holomorphic lift.** Let
`Φ : ℂ^g → X` be a continuous surjective homomorphism with kernel the full lattice `Λ`, and
`h : X → ℂ^g` such that `h ∘ Φ` is holomorphic on an open `V ∋ z₀` with invertible derivative at
`z₀`. Then `h` agrees near `Φ z₀` with a homeomorphism `e` onto an open subset of `ℂ^g`, whose inverse
lifts through `Φ` along a map `σ` that is holomorphic on `e.target`, with derivative the inverse of
the derivative of `h ∘ Φ` (invertible at each point of `σ(e.target)`). -/
theorem exists_chart_of_lift (hΦ : TorusVolume.IsUnif Λ Φ) (h : X → (Fin g → ℂ))
    {V : Set (Fin g → ℂ)} (hV : IsOpen V) (hd : DifferentiableOn ℂ (h ∘ Φ) V) {z₀ : Fin g → ℂ}
    (hz₀ : z₀ ∈ V) (hdet : (fderiv ℂ (h ∘ Φ) z₀).det ≠ 0) :
    ∃ (e : OpenPartialHomeomorph X (Fin g → ℂ)) (σ : (Fin g → ℂ) → (Fin g → ℂ)),
      Φ z₀ ∈ e.source ∧ EqOn h e e.source ∧ σ (e (Φ z₀)) = z₀ ∧ ContinuousOn σ e.target ∧
      ∀ x ∈ e.target, e.symm x = Φ (σ x) ∧ σ x ∈ V ∧ ∃ hx : (fderiv ℂ (h ∘ Φ) (σ x)).det ≠ 0,
        HasFDerivAt σ ((equivOfDet _ hx).symm : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) x := by
  set ψ := h ∘ Φ with hψdef
  have hstrict : HasStrictFDerivAt ψ
      ((equivOfDet _ hdet : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) z₀ := by
    rw [equivOfDet_coe]; exact Holomorphic.hasStrictFDerivAt hV hd hz₀
  let P := hstrict.toOpenPartialHomeomorph ψ
  have hPcoe : (P : (Fin g → ℂ) → (Fin g → ℂ)) = ψ := hstrict.toOpenPartialHomeomorph_coe
  -- the open set where `ψ` is holomorphic with invertible derivative, inside an injectivity ball
  obtain ⟨r₀, hr₀, hsep⟩ := TorusVolume.exists_ball_sub_mem Λ
  have hcont : ContinuousOn (fun w => (fderiv ℂ ψ w).det) V := fun w hw =>
    (ContinuousLinearMap.continuous_det.continuousAt.comp
      (Holomorphic.continuousAt_fderiv hV hd hw)).continuousWithinAt
  set N := (V ∩ (fun w => (fderiv ℂ ψ w).det) ⁻¹' {0}ᶜ) ∩ Metric.ball z₀ r₀
  have hNo : IsOpen N := (hcont.isOpen_inter_preimage hV isOpen_compl_singleton).inter Metric.isOpen_ball
  have hz₀N : z₀ ∈ N := ⟨⟨hz₀, hdet⟩, Metric.mem_ball_self hr₀⟩
  let P' := P.restrOpen N hNo
  have hP'coe : (P' : (Fin g → ℂ) → (Fin g → ℂ)) = ψ := hPcoe
  have hP'src : P'.source = P.source ∩ N := P.restrOpen_source N hNo
  -- `Φ` on the ball
  have hinj : InjOn Φ (Metric.ball z₀ r₀) := fun x hx y hy hxy => by
    have h1 : x - z₀ ∈ Metric.ball (0 : Fin g → ℂ) r₀ := by
      rw [mem_ball_zero_iff, ← dist_eq_norm]; exact hx
    have h2 : y - z₀ ∈ Metric.ball (0 : Fin g → ℂ) r₀ := by
      rw [mem_ball_zero_iff, ← dist_eq_norm]; exact hy
    have := hsep _ h1 _ h2 (by rw [sub_sub_sub_cancel_right]; exact (hΦ.eq_iff x y).mp hxy)
    simpa using this
  let Φl := OpenPartialHomeomorph.ofContinuousOpen (hinj.toPartialEquiv Φ (Metric.ball z₀ r₀))
    hΦ.cont.continuousOn hΦ.isOpenMap Metric.isOpen_ball
  have hΦl : ∀ z, Φl z = Φ z := fun z => rfl
  have hΦls : Φl.source = Metric.ball z₀ r₀ := rfl
  let e := Φl.symm.trans P'
  have hesymm : ∀ x, e.symm x = Φ (P'.symm x) := fun x => rfl
  have hz₀s : z₀ ∈ Φl.source := by rw [hΦls]; exact Metric.mem_ball_self hr₀
  have hp : Φ z₀ ∈ e.source := by
    refine ⟨?_, ?_⟩
    · show Φ z₀ ∈ Φl.symm.source
      rw [OpenPartialHomeomorph.symm_source, ← hΦl]; exact Φl.map_source hz₀s
    · show Φl.symm (Φ z₀) ∈ P'.source
      rw [← hΦl, Φl.left_inv hz₀s, hP'src]
      exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, hz₀N⟩
  have heq : EqOn h e e.source := by
    intro x hx
    have hxt : x ∈ Φl.target := hx.1
    show h x = P' (Φl.symm x)
    rw [hP'coe, hψdef, Function.comp_apply, ← hΦl, Φl.right_inv hxt]
  refine ⟨e, P'.symm, hp, heq, ?_, P'.continuousOn_symm.mono ?_, ?_⟩
  · show P'.symm (P' (Φl.symm (Φ z₀))) = z₀
    have h1 : Φl.symm (Φ z₀) = z₀ := by rw [← hΦl, Φl.left_inv hz₀s]
    rw [h1, P'.left_inv (by rw [hP'src]; exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, hz₀N⟩)]
  · intro x hx; exact hx.1
  · intro x hx
    have hxt : x ∈ P'.target := hx.1
    have hσs : P'.symm x ∈ P'.source := P'.map_target hxt
    rw [hP'src] at hσs
    have hσN := hσs.2
    refine ⟨hesymm x, hσN.1.1, hσN.1.2, ?_⟩
    have hfd : HasFDerivAt (P' : (Fin g → ℂ) → (Fin g → ℂ))
        ((equivOfDet _ hσN.1.2 : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
        (P'.symm x) := by
      rw [hP'coe]
      convert (hd.differentiableAt (hV.mem_nhds hσN.1.1)).hasFDerivAt using 1
      exact equivOfDet_coe _ _
    exact P'.hasFDerivAt_symm hxt hfd

end Generic

/-! ## §2. The holomorphic charts of `A_τ(ℂ)^an`, defined from algebraic coordinates only -/

section Defs

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- **`φ` is a holomorphic chart of `A_τ(ℂ)^an`.** `φ` is a homeomorphism from an open subset of
`A_τ(ℂ)` (analytic topology) onto an open subset of `ℂ^g` such that, at every point `q` of its domain,
every system of algebraic coordinates centred at `q` (the translate `F(q⁻¹ ·)`, `chartAt`, of regular
functions `F = (f₁, …, f_g)` vanishing at the origin with `df₁ ∧ ⋯ ∧ df_g ≠ 0`) is a holomorphic
function of the chart coordinate near `φ q` with invertible derivative at `φ q`. These are the charts of
the complex-analytic structure of the smooth variety `A_τ`: local algebraic (étale) coordinates are
local analytic coordinates (Serre, GAGA §2; the same construction as the Paul-Lez/HodgeConjecture
`ComplexPoint` manifold vendored in `CloudB3W17Hodge`). No uniformization enters the definition. -/
def IsHolChart (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (φ : @OpenPartialHomeomorph (𝒢.Pts τ) (Fin g → ℂ) (anTop 𝒢 τ) _) : Prop :=
  letI := anTop 𝒢 τ
  ∀ q ∈ φ.source, ∀ (U : Fin g → 𝒢.G.left.Opens) (hU : ∀ i, 𝒢.genericUnit ∈ U i)
    (s : ∀ i, Γ(𝒢.G.left, U i))
    (hm : ∀ i, 𝒢.G.left.presheaf.germ (U i) 𝒢.genericUnit (hU i) (s i) ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk),
    𝒢.wedge (fun i => ⟨_, hm i⟩) ≠ 0 →
    ∃ V : Set (Fin g → ℂ), IsOpen V ∧ φ q ∈ V ∧
      DifferentiableOn ℂ (chartAt 𝒢 τ U s q ∘ φ.symm) V ∧
      (fderiv ℂ (chartAt 𝒢 τ U s q ∘ φ.symm) (φ q)).det ≠ 0

end Defs

/-! ## §3. Algebraic coordinates are holomorphic charts (proved through T35) -/

section AlgCharts

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- In the coordinates of an analytic uniformization, the algebraic chart centred at `Φ z` is
holomorphic near `z`, with derivative at `z` of determinant `jacDet Φ f`. -/
theorem chart_comp_unif {g : ℕ} (𝒢 : GroupModel A L) {τ : L →+* ℂ}
    {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → 𝒢.Pts τ}
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (U : Fin g → 𝒢.G.left.Opens)
    (hU : ∀ i, 𝒢.genericUnit ∈ U i) (s : ∀ i, Γ(𝒢.G.left, U i))
    (hm : ∀ i, 𝒢.G.left.presheaf.germ (U i) 𝒢.genericUnit (hU i) (s i) ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk) (z : Fin g → ℂ) :
    ∃ V : Set (Fin g → ℂ), IsOpen V ∧ z ∈ V ∧
      DifferentiableOn ℂ (chartAt 𝒢 τ U s (Φ z) ∘ Φ) V ∧
      (fderiv ℂ (chartAt 𝒢 τ U s (Φ z) ∘ Φ) z).det = 𝒢.jacDet Φ (fun i => ⟨_, hm i⟩) := by
  set V₀ := ⋂ i, 𝒢.dom Φ (U i)
  have hV₀o : IsOpen V₀ := isOpen_iInter_of_finite fun i => hΦ.2.2.2.1 (U i)
  have h0V : (0 : Fin g → ℂ) ∈ V₀ :=
    mem_iInter.mpr fun i => ZInQ.Metrization.zero_mem_dom 𝒢 hΦ (U i) (hU i)
  have hψd : DifferentiableOn ℂ (coordMap 𝒢 τ U s ∘ Φ) V₀ :=
    differentiableOn_pi.mpr fun i => (hΦ.2.2.2.2 (U i) (s i)).mono (iInter_subset _ i)
  have hsubc : Continuous (fun w : Fin g → ℂ => w - z) := continuous_id.sub continuous_const
  refine ⟨(fun w => w - z) ⁻¹' V₀, hV₀o.preimage hsubc, by simpa using h0V, ?_, ?_⟩
  · rw [chartAt_comp 𝒢 hΦ U s z]
    exact hψd.comp ((differentiable_id.sub_const z).differentiableOn) (fun w hw => hw)
  · have hψ : HasFDerivAt (coordMap 𝒢 τ U s ∘ Φ) (fderiv ℂ (coordMap 𝒢 τ U s ∘ Φ) 0)
        ((fun w : Fin g → ℂ => w - z) z) := by
      simpa only [sub_self] using (Holomorphic.hasStrictFDerivAt hV₀o hψd h0V).hasFDerivAt
    have hsub : HasFDerivAt (fun w : Fin g → ℂ => w - z) (ContinuousLinearMap.id ℂ _) z :=
      (hasFDerivAt_id z).sub_const z
    rw [chartAt_comp 𝒢 hΦ U s z,
      (HasFDerivAt.comp (f := fun w : Fin g → ℂ => w - z) z hψ hsub).fderiv,
      ContinuousLinearMap.comp_id]
    exact det_fderiv_coordMap 𝒢 hΦ U hU s hm

/-- For the uniformization of a metrized model, `df₁ ∧ ⋯ ∧ df_g ≠ 0` gives `jacDet Φ f ≠ 0`. -/
theorem jacDet_ne_zero {g : ℕ} (M : MetrizedModel A L g) {τ : L →+* ℂ}
    {Φ : (Fin g → ℂ) → M.model.Pts τ}
    (hc : ∀ f, M.hodge.coeff τ (M.model.wedge f) = M.model.jacDet Φ f)
    (f : Fin g → IsLocalRing.maximalIdeal M.model.genStalk) (hw : M.model.wedge f ≠ 0) :
    M.model.jacDet Φ f ≠ 0 := by
  rw [← hc f]; exact M.hodge.coeff_apply_ne_zero τ hw

theorem det_comp_symm_ne {g : ℕ} (A : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
    (D : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) (hA : A.det ≠ 0) :
    (A.comp (D.symm : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))).det ≠ 0 := by
  show LinearMap.det ((A.comp (D.symm : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) :
    (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) ≠ 0
  have hco : ((A.comp (D.symm : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) :
      (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) =
      (A : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).comp (D.symm.toLinearEquiv : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :=
    rfl
  rw [hco, LinearMap.det_comp]
  exact mul_ne_zero hA (LinearEquiv.isUnit_det' D.symm.toLinearEquiv).ne_zero

/-- **Algebraic coordinates are holomorphic charts (Φ-free statement).** For every group model `𝒢`
of `A_L` with `g = dim A`, every `τ`, every system of algebraic coordinates `F` at the origin
(`df₁ ∧ ⋯ ∧ df_g ≠ 0`) and every point `p`, the translated coordinates `chartAt F p = F(p⁻¹ ·)` agree
near `p` with a holomorphic chart of `A_τ(ℂ)^an`. The proof uses a T35 uniformization; the statement
does not mention one. -/
theorem exists_holChart [NumberField K] (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (𝒢 : GroupModel A L) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) (τ : L →+* ℂ)
    (U : Fin g → 𝒢.G.left.Opens) (hU : ∀ i, 𝒢.genericUnit ∈ U i) (s : ∀ i, Γ(𝒢.G.left, U i))
    (hm : ∀ i, 𝒢.G.left.presheaf.germ (U i) 𝒢.genericUnit (hU i) (s i) ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk)
    (hw : 𝒢.wedge (fun i => ⟨_, hm i⟩) ≠ 0) (p : 𝒢.Pts τ) :
    letI := anTop 𝒢 τ
    ∃ e : OpenPartialHomeomorph (𝒢.Pts τ) (Fin g → ℂ), p ∈ e.source ∧
      EqOn (chartAt 𝒢 τ U s p) e e.source ∧ IsHolChart 𝒢 τ e := by
  obtain ⟨M, rfl⟩ := exists_metrized hT35 𝒢 g hg
  obtain ⟨Φ, hΦ, hc⟩ := M.arch τ
  letI := anTop M.model τ
  haveI : T2Space (M.model.Pts τ) := analyticPointsT2 K A L M.model τ
  haveI := M.hodge.periods_discrete τ
  haveI := M.hodge.periods_isZLattice τ
  have hUnif : TorusVolume.IsUnif (M.hodge.periods τ) Φ :=
    ⟨continuous_of_isAnalyticUniformization M.model τ hΦ, hΦ.1, hΦ.2.1, hΦ.2.2.1⟩
  obtain ⟨z₀, rfl⟩ := hUnif.surj p
  obtain ⟨V, hVo, hzV, hdV, hdet⟩ := chart_comp_unif M.model hΦ U hU s hm z₀
  have hdet' : (fderiv ℂ (chartAt M.model τ U s (Φ z₀) ∘ Φ) z₀).det ≠ 0 := by
    rw [hdet]; exact jacDet_ne_zero M hc _ hw
  obtain ⟨e, σ, hp, heq, -, hσc, hσ⟩ := exists_chart_of_lift hUnif _ hVo hdV hzV hdet'
  refine ⟨e, hp, heq, ?_⟩
  intro q hq U' hU' s' hm' hw'
  have hqt : e q ∈ e.target := e.map_source hq
  obtain ⟨hsy, -, -, -⟩ := hσ (e q) hqt
  have hzq : Φ (σ (e q)) = q := by rw [← hsy, e.left_inv hq]
  obtain ⟨V', hV'o, hzV', hdV', hdet2⟩ := chart_comp_unif M.model hΦ U' hU' s' hm' (σ (e q))
  rw [hzq] at hdV' hdet2
  set k := chartAt M.model τ U' s' q
  have hWo : IsOpen (e.target ∩ σ ⁻¹' V') := hσc.isOpen_inter_preimage e.open_target hV'o
  have hfun : EqOn (k ∘ e.symm) ((k ∘ Φ) ∘ σ) e.target := fun x hx => by
    simp only [Function.comp_apply, (hσ x hx).1]
  have hσd : DifferentiableOn ℂ σ e.target := fun x hx => by
    obtain ⟨-, -, hx', hfd⟩ := hσ x hx
    exact (HasFDerivAt.differentiableAt (𝕜 := ℂ) hfd).differentiableWithinAt
  refine ⟨e.target ∩ σ ⁻¹' V', hWo, ⟨hqt, hzV'⟩, ?_, ?_⟩
  · exact (hdV'.comp (hσd.mono inter_subset_left) (fun x hx => hx.2)).congr
      (hfun.mono inter_subset_left)
  · obtain ⟨-, -, hx', hfd⟩ := hσ (e q) hqt
    have hev : (k ∘ e.symm) =ᶠ[𝓝 (e q)] ((k ∘ Φ) ∘ σ) :=
      Filter.eventually_of_mem (e.open_target.mem_nhds hqt) hfun
    rw [hev.fderiv_eq,
      ((hdV'.differentiableAt (hV'o.mem_nhds hzV')).hasFDerivAt.comp (e q) hfd).fderiv]
    refine det_comp_symm_ne _ _ ?_
    rw [hdet2]; exact jacDet_ne_zero M hc _ hw'

end AlgCharts

/-! ## §4. Change of variables for densities (Mathlib's Jacobian estimates) -/

section Jacobian

variable {g : ℕ}

open scoped NNReal ENNReal in
/-- **Local Jacobian bounds.** If `G : ℂ^g → ℂ^g` is strictly differentiable at `x` with `ℂ`-linear
derivative `D`, then for every `ε > 0` there is a ball around `x` on which `G` scales Lebesgue measure by
a factor in `[|det D|² − ε, |det D|² + ε]` (`|det_ℝ D| = |det_ℂ D|²`). -/
theorem jacobian_bounds {G : (Fin g → ℂ) → (Fin g → ℂ)} {D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)}
    {x : Fin g → ℂ} (hG : HasStrictFDerivAt G D x) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ T ⊆ Metric.ball x ρ, volume T ≠ ⊤ ∧ volume (G '' T) ≠ ⊤ ∧
      (volume (G '' T)).toReal ≤ (‖D.det‖ ^ 2 + ε) * (volume T).toReal ∧
      (‖D.det‖ ^ 2 - ε) * (volume T).toReal ≤ (volume (G '' T)).toReal := by
  set d : ℝ := ‖D.det‖ ^ 2 with hd
  have hd0 : 0 ≤ d := by positivity
  set A : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ) := D.restrictScalars ℝ
  have hAd : |A.det| = d := by
    rw [TorusVolume.det_restrictScalars_eq, abs_of_nonneg (by positivity)]
  have hup : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), ∀ (s : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → (Fin g → ℂ)),
      ApproximatesLinearOn f A s δ → volume (f '' s) ≤ ENNReal.ofReal (d + ε) * volume s :=
    addHaar_image_le_mul_of_det_lt (volume : Measure (Fin g → ℂ)) A
      (m := Real.toNNReal (d + ε)) (by
        rw [hAd]; exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))
  have hlow : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), ∀ (s : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → (Fin g → ℂ)),
      ApproximatesLinearOn f A s δ → ENNReal.ofReal (d - ε) * volume s ≤ volume (f '' s) := by
    by_cases hdε : ε < d
    · exact mul_le_addHaar_image_of_lt_det (volume : Measure (Fin g → ℂ)) A
        (m := Real.toNNReal (d - ε)) (by
          rw [hAd]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
    · filter_upwards with δ s f _
      rw [ENNReal.ofReal_of_nonpos (by linarith), zero_mul]
      exact bot_le
  obtain ⟨δ, ⟨hδu, hδl⟩, hδpos⟩ := ((hup.and hlow).and self_mem_nhdsWithin).exists
  obtain ⟨s₀, hs₀, hsA⟩ := (hG.restrictScalars ℝ).approximates_deriv_on_nhds (c := δ) (Or.inr hδpos)
  obtain ⟨ρ, hρ, hρs⟩ := Metric.mem_nhds_iff.mp hs₀
  refine ⟨ρ, hρ, fun T hT => ?_⟩
  have hTt : volume T ≠ ⊤ := ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hT)
  have hTA : ApproximatesLinearOn G A T δ := hsA.mono_set (hT.trans hρs)
  have hX1 := hδu T G hTA
  have hX2 := hδl T G hTA
  have hXt : volume (G '' T) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTt) hX1
  refine ⟨hTt, hXt, ?_, ?_⟩
  · have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTt) hX1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  · by_cases hdε : 0 ≤ d - ε
    · have := ENNReal.toReal_mono hXt hX2
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hdε] at this
    · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) ENNReal.toReal_nonneg).trans
        ENNReal.toReal_nonneg

end Jacobian

/-! ## §5. The print's measure `(i/2)^g η̃ ∧ η̄̃`, density in every holomorphic chart -/

section AnDefs

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- **`nu` is the measure `(i/2)^g η̃ ∧ η̄̃` near `p`, read in every holomorphic chart.** Here `η̃` is the
invariant holomorphic `g`-form on `A_τ(ℂ)^an` with `η̃(1) = η`. If `η = l · df₁ ∧ ⋯ ∧ df_g` at the
origin, then at `p` the form `η̃` is `l · dF_p` in the algebraic chart `F_p = F(p⁻¹ ·)` (`chartAt`;
invariance), so in a holomorphic chart `φ` at `p` its coefficient is `l · det D(F_p ∘ φ⁻¹)(φ p)` and
`(i/2)^g η̃ ∧ η̄̃` has density `|τ l|² |det D(F_p ∘ φ⁻¹)(φ p)|²` with respect to Lebesgue measure
`dx₁dy₁⋯dx_gdy_g` of the chart (`(i/2) dz ∧ dz̄ = dx ∧ dy`). This is required for **every** holomorphic
chart `φ` of `A_τ(ℂ)^an` (`IsHolChart`) containing `p`, at the centre `φ p`, with the `ε`-estimate. -/
def HasAnFormDensityAt (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (nu : @Measure (𝒢.Pts τ) (anBorel 𝒢 τ)) (eta : 𝒢.hodgeSpace g) (p : 𝒢.Pts τ) : Prop :=
  letI := anTop 𝒢 τ
  letI := anBorel 𝒢 τ
  ∀ φ : OpenPartialHomeomorph (𝒢.Pts τ) (Fin g → ℂ), IsHolChart 𝒢 τ φ → p ∈ φ.source →
  ∀ (U : Fin g → 𝒢.G.left.Opens) (hU : ∀ i, 𝒢.genericUnit ∈ U i) (s : ∀ i, Γ(𝒢.G.left, U i))
    (hm : ∀ i, 𝒢.G.left.presheaf.germ (U i) 𝒢.genericUnit (hU i) (s i) ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk)
    (l : L), eta = l • 𝒢.wedge (fun i => ⟨_, hm i⟩) →
    ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 p, ∀ E ⊆ W, MeasurableSet E →
      |(nu E).toReal - ‖τ l‖ ^ 2 * ‖(fderiv ℂ (chartAt 𝒢 τ U s p ∘ φ.symm) (φ p)).det‖ ^ 2 *
          (volume (φ '' E)).toReal| ≤ ε * (volume (φ '' E)).toReal

/-- **`nu` is the measure `(i/2)^g η̃ ∧ η̄̃` on the complex manifold `A_τ(ℂ)^an`**: a finite Borel measure
with the density of the form in every holomorphic chart at every point. -/
def IsAnFormMeasure (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (nu : @Measure (𝒢.Pts τ) (anBorel 𝒢 τ)) (eta : 𝒢.hodgeSpace g) : Prop :=
  @IsFiniteMeasure _ (anBorel 𝒢 τ) nu ∧ ∀ p, HasAnFormDensityAt 𝒢 τ nu eta p

/-- **The print's archimedean Faltings metric** `‖η‖²_τ = (i/2)^g ∫_{A_τ(ℂ)^an} η̃ ∧ η̄̃ = r`, the
integral over the complex manifold `A_τ(ℂ)^an` (densities in its holomorphic charts): the measure exists
and every such measure has total mass `r`. -/
def IsAnMetricSq (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} (eta : 𝒢.hodgeSpace g) (r : ℝ) : Prop :=
  letI := anBorel 𝒢 τ
  (∃ nu : Measure (𝒢.Pts τ), IsAnFormMeasure 𝒢 τ nu eta) ∧
    ∀ nu : Measure (𝒢.Pts τ), IsAnFormMeasure 𝒢 τ nu eta → (nu univ).toReal = r

/-- **Faltings' stable height, with the metric integrated over the complex manifold `A_τ(ℂ)^an`.**
`ZInQ.HeightFix.IsPrintedStableHeight` verbatim, with `IsPrintedMetricSq` (densities in translated
algebraic coordinates) replaced by `IsAnMetricSq` (densities in every holomorphic chart of
`A_τ(ℂ)^an`). -/
def IsAnStableHeight {K : Type} [Field K] (A : PkgI3.AbVar K) (x : ℝ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (𝒩 : GroupModel A L) (g : ℕ),
    𝒩.IsNeronModel ∧ IsSemistableRes 𝒩 ∧ A.dim = (g : WithBot ℕ∞) ∧
    ∃ eta ∈ printedDetLattice 𝒩 g, eta ≠ 0 ∧ secIndex (printedDetLattice 𝒩 g) eta ≠ 0 ∧
      ∃ r : (L →+* ℂ) → ℝ, (∀ τ, IsAnMetricSq 𝒩 τ eta (r τ)) ∧
        x = (Real.log (secIndex (printedDetLattice 𝒩 g) eta) -
          (1 / 2) * ∑ τ : L →+* ℂ, Real.log (r τ)) / Module.finrank ℚ L

end AnDefs

/-! ## §6. The print's measure is the chart-by-chart measure (Φ-free statement, proved through T35) -/

section Equiv

variable {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K} {L : Type} [Field L]
  [NumberField L] [Algebra K L]

/-- **Chart independence of the density.** For `η ≠ 0` and `g = dim A`, a Borel measure on `A_τ(ℂ)`
has the density of `(i/2)^g η̃ ∧ η̄̃` at `p` in every holomorphic chart of `A_τ(ℂ)^an`
(`HasAnFormDensityAt`) iff it has the density `|τ l|²` at `p` in the translated algebraic coordinates
(height-fix's `HasFormDensityAt`). `⇒`: the algebraic chart is a holomorphic chart
(`exists_holChart`), in which the coefficient is `l`. `⇐`: change of variables from the algebraic chart
to any holomorphic chart (`jacobian_bounds`). -/
theorem hasAnFormDensityAt_iff (hT35 : ZInQ.LeafPush2.UniformizationExists) (𝒢 : GroupModel A L)
    (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) (τ : L →+* ℂ)
    (nu : @Measure (𝒢.Pts τ) (anBorel 𝒢 τ)) (eta : 𝒢.hodgeSpace g) (heta : eta ≠ 0)
    (p : 𝒢.Pts τ) : HasAnFormDensityAt 𝒢 τ nu eta p ↔ HasFormDensityAt 𝒢 τ nu eta p := by
  letI := anTop 𝒢 τ
  letI := anBorel 𝒢 τ
  have hwne : ∀ (U : Fin g → 𝒢.G.left.Opens) (hU : ∀ i, 𝒢.genericUnit ∈ U i)
      (s : ∀ i, Γ(𝒢.G.left, U i))
      (hm : ∀ i, 𝒢.G.left.presheaf.germ (U i) 𝒢.genericUnit (hU i) (s i) ∈
        IsLocalRing.maximalIdeal 𝒢.genStalk) (l : L),
      eta = l • 𝒢.wedge (fun i => ⟨_, hm i⟩) → 𝒢.wedge (fun i => ⟨_, hm i⟩) ≠ 0 :=
    fun U hU s hm l h hw => heta (by rw [h, hw, smul_zero])
  constructor
  · intro hA U hU s hm l hrep ε hε
    obtain ⟨e, hpe, heq, hhol⟩ :=
      exists_holChart hT35 𝒢 g hg τ U hU s hm (hwne U hU s hm l hrep) p
    obtain ⟨W, hW, hWb⟩ := hA e hhol hpe U hU s hm l hrep ε hε
    have hid : fderiv ℂ (chartAt 𝒢 τ U s p ∘ e.symm) (e p) = ContinuousLinearMap.id ℂ _ := by
      have hev : (chartAt 𝒢 τ U s p ∘ e.symm) =ᶠ[𝓝 (e p)] id :=
        Filter.eventually_of_mem (e.open_target.mem_nhds (e.map_source hpe)) fun x hx => by
          simp only [Function.comp_apply, id]
          rw [heq (e.map_target hx), e.right_inv hx]
      rw [hev.fderiv_eq, fderiv_id]
    have hdet1 : ‖(ContinuousLinearMap.id ℂ (Fin g → ℂ)).det‖ ^ 2 = 1 := by
      simp [ContinuousLinearMap.det]
    refine ⟨W ∩ e.source, inter_mem hW (e.open_source.mem_nhds hpe), fun E hE hEm => ?_⟩
    have himg : chartAt 𝒢 τ U s p '' E = e '' E :=
      (heq.mono (hE.trans inter_subset_right)).image_eq
    have := hWb E (hE.trans inter_subset_left) hEm
    rw [hid, hdet1, _root_.mul_one] at this
    rw [himg]; exact this
  · intro hF φ hφ hpφ U hU s hm l hrep ε hε
    obtain ⟨V, hVo, hpV, hdV, -⟩ := hφ p hpφ U hU s hm (hwne U hU s hm l hrep)
    set G := chartAt 𝒢 τ U s p ∘ φ.symm with hGdef
    set D := fderiv ℂ G (φ p)
    set c := ‖τ l‖ ^ 2 with hcdef
    set d := ‖D.det‖ ^ 2 with hddef
    have hc0 : 0 ≤ c := by positivity
    have hd0 : 0 ≤ d := by positivity
    have hGs : HasStrictFDerivAt G D (φ p) := Holomorphic.hasStrictFDerivAt hVo hdV hpV
    set ε₁ := min 1 (ε / (2 * (c + 1))) with hε₁def
    have hε₁ : 0 < ε₁ := lt_min one_pos (by positivity)
    obtain ⟨ρ, hρ, hJ⟩ := jacobian_bounds hGs hε₁
    set ε₂ := ε / (2 * (d + 1)) with hε₂def
    have hε₂ : 0 < ε₂ := by positivity
    obtain ⟨W₂, hW₂, hW₂b⟩ := hF U hU s hm l hrep ε₂ hε₂
    have hpre : φ ⁻¹' Metric.ball (φ p) ρ ∈ 𝓝 p :=
      (φ.continuousAt hpφ).preimage_mem_nhds (Metric.ball_mem_nhds _ hρ)
    refine ⟨W₂ ∩ φ.source ∩ φ ⁻¹' Metric.ball (φ p) ρ,
      inter_mem (inter_mem hW₂ (φ.open_source.mem_nhds hpφ)) hpre, fun E hE hEm => ?_⟩
    have hEs : E ⊆ φ.source := fun q hq => (hE hq).1.2
    have himg : chartAt 𝒢 τ U s p '' E = G '' (φ '' E) := by
      rw [image_image]
      refine image_congr fun q hq => ?_
      simp only [hGdef, Function.comp_apply, φ.left_inv (hEs hq)]
    have hT : φ '' E ⊆ Metric.ball (φ p) ρ := by
      rintro _ ⟨q, hq, rfl⟩; exact (hE hq).2
    obtain ⟨-, -, hup, hlow⟩ := hJ _ hT
    have hb := hW₂b E (fun q hq => (hE hq).1.1) hEm
    rw [himg] at hb
    set v := (volume (φ '' E)).toReal
    set X := (volume (G '' (φ '' E))).toReal
    set a := (nu E).toReal
    have hv0 : 0 ≤ v := ENNReal.toReal_nonneg
    have h1 : |a - c * X| ≤ ε₂ * ((d + ε₁) * v) :=
      hb.trans (mul_le_mul_of_nonneg_left hup hε₂.le)
    have h2 : |c * X - c * d * v| ≤ c * (ε₁ * v) := by
      rw [show c * X - c * d * v = c * (X - d * v) by ring, abs_mul, abs_of_nonneg hc0]
      refine mul_le_mul_of_nonneg_left ?_ hc0
      rw [abs_le]; constructor <;> nlinarith
    have hε₁1 : ε₁ ≤ 1 := min_le_left _ _
    have hε₁2 : ε₁ ≤ ε / (2 * (c + 1)) := min_le_right _ _
    have e1 : ε₂ * (d + ε₁) ≤ ε / 2 := by
      have : ε₂ * (d + 1) = ε / 2 := by rw [hε₂def]; field_simp
      nlinarith
    have e2 : c * ε₁ ≤ ε / 2 := by
      have h' : c * (ε / (2 * (c + 1))) ≤ ε / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      exact (mul_le_mul_of_nonneg_left hε₁2 hc0).trans h'
    calc |a - c * d * v| = |(a - c * X) + (c * X - c * d * v)| := by ring_nf
      _ ≤ |a - c * X| + |c * X - c * d * v| := abs_add_le _ _
      _ ≤ ε₂ * ((d + ε₁) * v) + c * (ε₁ * v) := add_le_add h1 h2
      _ = (ε₂ * (d + ε₁) + c * ε₁) * v := by ring
      _ ≤ (ε / 2 + ε / 2) * v := mul_le_mul_of_nonneg_right (add_le_add e1 e2) hv0
      _ = ε * v := by ring

theorem isAnFormMeasure_iff (hT35 : ZInQ.LeafPush2.UniformizationExists) (𝒢 : GroupModel A L)
    (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) (τ : L →+* ℂ)
    (nu : @Measure (𝒢.Pts τ) (anBorel 𝒢 τ)) (eta : 𝒢.hodgeSpace g) (heta : eta ≠ 0) :
    IsAnFormMeasure 𝒢 τ nu eta ↔ IsFormMeasure 𝒢 τ nu eta :=
  and_congr Iff.rfl (forall_congr' fun p => hasAnFormDensityAt_iff hT35 𝒢 g hg τ nu eta heta p)

/-- **The print's metric (integral over the complex manifold `A_τ(ℂ)^an`) is height-fix's metric.** -/
theorem isAnMetricSq_iff (hT35 : ZInQ.LeafPush2.UniformizationExists) (𝒢 : GroupModel A L)
    (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) (τ : L →+* ℂ) (eta : 𝒢.hodgeSpace g) (heta : eta ≠ 0)
    (r : ℝ) : IsAnMetricSq 𝒢 τ eta r ↔ IsPrintedMetricSq 𝒢 τ eta r := by
  letI := anBorel 𝒢 τ
  unfold IsAnMetricSq IsPrintedMetricSq
  simp only [isAnFormMeasure_iff hT35 𝒢 g hg τ _ eta heta]

/-- **The two stable heights coincide** (given T35). -/
theorem isAnStableHeight_iff (hT35 : ZInQ.LeafPush2.UniformizationExists) (A : PkgI3.AbVar K)
    (x : ℝ) : IsAnStableHeight A x ↔ ZInQ.HeightFix.IsPrintedStableHeight A x := by
  constructor
  · rintro ⟨L, iF, iN, iA, 𝒩, g, hN, hS, hdim, eta, hetaM, heta0, hsec, r, hr, hx⟩
    exact ⟨L, iF, iN, iA, 𝒩, g, hN, hS, hdim, eta, hetaM, heta0, hsec, r,
      fun τ => (isAnMetricSq_iff hT35 𝒩 g hdim τ eta heta0 (r τ)).mp (hr τ), hx⟩
  · rintro ⟨L, iF, iN, iA, 𝒩, g, hN, hS, hdim, eta, hetaM, heta0, hsec, r, hr, hx⟩
    exact ⟨L, iF, iN, iA, 𝒩, g, hN, hS, hdim, eta, hetaM, heta0, hsec, r,
      fun τ => (isAnMetricSq_iff hT35 𝒩 g hdim τ eta heta0 (r τ)).mpr (hr τ), hx⟩

end Equiv

end ZInQ.R3Residual
