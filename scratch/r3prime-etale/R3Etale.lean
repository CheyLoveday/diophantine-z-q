import ZInQKernel.Contrib.OneProof.AnalyticStableHeight

open CategoryTheory AlgebraicGeometry MeasureTheory Topology Set Filter MonObj
open ZInQ.DefFaltings ZInQ.HeightSplit ZInQ.HeightGlue ZInQ.HeightDict ZInQ.HeightFix ZInQ.R3Residual

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace ZInQ.R3Etale

/-! ## §1. Serre's sheaf of holomorphic functions on `A_τ(ℂ)^an` and its charts -/

section Defs

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- The values `(s₁(x), …, s_m(x))` of finitely many regular functions at a complex point. -/
noncomputable def evalVec (𝒢 : GroupModel A L) (τ : L →+* ℂ) {m : ℕ} (U : Fin m → 𝒢.G.left.Opens)
    (s : ∀ j, Γ(𝒢.G.left, U j)) (x : 𝒢.Pts τ) : Fin m → ℂ :=
  fun j => 𝒢.evalAt x (U j) (s j)

/-- **Serre's sheaf of holomorphic functions on `A_τ(ℂ)^an`** (Serre, GAGA §2; SGA 1 XII 1.1, the
reduced structure sheaf): `h` is holomorphic at `q` when, near `q` (analytic topology `anTop`), it is
`H(s₁, …, s_m)` for finitely many regular functions `s_j ∈ Γ(U_j, 𝒪_𝒢)` defined at `q` and a function
`H` holomorphic near `(s_j(q))_j ∈ ℂ^m`. On an affine piece `U ↪ ℂ^n` (generators of `Γ(U)`) this is
"locally the restriction of a holomorphic function of the coordinates". No étale coordinates enter. -/
def AnHolAt (𝒢 : GroupModel A L) (τ : L →+* ℂ) (h : 𝒢.Pts τ → ℂ) (q : 𝒢.Pts τ) : Prop :=
  ∃ (m : ℕ) (U : Fin m → 𝒢.G.left.Opens) (s : ∀ j, Γ(𝒢.G.left, U j)) (H : (Fin m → ℂ) → ℂ),
    (∀ j, ⊤ ≤ q.left ⁻¹ᵁ U j) ∧ (∀ᶠ y in 𝓝 (evalVec 𝒢 τ U s q), DifferentiableAt ℂ H y) ∧
    ∀ᶠ x in @nhds _ (anTop 𝒢 τ) q, h x = H (evalVec 𝒢 τ U s x)

/-- **`φ` is a chart of the complex space `(A_τ(ℂ), 𝒪^an)`**: a homeomorphism from an open subset of
`A_τ(ℂ)` onto an open subset of `ℂ^g` which is an isomorphism of ringed spaces, i.e. at every point
`q` of its domain a function is holomorphic at `q` in Serre's sense (`AnHolAt`) iff it is a holomorphic
function of the chart coordinate near `φ q`. -/
def IsSerreChart (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (φ : @OpenPartialHomeomorph (𝒢.Pts τ) (Fin g → ℂ) (anTop 𝒢 τ) _) : Prop :=
  letI := anTop 𝒢 τ
  ∀ q ∈ φ.source, ∀ h : 𝒢.Pts τ → ℂ,
    AnHolAt 𝒢 τ h q ↔ ∀ᶠ y in 𝓝 (φ q), DifferentiableAt ℂ (h ∘ φ.symm) y

end Defs

/-- **GLUE `TranslationAnHol`: left translation by a complex point is holomorphic.** For a group
model `𝒢`, `τ`, a regular function `s ∈ Γ(U, 𝒪_𝒢)` and complex points `p, x₀` with `p x₀ ∈ U(ℂ)`,
the function `x ↦ s(p x)` is holomorphic at `x₀` in Serre's sense. (Left translation by `p` is a
morphism of the complex variety `𝒢 ×_{𝓞_L,τ} ℂ`; morphisms are holomorphic, GAGA §2 / SGA 1 XII 1.1.
Concretely: on an affine open of `𝒢 ×_{𝓞_L} 𝒢` around `(p, x₀)`, `μ^* s = r / b^N` with
`r, b ∈ R₁ ⊗ R₂`, so `s(p x) = Σ αₖ(p) βₖ(x) / (Σ aⱼ(p) cⱼ(x))^N`.) -/
def TranslationAnHol : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (U : 𝒢.G.left.Opens) (s : Γ(𝒢.G.left, U)) (p x₀ : 𝒢.Pts τ),
    ⊤ ≤ (p * x₀).left ⁻¹ᵁ U → AnHolAt 𝒢 τ (fun x => 𝒢.evalAt (p * x) U s) x₀

/-! ## §2. Generic analysis -/

section Generic

variable {g : ℕ}

/-- A holomorphic map with invertible derivative at `z` has a holomorphic local inverse. -/
theorem exists_localInverse {ψ : (Fin g → ℂ) → (Fin g → ℂ)} {z : Fin g → ℂ}
    (hd : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ψ w) (hdet : (fderiv ℂ ψ z).det ≠ 0) :
    ∃ σ : (Fin g → ℂ) → (Fin g → ℂ), σ (ψ z) = z ∧ ContinuousAt σ (ψ z) ∧
      (∀ᶠ y in 𝓝 (ψ z), DifferentiableAt ℂ σ y) ∧ (∀ᶠ w in 𝓝 z, σ (ψ w) = w) := by
  obtain ⟨V, hVsub, hVo, hzV⟩ := mem_nhds_iff.mp hd
  have hdV : DifferentiableOn ℂ ψ V := fun w hw => (hVsub hw).differentiableWithinAt
  have hstrict : HasStrictFDerivAt ψ
      ((equivOfDet _ hdet : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) z := by
    rw [equivOfDet_coe]; exact Holomorphic.hasStrictFDerivAt hVo hdV hzV
  set P := hstrict.toOpenPartialHomeomorph ψ
  have hPcoe : (P : (Fin g → ℂ) → (Fin g → ℂ)) = ψ := hstrict.toOpenPartialHomeomorph_coe
  have hzs : z ∈ P.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hzt : ψ z ∈ P.target := by rw [← hPcoe]; exact P.map_source hzs
  have hσz : P.symm (ψ z) = z := by
    have := P.left_inv hzs; rwa [hPcoe] at this
  have hcσ : ContinuousAt P.symm (ψ z) := P.continuousAt_symm hzt
  refine ⟨P.symm, hσz, hcσ, ?_, ?_⟩
  · have hgood := eventually_det_ne hVo hdV hzV hdet
    rw [← hσz] at hgood
    filter_upwards [hcσ.eventually hgood, P.open_target.mem_nhds hzt] with y hy hyt
    obtain ⟨hyV, hydet⟩ := hy
    have hfd : HasFDerivAt (P : (Fin g → ℂ) → (Fin g → ℂ))
        ((equivOfDet _ hydet : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
        (P.symm y) := by
      rw [hPcoe, equivOfDet_coe]; exact (hdV.differentiableAt (hVo.mem_nhds hyV)).hasFDerivAt
    exact (P.hasFDerivAt_symm hyt hfd).differentiableAt
  · filter_upwards [P.open_source.mem_nhds hzs] with w hw
    have := P.left_inv hw; rwa [hPcoe] at this

theorem det_comp_eq (A B : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) :
    (A.comp B).det = A.det * B.det := by
  change LinearMap.det ((A : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).comp (B : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) =
    LinearMap.det (A : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) * LinearMap.det (B : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
  exact LinearMap.det_comp _ _

end Generic

/-! ## §3. Serre's sheaf along a uniformization -/

section Along

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- Finitely many Serre-holomorphic functions are jointly a holomorphic function of one finite
family of regular functions. -/
theorem anHolAt_pi (𝒢 : GroupModel A L) (τ : L →+* ℂ) {n : ℕ} {f : 𝒢.Pts τ → (Fin n → ℂ)}
    {q : 𝒢.Pts τ} (hf : ∀ i, AnHolAt 𝒢 τ (fun x => f x i) q) :
    ∃ (m : ℕ) (U : Fin m → 𝒢.G.left.Opens) (s : ∀ j, Γ(𝒢.G.left, U j))
      (H : (Fin m → ℂ) → (Fin n → ℂ)),
      (∀ j, ⊤ ≤ q.left ⁻¹ᵁ U j) ∧ (∀ᶠ y in 𝓝 (evalVec 𝒢 τ U s q), DifferentiableAt ℂ H y) ∧
      ∀ᶠ x in @nhds _ (anTop 𝒢 τ) q, f x = H (evalVec 𝒢 τ U s x) := by
  letI := anTop 𝒢 τ
  choose m U s H hU hH hev using hf
  let e : Fin (∑ i, m i) ≃ (Σ i, Fin (m i)) := finSigmaFinEquiv.symm
  let W : Fin (∑ i, m i) → 𝒢.G.left.Opens := fun j => U (e j).1 (e j).2
  let t : ∀ j, Γ(𝒢.G.left, W j) := fun j => s (e j).1 (e j).2
  let Lm : ∀ i : Fin n, (Fin (∑ i, m i) → ℂ) →L[ℂ] (Fin (m i) → ℂ) := fun i =>
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (e.symm ⟨i, j⟩)
  have hL : ∀ x i, Lm i (evalVec 𝒢 τ W t x) = evalVec 𝒢 τ (U i) (s i) x := by
    intro x i
    funext j
    let F : (Σ i, Fin (m i)) → ℂ := fun σ => 𝒢.evalAt x (U σ.1 σ.2) (s σ.1 σ.2)
    show F (e (e.symm ⟨i, j⟩)) = F ⟨i, j⟩
    rw [Equiv.apply_symm_apply]
  refine ⟨∑ i, m i, W, t, fun y i => H i (Lm i y), fun j => hU _ _, ?_, ?_⟩
  · have hi : ∀ i, ∀ᶠ y in 𝓝 (evalVec 𝒢 τ W t q), DifferentiableAt ℂ (H i) (Lm i y) := by
      intro i
      have h1 := hH i
      rw [← hL q i] at h1
      exact (Lm i).continuous.continuousAt.eventually h1
    filter_upwards [Filter.eventually_all.mpr hi] with y hy
    exact differentiableAt_pi.mpr fun i => (hy i).comp y (Lm i).differentiableAt
  · filter_upwards [Filter.eventually_all.mpr hev] with x hx
    funext i
    rw [hx i, hL x i]

/-- Serre-holomorphic functions are holomorphic along an analytic uniformization. -/
theorem holo_of_anHolAt (𝒢 : GroupModel A L) {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (hΦc : @Continuous _ _ _ (anTop 𝒢 τ) Φ) {h : 𝒢.Pts τ → ℂ} {z : Fin g → ℂ}
    (hh : AnHolAt 𝒢 τ h (Φ z)) : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (h ∘ Φ) w := by
  letI := anTop 𝒢 τ
  obtain ⟨m, U, s, H, hU, hH, hev⟩ := hh
  set D := ⋂ j, 𝒢.dom Φ (U j)
  have hDo : IsOpen D := isOpen_iInter_of_finite fun j => hΦ.2.2.2.1 (U j)
  have hzD : z ∈ D := mem_iInter.mpr fun j => hU j
  have hψd : DifferentiableOn ℂ (evalVec 𝒢 τ U s ∘ Φ) D :=
    differentiableOn_pi.mpr fun j => (hΦ.2.2.2.2 (U j) (s j)).mono (iInter_subset _ j)
  have hψ : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (evalVec 𝒢 τ U s ∘ Φ) w :=
    Filter.eventually_of_mem (hDo.mem_nhds hzD) fun w hw => hψd.differentiableAt (hDo.mem_nhds hw)
  have hcont : ContinuousAt (evalVec 𝒢 τ U s ∘ Φ) z :=
    (hψd.differentiableAt (hDo.mem_nhds hzD)).continuousAt
  have hH' := hcont.eventually hH
  have hev' := (hΦc.continuousAt.eventually hev).eventually_nhds
  filter_upwards [hψ, hH', hev'] with w hw1 hw2 hw3
  have : DifferentiableAt ℂ (H ∘ (evalVec 𝒢 τ U s ∘ Φ)) w := hw2.comp w hw1
  exact this.congr_of_eventuallyEq hw3

/-- `1 ∈ U(ℂ)` for an open `U` containing the origin of the generic fibre. -/
theorem one_mem_of_genericUnit (𝒢 : GroupModel A L) {τ : L →+* ℂ} {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → 𝒢.Pts τ}
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (U : 𝒢.G.left.Opens) (hU : 𝒢.genericUnit ∈ U) :
    ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ U := by
  have h0 : Φ 0 = 1 := (hΦ.2.1 0).2 Λ.zero_mem
  have := ZInQ.Metrization.zero_mem_dom 𝒢 hΦ U hU
  rw [← h0]; exact this

/-- The translated algebraic coordinates are Serre-holomorphic (from `TranslationAnHol`). -/
theorem chartAt_anHolAt (hTH : TranslationAnHol) (𝒢 : GroupModel A L) {τ : L →+* ℂ} {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → 𝒢.Pts τ}
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (U : Fin g → 𝒢.G.left.Opens)
    (hU : ∀ i, 𝒢.genericUnit ∈ U i) (s : ∀ i, Γ(𝒢.G.left, U i)) (q : 𝒢.Pts τ) (i : Fin g) :
    AnHolAt 𝒢 τ (fun x => chartAt 𝒢 τ U s q x i) q := by
  refine hTH K A L 𝒢 τ (U i) (s i) q⁻¹ q ?_
  rw [inv_mul_cancel]
  exact one_mem_of_genericUnit 𝒢 hΦ (U i) (hU i)

variable [NumberField K]

/-- **Holomorphic along the uniformization ⇒ Serre-holomorphic** (from `TranslationAnHol`). -/
theorem anHolAt_of_holo (hTH : TranslationAnHol) {g : ℕ} (M : MetrizedModel A L g)
    (τ : L →+* ℂ) {Φ : (Fin g → ℂ) → M.model.Pts τ}
    (hΦ : M.model.IsAnalyticUniformization τ (M.hodge.periods τ) Φ)
    (hc : ∀ f, M.hodge.coeff τ (M.model.wedge f) = M.model.jacDet Φ f)
    {h : M.model.Pts τ → ℂ} {z : Fin g → ℂ} (hh : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (h ∘ Φ) w) :
    AnHolAt M.model τ h (Φ z) := by
  letI := anTop M.model τ
  haveI : T2Space (M.model.Pts τ) := analyticPointsT2 K A L M.model τ
  haveI := M.hodge.periods_discrete τ
  haveI := M.hodge.periods_isZLattice τ
  have hUnif : TorusVolume.IsUnif (M.hodge.periods τ) Φ :=
    ⟨continuous_of_isAnalyticUniformization M.model τ hΦ, hΦ.1, hΦ.2.1, hΦ.2.2.1⟩
  obtain ⟨U, hU, s, hm, hw⟩ := exists_algCoord M τ
  set q := Φ z with hqdef
  set k := chartAt M.model τ U s q with hkdef
  obtain ⟨m, W, t, Hk, hWq, hHk, hkev⟩ :=
    anHolAt_pi M.model τ (f := k) (chartAt_anHolAt hTH M.model hΦ U hU s q)
  obtain ⟨V, hVo, hzV, hdV, hdet⟩ := chart_comp_unif M.model hΦ U hU s hm z
  have hdet' : (fderiv ℂ (k ∘ Φ) z).det ≠ 0 := by rw [hdet]; exact jacDet_ne_zero M hc _ hw
  have hψd : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (k ∘ Φ) w :=
    Filter.eventually_of_mem (hVo.mem_nhds hzV) fun w hw => hdV.differentiableAt (hVo.mem_nhds hw)
  obtain ⟨σ, hσz, hσc, hσd, hσψ⟩ := exists_localInverse hψd hdet'
  have hkq : Hk (evalVec M.model τ W t q) = k q := hkev.self_of_nhds.symm
  have hkz : (k ∘ Φ) z = k q := rfl
  rw [hkz] at hσz hσc hσd
  have hHc : ContinuousAt Hk (evalVec M.model τ W t q) := hHk.self_of_nhds.continuousAt
  refine ⟨m, W, t, (h ∘ Φ) ∘ σ ∘ Hk, hWq, ?_, ?_⟩
  · have h2 : ∀ᶠ y in 𝓝 (evalVec M.model τ W t q), DifferentiableAt ℂ σ (Hk y) := by
      rw [← hkq] at hσd
      exact hHc.eventually hσd
    have hc2 : ContinuousAt (σ ∘ Hk) (evalVec M.model τ W t q) := by
      refine ContinuousAt.comp ?_ hHc
      rw [hkq]; exact hσc
    have h3 : ∀ᶠ y in 𝓝 (evalVec M.model τ W t q), DifferentiableAt ℂ (h ∘ Φ) (σ (Hk y)) := by
      have hσq : (σ ∘ Hk) (evalVec M.model τ W t q) = z := by
        show σ (Hk _) = z; rw [hkq]; exact hσz
      have hh' := hh
      rw [← hσq] at hh'
      exact hc2.eventually hh'
    filter_upwards [hHk, h2, h3] with y hy1 hy2 hy3
    exact hy3.comp y (hy2.comp y hy1)
  · obtain ⟨O, hOsub, hOo, hzO⟩ := mem_nhds_iff.mp hσψ
    have hΦO : Φ '' O ∈ 𝓝 q := (hUnif.isOpenMap O hOo).mem_nhds ⟨z, hzO, rfl⟩
    filter_upwards [hΦO, hkev] with x hx hx2
    obtain ⟨w, hwO, rfl⟩ := hx
    show h (Φ w) = h (Φ (σ (Hk (evalVec M.model τ W t (Φ w)))))
    rw [← hx2]
    exact congrArg (fun w' => h (Φ w')) (hOsub hwO).symm

end Along

/-! ## §4. R3′: the holomorphic charts are the charts of Serre's complex structure -/

section Main

variable {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K} {L : Type} [Field L]
  [NumberField L] [Algebra K L]

/-- **R3′.** For every group model `𝒢` of `A_L` (`g = dim A`) and every `τ`, a homeomorphism `φ` from
an open subset of `A_τ(ℂ)` onto an open subset of `ℂ^g` is a holomorphic chart in the sense of
`IsHolChart` (algebraic coordinates, translated, are holomorphic coordinates in `φ`) iff it is a chart
of Serre's complex space `(A_τ(ℂ), 𝒪^an)` (`IsSerreChart`). Through T35 and `TranslationAnHol`. -/
theorem isHolChart_iff_isSerreChart (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hTH : TranslationAnHol) (𝒢 : GroupModel A L) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞))
    (τ : L →+* ℂ) (φ : @OpenPartialHomeomorph (𝒢.Pts τ) (Fin g → ℂ) (anTop 𝒢 τ) _) :
    IsHolChart 𝒢 τ φ ↔ IsSerreChart 𝒢 τ φ := by
  letI := anTop 𝒢 τ
  obtain ⟨M, rfl⟩ := exists_metrized hT35 𝒢 g hg
  obtain ⟨Φ, hΦ, hc⟩ := M.arch τ
  haveI : T2Space (M.model.Pts τ) := analyticPointsT2 K A L M.model τ
  haveI := M.hodge.periods_discrete τ
  haveI := M.hodge.periods_isZLattice τ
  have hUnif : TorusVolume.IsUnif (M.hodge.periods τ) Φ :=
    ⟨continuous_of_isAnalyticUniformization M.model τ hΦ, hΦ.1, hΦ.2.1, hΦ.2.2.1⟩
  constructor
  · intro hφ q hq h
    obtain ⟨z, rfl⟩ := hUnif.surj q
    obtain ⟨O, hOo, hzO, hdO, hdetO⟩ := unif_holChart hT35 M.model g hg τ hΦ φ hφ z hq
    constructor
    · intro hh
      have hhΦ := holo_of_anHolAt M.model hΦ hUnif.cont hh
      obtain ⟨O₂, hO₂sub, hO₂o, hzO₂⟩ := mem_nhds_iff.mp hhΦ
      obtain ⟨V, hVo, hV, hdV⟩ := holo_in_chart_of_lift φ Φ hUnif.cont hq hOo hzO hdO hdetO h
        hO₂o hzO₂ (fun w hw => (hO₂sub hw).differentiableWithinAt)
      exact Filter.eventually_of_mem (hVo.mem_nhds hV) fun y hy =>
        hdV.differentiableAt (hVo.mem_nhds hy)
    · intro hh
      apply anHolAt_of_holo hTH M τ hΦ hc
      have hcφ : ContinuousAt (φ ∘ Φ) z := (hdO.differentiableAt (hOo.mem_nhds hzO)).continuousAt
      have hh' := hcφ.eventually hh
      have hsrc : ∀ᶠ w in 𝓝 z, Φ w ∈ φ.source :=
        hUnif.cont.continuousAt.eventually (φ.open_source.mem_nhds hq)
      filter_upwards [hh', hOo.mem_nhds hzO, hsrc.eventually_nhds] with w hw1 hw2 hw3
      have hd : DifferentiableAt ℂ ((h ∘ φ.symm) ∘ (φ ∘ Φ)) w :=
        hw1.comp w (hdO.differentiableAt (hOo.mem_nhds hw2))
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [hw3] with w' hw'
      simp only [Function.comp_apply, φ.left_inv hw']
  · intro hφ q hq U hU s hm hw
    obtain ⟨z, rfl⟩ := hUnif.surj q
    set k := chartAt M.model τ U s (Φ z) with hkdef
    have hkd : ∀ i, ∀ᶠ y in 𝓝 (φ (Φ z)), DifferentiableAt ℂ ((fun x => k x i) ∘ φ.symm) y :=
      fun i => (hφ _ hq _).mp (chartAt_anHolAt hTH M.model hΦ U hU s (Φ z) i)
    have hkd' : ∀ᶠ y in 𝓝 (φ (Φ z)), DifferentiableAt ℂ (k ∘ φ.symm) y := by
      filter_upwards [Filter.eventually_all.mpr hkd] with y hy
      exact differentiableAt_pi.mpr hy
    have hφi : ∀ i, AnHolAt M.model τ (fun x => φ x i) (Φ z) := fun i => by
      refine (hφ _ hq _).mpr ?_
      filter_upwards [φ.open_target.mem_nhds (φ.map_source hq)] with y hy
      have heq : ((fun x => φ x i) ∘ φ.symm) =ᶠ[𝓝 y] (fun y : Fin g → ℂ => y i) := by
        filter_upwards [φ.open_target.mem_nhds hy] with y' hy'
        simp only [Function.comp_apply, φ.right_inv hy']
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) i).differentiableAt.congr_of_eventuallyEq
        heq
    have hφΦ : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (φ ∘ Φ) w := by
      filter_upwards [Filter.eventually_all.mpr fun i =>
        holo_of_anHolAt M.model hΦ hUnif.cont (hφi i)] with w hw
      exact differentiableAt_pi.mpr hw
    obtain ⟨V, hVo, hzV, hdV, hdet⟩ := chart_comp_unif M.model hΦ U hU s hm z
    have hdet' : (fderiv ℂ (k ∘ Φ) z).det ≠ 0 := by rw [hdet]; exact jacDet_ne_zero M hc _ hw
    have heq : (k ∘ Φ) =ᶠ[𝓝 z] (k ∘ φ.symm) ∘ (φ ∘ Φ) := by
      filter_upwards [hUnif.cont.continuousAt.eventually (φ.open_source.mem_nhds hq)] with w hw
      simp only [Function.comp_apply, φ.left_inv hw]
    have hfd : fderiv ℂ (k ∘ Φ) z =
        (fderiv ℂ (k ∘ φ.symm) (φ (Φ z))).comp (fderiv ℂ (φ ∘ Φ) z) := by
      rw [heq.fderiv_eq]; exact fderiv_comp z hkd'.self_of_nhds hφΦ.self_of_nhds
    refine ⟨interior {y | DifferentiableAt ℂ (k ∘ φ.symm) y}, isOpen_interior,
      mem_interior_iff_mem_nhds.mpr hkd', fun y hy =>
        (interior_subset (s := {y | DifferentiableAt ℂ (k ∘ φ.symm) y}) hy :
          DifferentiableAt ℂ (k ∘ φ.symm) y).differentiableWithinAt, ?_⟩
    intro h0
    apply hdet'
    rw [hfd, det_comp_eq, h0, zero_mul]

end Main

end ZInQ.R3Etale

#print axioms ZInQ.R3Etale.isHolChart_iff_isSerreChart
