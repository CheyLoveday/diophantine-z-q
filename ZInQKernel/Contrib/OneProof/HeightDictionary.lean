import ZInQKernel.OneProof.H.TailZ4
import ZInQKernel.Contrib.OneProof.HeightDictionary.TorusVolume
import ZInQKernel.Contrib.OneProof.HeightDictionary.Holomorphic

/-! # height-dict: the kernel's Faltings height is the printed one (archimedean dictionary)

`ZInQ.HeightSplit.BostLowerBound` and `ZInQ.HeightSplit.GaudronRemondThm14` are stated over
`IsStableFaltingsHeight A x`, whose archimedean data is the kernel's coordinate form: the metric of
`η ∈ ⋀^g ω` at `τ` is `torusMetricSq Λ c = |c|² covol(Λ)`, read off an analytic uniformization
`Φ : ℂ^g → 𝒢(ℂ)_τ` with kernel `Λ` and `c = jacDet Φ f` (the coefficient of `Φ*η` on
`dz₁ ∧ ⋯ ∧ dz_g`).

This file restates both leaves over `IsPrintedStableHeight A x`, in which the metric at `τ` is
built as the print builds it: `‖η‖²_τ = (i/2)^g ∫_{A_τ(ℂ)} η ∧ η̄` for the invariant `g`-form `η`,
i.e. the total mass of the measure `(i/2)^g η ∧ η̄` on the compact group `A_τ(ℂ) = 𝒢(ℂ)_τ` with its
analytic topology (`HeightGlue.anTop`): a finite left-invariant Borel measure `μ` whose density at the
identity, in any algebraic local coordinates `f₁, …, f_g` (regular functions vanishing at `0`) with
`η = l · df₁ ∧ ⋯ ∧ df_g`, is `|τ(l)|²` with respect to Lebesgue measure `dx₁dy₁⋯dx_gdy_g`
(`IsFaltingsMetricSq`). No uniformization enters the definition.

It proves (`isFaltingsMetricSq_of_metrized`, from `TorusVolume.volume_eq_of_normalized`: Haar
uniqueness, the fundamental domain of `Λ`, and the Jacobian estimates of change of variables) that
every metrized model computes this printed metric, hence `IsStableFaltingsHeight A x →
IsPrintedStableHeight A x` (`isPrintedStableHeight_of`, using the kernel's uniqueness of analytic
uniformizations and `UniformizationDim`, both from T35), and the two consumer forms from the restated
leaves. -/

open CategoryTheory AlgebraicGeometry MeasureTheory Topology Set MonObj
open MonoidalCategory CartesianMonoidalCategory
open ZInQ.DefFaltings ZInQ.HeightSplit ZInQ.HeightGlue
open scoped NumberField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace ZInQ.HeightDict

section Defs

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- The Borel `σ`-algebra of the analytic topology of `𝒢(ℂ)_τ = A_τ(ℂ)`. -/
noncomputable def anBorel (𝒢 : GroupModel A L) (τ : L →+* ℂ) : MeasurableSpace (𝒢.Pts τ) :=
  @borel _ (anTop 𝒢 τ)

/-- The map `p ↦ (f₁(p), …, f_g(p))` of a tuple of regular functions `fᵢ ∈ Γ(Uᵢ, 𝒪_𝒢)`. -/
noncomputable def coordMap (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (U : Fin g → 𝒢.G.left.Opens) (s : ∀ i, Γ(𝒢.G.left, U i)) : 𝒢.Pts τ → (Fin g → ℂ) :=
  fun p i => 𝒢.evalAt p (U i) (s i)

/-- **`μ` is the measure `(i/2)^g η ∧ η̄` at the identity.** For every tuple of regular functions
`fᵢ ∈ Γ(Uᵢ, 𝒪_𝒢)` defined and vanishing at the origin `ξ` of the generic fibre, and every `l ∈ L`
with `η = l · df₁ ∧ ⋯ ∧ df_g`, the image of `μ` under `F = (f₁, …, f_g)` has density `|τ(l)|²` at
`F(1)` relative to Lebesgue measure on `ℂ^g` (`(i/2)^g dz ∧ dz̄ = dx dy`): near `1`,
`|μ(E) − |τ l|² λ(F(E))| ≤ ε λ(F(E))`. -/
def IsNormalizedBy (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (mu : @Measure (𝒢.Pts τ) (anBorel 𝒢 τ)) (eta : 𝒢.hodgeSpace g) : Prop :=
  letI := anTop 𝒢 τ
  letI := anBorel 𝒢 τ
  ∀ (U : Fin g → 𝒢.G.left.Opens) (hU : ∀ i, 𝒢.genericUnit ∈ U i) (s : ∀ i, Γ(𝒢.G.left, U i))
    (hm : ∀ i, 𝒢.G.left.presheaf.germ (U i) 𝒢.genericUnit (hU i) (s i) ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk)
    (l : L), eta = l • 𝒢.wedge (fun i => ⟨_, hm i⟩) →
    ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 (1 : 𝒢.Pts τ), ∀ E ⊆ W, MeasurableSet E →
      |(mu E).toReal - ‖τ l‖ ^ 2 * (volume (coordMap 𝒢 τ U s '' E)).toReal| ≤
        ε * (volume (coordMap 𝒢 τ U s '' E)).toReal

/-- **The printed archimedean Faltings metric** `‖η‖²_τ = (i/2)^g ∫_{A_τ(ℂ)} η ∧ η̄ = r`: every finite
left-invariant Borel measure on `A_τ(ℂ)` (analytic topology) that is `(i/2)^g η ∧ η̄` at the identity
has total mass `r`. -/
def IsFaltingsMetricSq (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} (eta : 𝒢.hodgeSpace g) (r : ℝ) :
    Prop :=
  letI := anTop 𝒢 τ
  letI := anBorel 𝒢 τ
  ∀ mu : Measure (𝒢.Pts τ), IsFiniteMeasure mu → mu.IsMulLeftInvariant → IsNormalizedBy 𝒢 τ mu eta →
    (mu univ).toReal = r

end Defs

/-- **Faltings' stable height, as the print builds it** (Faltings 1983 §1; Deligne, Sém. Bourbaki
616 §1; locators UNVERIFIED): `x = deg(ω̄_𝒩)/[L:ℚ]` for the Néron model `𝒩` of `A_L` over a number
field `L ⊇ K` where `A` has semistable reduction everywhere, `g = dim A`, `ω_𝒩 = ⋀^g e*Ω¹` (the
kernel's `detLattice g`), computed with any nonzero section `η`:
`deg = log #(ω_𝒩/𝓞_L η) − ½ ∑_{τ : L → ℂ} log ‖η‖²_τ` with the printed metric
`‖η‖²_τ = (i/2)^g ∫_{A_τ(ℂ)} η ∧ η̄` (`IsFaltingsMetricSq`). -/
def IsPrintedStableHeight {K : Type} [Field K] (A : PkgI3.AbVar K) (x : ℝ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (𝒩 : GroupModel A L) (g : ℕ),
    𝒩.IsNeronModel ∧ IsSemistable 𝒩 ∧ A.dim = (g : WithBot ℕ∞) ∧
    ∃ eta ∈ 𝒩.detLattice g, eta ≠ 0 ∧ secIndex (𝒩.detLattice g) eta ≠ 0 ∧
      ∃ r : (L →+* ℂ) → ℝ, (∀ τ, IsFaltingsMetricSq 𝒩 τ eta (r τ)) ∧
        x = (Real.log (secIndex (𝒩.detLattice g) eta) -
          (1 / 2) * ∑ τ : L →+* ℂ, Real.log (r τ)) / Module.finrank ℚ L

/-- **Leaf R21-Bost over the printed height** (J.-B. Bost, Sém. Bourbaki 795 (1994/95), Astérisque
237 (1996); display UNVERIFIED): `ZInQ.HeightSplit.BostLowerBound` with `IsStableFaltingsHeight`
replaced by `IsPrintedStableHeight` (Deligne's normalization `h_D = h_F + (g/2) log π`). -/
def BostLowerBoundPrinted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, IsPrintedStableHeight A x →
      -((g : ℝ) / 2 * Real.log (2 * Real.pi)) ≤ x + (g : ℝ) / 2 * Real.log Real.pi

/-- **Leaf R19-GR over the printed height** (Gaudron–Rémond, Duke Math. J. 163 (2014), Thm 1.4,
p. 2060; `κ` p. 2058; read by the locator audit): `ZInQ.HeightSplit.GaudronRemondThm14` with
`IsStableFaltingsHeight` replaced by `IsPrintedStableHeight` (stable height, Faltings' original
normalization). -/
def GaudronRemondThm14Printed : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (g : ℕ) (x : ℝ),
    A.dim = (g : WithBot ℕ∞) → IsPrintedStableHeight A x →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ) →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ ∧ (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogeny ψ ∧ (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x)


/-! ## The dictionary: a metrized model computes the printed metric -/

section Dict

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- **The archimedean dictionary.** For a metrized model `M` (analytic uniformization `Φ` with kernel
`Λ_τ`, coefficient map `c_τ`), the kernel's metric `torusMetricSq Λ_τ (c_τ η) = |c_τ η|² covol(Λ_τ)`
is the printed metric `(i/2)^g ∫_{A_τ(ℂ)} η ∧ η̄`. -/
theorem isFaltingsMetricSq_of_metrized {g : ℕ} (M : MetrizedModel A L g) (τ : L →+* ℂ)
    (eta : M.model.hodgeSpace g) :
    IsFaltingsMetricSq M.model τ eta
      (torusMetricSq (M.hodge.periods τ) (M.hodge.coeff τ eta)) := by
  obtain ⟨Φ, hΦ, hc⟩ := M.arch τ
  letI := anTop M.model τ
  letI := anBorel M.model τ
  haveI : BorelSpace (M.model.Pts τ) := ⟨rfl⟩
  haveI : T2Space (M.model.Pts τ) := analyticPointsT2 K A L M.model τ
  haveI := M.hodge.periods_discrete τ
  haveI := M.hodge.periods_isZLattice τ
  intro mu hfin hinv hnorm
  -- a wedge `1 ⊗ df₁ ∧ ⋯ ∧ df_g ≠ 0`
  have hw : ∃ f : Fin g → IsLocalRing.maximalIdeal M.model.genStalk, M.model.wedge f ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply M.hodge.coeff_ne_zero τ
    refine GroupModel.semilinear_ext_wedge M.model _ _ fun f => ?_
    rw [hcon f, map_zero, LinearMap.zero_apply]
  obtain ⟨f, hf⟩ := hw
  obtain ⟨l, hl⟩ := (finrank_eq_one_iff_of_nonzero' _ hf).mp M.hodge.finrank_eq_one eta
  -- representatives of the germs `fᵢ` (the ones `germAlong` uses)
  let U : Fin g → M.model.G.left.Opens := fun i => (M.model.exists_rep (f i)).choose
  have hU : ∀ i, M.model.genericUnit ∈ U i := fun i =>
    (M.model.exists_rep (f i)).choose_spec.choose
  let s : ∀ i, Γ(M.model.G.left, U i) := fun i =>
    (M.model.exists_rep (f i)).choose_spec.choose_spec.choose
  have hgerm : ∀ i, M.model.G.left.presheaf.germ (U i) M.model.genericUnit (hU i) (s i) =
      (f i : M.model.genStalk) := fun i =>
    (M.model.exists_rep (f i)).choose_spec.choose_spec.choose_spec
  have hm : ∀ i, M.model.G.left.presheaf.germ (U i) M.model.genericUnit (hU i) (s i) ∈
      IsLocalRing.maximalIdeal M.model.genStalk := fun i => by rw [hgerm]; exact (f i).2
  have hwf : M.model.wedge (fun i => ⟨_, hm i⟩) = M.model.wedge f := by
    congr 1; funext i; exact Subtype.ext (hgerm i)
  have hnormal := hnorm U hU s hm l (by rw [hwf, hl])
  -- `F ∘ Φ` is holomorphic near `0`
  set F := coordMap M.model τ U s
  have hψ : F ∘ Φ = fun z i => M.model.germAlong Φ (f i) z := rfl
  set V := ⋂ i, M.model.dom Φ (U i)
  have hVo : IsOpen V := isOpen_iInter_of_finite fun i => hΦ.2.2.2.1 (U i)
  have h0V : (0 : Fin g → ℂ) ∈ V :=
    mem_iInter.mpr fun i => ZInQ.Metrization.zero_mem_dom M.model hΦ (U i) (hU i)
  have hdi : ∀ i, DifferentiableOn ℂ (fun z => M.model.germAlong Φ (f i) z) V := fun i =>
    (hΦ.2.2.2.2 (U i) (s i)).mono (iInter_subset _ i)
  have hψd : DifferentiableOn ℂ (F ∘ Φ) V := by
    rw [hψ]; exact differentiableOn_pi.mpr hdi
  have hstrict := (Holomorphic.hasStrictFDerivAt hVo hψd h0V).restrictScalars ℝ
  have hUnif : TorusVolume.IsUnif (M.hodge.periods τ) Φ :=
    ⟨continuous_of_isAnalyticUniformization M.model τ hΦ, hΦ.1, hΦ.2.1, hΦ.2.2.1⟩
  have key := TorusVolume.volume_eq_of_normalized hUnif mu F (fderiv ℂ (F ∘ Φ) 0) hstrict
    (‖τ l‖ ^ 2) hnormal
  rw [key]
  -- the determinant is `jacDet Φ f`
  have hdet : LinearMap.det ((fderiv ℂ (F ∘ Φ) 0 : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) :
      (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) = M.model.jacDet Φ f := by
    rw [← LinearMap.det_toMatrix', GroupModel.jacDet]
    congr 1
    ext i j
    rw [LinearMap.toMatrix'_apply, hψ,
      fderiv_pi fun i => (hdi i).differentiableAt (hVo.mem_nhds h0V)]
    rfl
  have hcoeff : M.hodge.coeff τ eta = τ l * M.model.jacDet Φ f := by
    rw [← hl, map_smulₛₗ, hc f, smul_eq_mul]
  rw [torusMetricSq, hcoeff, hdet, norm_mul, mul_pow]

end Dict

/-! ## The identification and the consumer forms -/

/-- **`IsStableFaltingsHeight A x → IsPrintedStableHeight A x`**: the kernel's stable height is the
printed one. Uses the kernel's uniqueness of analytic uniformizations (so that the height of `𝒩` is
the model height of any metrization) and `UniformizationDim` (so that `g = dim A`); both follow
from T35 (`HeightGlue.analyticUniformizationUnique_of_t35`, `HeightGlue.uniformizationDim_of_t35`). -/
theorem isPrintedStableHeight_of (hU : AnalyticUniformizationUnique) (hDim : UniformizationDim)
    {K : Type} [Field K] {A : PkgI3.AbVar K} {x : ℝ} (hx : IsStableFaltingsHeight A x) :
    IsPrintedStableHeight A x := by
  obtain ⟨L, iF, iN, iA, 𝒩, hN, hS, hh⟩ := hx
  have hM : ∃ (g : ℕ) (M : MetrizedModel A L g), M.model = 𝒩 := by
    by_contra hcon
    push Not at hcon
    have htop : 𝒩.height = ⊤ :=
      le_antisymm le_top (le_iInf fun g => le_iInf fun M => le_iInf fun h => absurd h (hcon g M))
    rw [htop] at hh
    exact EReal.coe_ne_top x hh.symm
  obtain ⟨g, M, rfl⟩ := hM
  have hxM : x = M.hodge.modelHeight := by
    have := groupModel_height_eq hU metrizedDimUnique M
    rw [hh] at this
    exact_mod_cast this
  obtain ⟨τ₀⟩ : Nonempty (L →+* ℂ) := ⟨(IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom⟩
  obtain ⟨Φ₀, hΦ₀, -⟩ := M.arch τ₀
  have hdim : A.dim = (g : WithBot ℕ∞) := hDim K A L M.model τ₀ g _ Φ₀
    (M.hodge.periods_discrete τ₀) (M.hodge.periods_isZLattice τ₀) hΦ₀
  obtain ⟨eta, hetaM, heta0, hsec⟩ := M.hodge.isLattice
  have hetaM' : eta ∈ M.model.detLattice g := M.lattice_eq ▸ hetaM
  have hsec' : secIndex (M.model.detLattice g) eta ≠ 0 := M.lattice_eq ▸ hsec
  refine ⟨L, iF, iN, iA, M.model, g, hN, hS, hdim, eta, hetaM', heta0, hsec',
    fun τ => torusMetricSq (M.hodge.periods τ) (M.hodge.coeff τ eta),
    fun τ => isFaltingsMetricSq_of_metrized M τ eta, ?_⟩
  rw [hxM, M.hodge.modelHeight_eq hetaM heta0, M.lattice_eq]

/-- **`BostLowerBound` from Bost's bound over the printed height**, given the kernel's uniqueness of
analytic uniformizations and `UniformizationDim`. -/
theorem bostLowerBound_of_printed' (hB : BostLowerBoundPrinted)
    (hU : AnalyticUniformizationUnique) (hDim : UniformizationDim) : BostLowerBound :=
  fun K _ _ A g hg x hx => hB K A g hg x (isPrintedStableHeight_of hU hDim hx)

/-- **`GaudronRemondThm14` from Gaudron–Rémond over the printed height**, given the kernel's
uniqueness of analytic uniformizations and `UniformizationDim`. -/
theorem gaudronRemondThm14_of_printed' (hGR : GaudronRemondThm14Printed)
    (hU : AnalyticUniformizationUnique) (hDim : UniformizationDim) : GaudronRemondThm14 :=
  fun K _ _ A B g x hg hx hiso => hGR K A B g x hg (isPrintedStableHeight_of hU hDim hx) hiso

/-- **The field `bostLowerBound`** from the printed leaf and the textbook fields
`uniformizationLeafAll`, `mumfordTorsionAlgClosed` (which give T35). -/
theorem bostLowerBound_of_printed (hB : BostLowerBoundPrinted)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : BostLowerBound :=
  bostLowerBound_of_printed' hB (analyticUniformizationUnique_of_t35 (AvSplit.Final.h38 hUL hMT))
    (uniformizationDim_of_t35 (AvSplit.Final.h38 hUL hMT))

/-- **The field `gaudronRemondThm14`** from the printed leaf and the textbook fields
`uniformizationLeafAll`, `mumfordTorsionAlgClosed`. -/
theorem gaudronRemondThm14_of_printed (hGR : GaudronRemondThm14Printed)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : GaudronRemondThm14 :=
  gaudronRemondThm14_of_printed' hGR
    (analyticUniformizationUnique_of_t35 (AvSplit.Final.h38 hUL hMT))
    (uniformizationDim_of_t35 (AvSplit.Final.h38 hUL hMT))

end ZInQ.HeightDict
