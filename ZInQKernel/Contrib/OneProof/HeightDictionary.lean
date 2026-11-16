import ZInQKernel.OneProof.H.TailZ4
import ZInQKernel.Contrib.OneProof.HeightDictionary.TorusVolume

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

end ZInQ.HeightDict
