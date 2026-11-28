import ZInQKernel.Contrib.OneProof.HeightModelM2.GR1Rows
import ZInQKernel.Contrib.OneProof.HeightModelM5.DetLattice

/-!
# The GR1 rows over the sheaf `ε*Ω^g`

`IsGR1StableHeightSheaf A x` is `IsGR1StableHeightOriginal A x` with the lattice taken to be the
module `M = Γ(Spec 𝓞_{K'}, ε*Ω^g)` of global sections of the sheaf `⋀^g e*Ω¹_{𝒜/𝓞_{K'}}`
(`GlobalPullOmegaTop`, built from Mathlib's sheaf of modules): a section `η ∈ M`, `η ≠ 0`, with
`[M : 𝓞η] ≠ 0`, the metrics of its image `genericGermPullOmegaTop η` in the Hodge line, and the
same formula for `x`.

* `isGR1StableHeightSheaf_iff`: the two predicates are equivalent, since the generic germ is
  injective with image `printedDetLattice` (`printedDetLattice_eq_sheaf`) and so carries the
  index `[M : 𝓞η]` to the tree's `secIndex` (`secIndex_genericGermPullOmegaTop`).
* `gaudronRemondThm14GR1Sheaf_iff`, `gaudronRemondSec9LowerGR1WeakSheaf_iff`: the rows over the
  new predicate are the bundle's rows; `gaudronRemondThm14GR1_of_sheaf` and
  `gaudronRemondSec9LowerGR1Weak_of_sheaf` restate one direction.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Topology MonObj
open ZInQ.DefFaltings ZInQ.HeightSplit ZInQ.HeightGlue ZInQ.HeightDict ZInQ.HeightFix
open ZInQ.R3Residual ZInQ.H5Glue ZInQ.SemistabAssembly CToPrinted ZInQ.GR14Printed
open ZInQ.HeightModelM
open scoped NumberField

namespace ZInQ.HeightModelM5

/-- **The index of a section is preserved**: for `η ∈ M = Γ(S, ε*Ω^g)`, the tree's index of the
image of `η` in `printedDetLattice` is `[M : 𝓞η]`. -/
theorem secIndex_genericGermPullOmegaTop {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type}
    [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L) (g : ℕ)
    (hg : A.dim = (g : WithBot ℕ∞)) (eta : GlobalPullOmegaTop 𝒢 g) :
    secIndex (printedDetLattice 𝒢 g) (genericGermPullOmegaTop 𝒢 g eta) =
      (Submodule.span (𝓞 L) {eta}).toAddSubgroup.index := by
  rw [← (printedDetLattice_eq_sheaf 𝒢 g hg).2]
  show (Submodule.span (𝓞 L) {genericGermPullOmegaTop 𝒢 g eta}).toAddSubgroup.relIndex
      (LinearMap.range (genericGermPullOmegaTop 𝒢 g)).toAddSubgroup = _
  exact GG.relIndex_span_range _ (genericGermPullOmegaTop_injective 𝒢 g) eta

/-- **Gaudron–Rémond's stable height over the sheaf `ε*Ω^g`** (GR1 §2.3, p. 351): `x = h_F(A)`
computed on a semi-abelian group model `𝒜` of `A` over the ring of integers of a number field `K'`
over the base, with a nonzero global section `η` of `ε*Ω^g_{𝒜/𝒪_{K'}}` (an element of the module
`M = Γ(Spec 𝓞_{K'}, ε*Ω^g)` of global sections of the sheaf) with `[M : 𝓞η]` finite, and the
metrics of its image in the Hodge line. -/
def IsGR1StableHeightSheaf {K : Type} [Field K] (A : PkgI3.AbVar K) (x : ℝ) : Prop :=
  ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (𝒜 : GroupModel A K')
    (g : ℕ), IsSemiAbelianModel 𝒜 ∧ A.dim = (g : WithBot ℕ∞) ∧
    ∃ eta : GlobalPullOmegaTop 𝒜 g, eta ≠ 0 ∧
      (Submodule.span (𝓞 K') {eta}).toAddSubgroup.index ≠ 0 ∧
      ∃ r : (K' →+* ℂ) → ℝ, (∀ τ, IsAnMetricSq 𝒜 τ (genericGermPullOmegaTop 𝒜 g eta) (r τ)) ∧
        x = (Real.log ((Submodule.span (𝓞 K') {eta}).toAddSubgroup.index) -
          (1 / 2) * ∑ τ : K' →+* ℂ, Real.log (r τ)) / Module.finrank ℚ K'

/-- **The height over the sheaf is the tree's predicate.** -/
theorem isGR1StableHeightSheaf_iff {K : Type} [Field K] {A : PkgI3.AbVar K} {x : ℝ} :
    IsGR1StableHeightSheaf A x ↔ IsGR1StableHeightOriginal A x := by
  constructor
  · rintro ⟨K', iF, iN, iA, 𝒜, g, hsa, hg, eta, hne, hsec, r, hr, hx⟩
    have hP := printedDetLattice_eq_sheaf 𝒜 g hg
    have hi := secIndex_genericGermPullOmegaTop 𝒜 g hg eta
    refine ⟨K', iF, iN, iA, 𝒜, g, hsa, hg, genericGermPullOmegaTop 𝒜 g eta, ?_, ?_, ?_, r, hr,
      ?_⟩
    · rw [← hP.2]; exact LinearMap.mem_range_self _ eta
    · exact fun h => hne (hP.1 (h.trans (map_zero _).symm))
    · rw [hi]; exact hsec
    · rw [hi]; exact hx
  · rintro ⟨K', iF, iN, iA, 𝒜, g, hsa, hg, eta, heta, hne, hsec, r, hr, hx⟩
    have hP := printedDetLattice_eq_sheaf 𝒜 g hg
    rw [← hP.2] at heta
    obtain ⟨m, rfl⟩ := LinearMap.mem_range.1 heta
    have hi := secIndex_genericGermPullOmegaTop 𝒜 g hg m
    refine ⟨K', iF, iN, iA, 𝒜, g, hsa, hg, m, fun h => hne (by rw [h, map_zero]), ?_, r, hr, ?_⟩
    · rw [← hi]; exact hsec
    · rw [← hi]; exact hx

/-- `GaudronRemondThm14GR1` over `IsGR1StableHeightSheaf`. -/
def GaudronRemondThm14GR1Sheaf : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (g : ℕ) (x : ℝ), 1 ≤ g →
    A.dim = (g : WithBot ℕ∞) → IsGR1StableHeightSheaf A x →
    (∃ φ : A.X ⟶ B.X, IsIsogenyPrinted φ) →
    (∃ φ : A.X ⟶ B.X, IsIsogenyPrinted φ ∧
      (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogenyPrinted ψ ∧
      (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x)

/-- **The Thm 1.4 row over the sheaf is the bundle's row.** -/
theorem gaudronRemondThm14GR1Sheaf_iff : GaudronRemondThm14GR1Sheaf ↔ GaudronRemondThm14GR1 :=
  ⟨fun h K _ _ A B g x hg1 hg hx hiso =>
      h K A B g x hg1 hg (isGR1StableHeightSheaf_iff.mpr hx) hiso,
    fun h K _ _ A B g x hg1 hg hx hiso =>
      h K A B g x hg1 hg (isGR1StableHeightSheaf_iff.mp hx) hiso⟩

/-- The field `gaudronRemondThm14GR1` from its statement over `IsGR1StableHeightSheaf`. -/
theorem gaudronRemondThm14GR1_of_sheaf (h : GaudronRemondThm14GR1Sheaf) :
    GaudronRemondThm14GR1 :=
  gaudronRemondThm14GR1Sheaf_iff.mp h

/-- `GaudronRemondSec9LowerGR1Weak` over `IsGR1StableHeightSheaf`. -/
def GaudronRemondSec9LowerGR1WeakSheaf : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, IsGR1StableHeightSheaf A x → -(3 / 2) * (g : ℝ) ≤ x

/-- **The weak Cor. 8.4 row over the sheaf is the bundle's row.** -/
theorem gaudronRemondSec9LowerGR1WeakSheaf_iff :
    GaudronRemondSec9LowerGR1WeakSheaf ↔ GaudronRemondSec9LowerGR1Weak :=
  ⟨fun h K _ _ A g hg x hx => h K A g hg x (isGR1StableHeightSheaf_iff.mpr hx),
    fun h K _ _ A g hg x hx => h K A g hg x (isGR1StableHeightSheaf_iff.mp hx)⟩

/-- The field `gaudronRemondSec9LowerGR1Weak` from its statement over
`IsGR1StableHeightSheaf`. -/
theorem gaudronRemondSec9LowerGR1Weak_of_sheaf (h : GaudronRemondSec9LowerGR1WeakSheaf) :
    GaudronRemondSec9LowerGR1Weak :=
  gaudronRemondSec9LowerGR1WeakSheaf_iff.mp h

end ZInQ.HeightModelM5
