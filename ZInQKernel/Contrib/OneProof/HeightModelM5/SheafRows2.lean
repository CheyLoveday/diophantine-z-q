import ZInQKernel.Contrib.OneProof.HeightModelM5.SheafRows
import ZInQKernel.Contrib.OneProof.HeightModelM5.PullbackWedge

/-!
# The GR1 rows over `ε*Ω^g`, the pullback of the top exterior power

Gaudron–Rémond take the lattice `M = Γ(Spec 𝓞_{K'}, ε*Ω^g)` with `Ω^g` the top exterior power of
`Ω¹_{𝒜/𝓞_{K'}}` and `ε*` the pullback along the unit section. `SheafRows.lean` used the sheaf
`⋀^g ε*Ω¹` instead. Here `M` is taken literally: `GlobalPullTopOmega 𝒢 g` is the module of global
sections of `ε^*(⋀^g Ω¹)`, the pullback of `schemeWedge (relOmega f) g`.

* `globalPullTopEquiv`: the `𝓞_{K'}`-linear isomorphism `Γ(S, ε^*(⋀^g Ω¹)) ≃ Γ(S, ⋀^g ε^*Ω¹)`
  given by the natural morphism `ε^*(⋀^g Ω¹) ⟶ ⋀^g ε^*Ω¹` of `PullbackWedge.lean`, an isomorphism
  on stalks (`PW.wedgePullMap_stalk_bijective`) and on global sections.
* `genericGermPullTopOmega`: the generic germ of `M` in the tree's Hodge line, through that
  isomorphism; `printedDetLattice_eq_pullTop`: it is injective with image `printedDetLattice`.
* `isGR1StableHeightSheaf'_iff`: the height over `M` is the tree's `IsGR1StableHeightOriginal`;
  `gaudronRemondThm14GR1Sheaf'_iff`, `gaudronRemondSec9LowerGR1WeakSheaf'_iff`: the rows over the
  new predicate are the bundle's rows.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Topology MonObj
open ZInQ.DefFaltings ZInQ.HeightSplit ZInQ.HeightGlue ZInQ.HeightDict ZInQ.HeightFix
open ZInQ.R3Residual ZInQ.H5Glue ZInQ.SemistabAssembly CToPrinted ZInQ.GR14Printed
open ZInQ.HeightModelM
open scoped NumberField

namespace ZInQ.HeightModelM5

section Lattice

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- **The global sections `Γ(S, ε^*(⋀^g Ω¹))` of the pullback of the top exterior power.** -/
abbrev GlobalPullTopOmega (g : ℕ) : Type :=
  Γ(GG.pullTopOmega 𝒢.G.hom 𝒢.unitSection g, ⊤)

/-- `GlobalPullTopOmega` is literally the module of global sections of the pullback along the unit
section of `⋀^g Ω¹_{𝒢/𝓞_L}`. -/
theorem globalPullTopOmega_eq (g : ℕ) :
    GlobalPullTopOmega 𝒢 g =
      Γ((Scheme.Modules.pullback 𝒢.unitSection).obj (schemeWedge (relOmegaPre 𝒢.G.hom) g), ⊤) :=
  rfl

/-- `Γ(S, ε^*(⋀^g Ω¹))` is an `𝓞_L`-module through `𝓞_L ≅ Γ(S, 𝒪_S)`. -/
noncomputable instance (g : ℕ) : Module (𝓞 L) (GlobalPullTopOmega 𝒢 g) :=
  Module.compHom _ (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv.hom

/-- **`Γ(S, ε^*(⋀^g Ω¹)) ≃ Γ(S, ⋀^g ε^*Ω¹)`**, linear over `𝓞_L`. -/
noncomputable def globalPullTopEquiv (g : ℕ) :
    GlobalPullTopOmega 𝒢 g ≃ₗ[𝓞 L] GlobalPullOmegaTop 𝒢 g :=
  { (GG.globalPullWedgeEquiv 𝒢.G.hom 𝒢.unitSection g) with
    map_smul' := fun a m => (GG.globalPullWedgeEquiv 𝒢.G.hom 𝒢.unitSection g).map_smul
      ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv.hom a) m }

theorem globalPullTopEquiv_apply (g : ℕ) (m : GlobalPullTopOmega 𝒢 g) :
    globalPullTopEquiv 𝒢 g m = GG.globalPullWedgeEquiv 𝒢.G.hom 𝒢.unitSection g m :=
  rfl

/-- **The generic germ of `Γ(S, ε^*(⋀^g Ω¹))`** in the tree's Hodge line. -/
noncomputable def genericGermPullTopOmega (g : ℕ) :
    GlobalPullTopOmega 𝒢 g →ₗ[𝓞 L] 𝒢.hodgeSpace g :=
  (genericGermPullOmegaTop 𝒢 g).comp (globalPullTopEquiv 𝒢 g).toLinearMap

theorem genericGermPullTopOmega_apply (g : ℕ) (m : GlobalPullTopOmega 𝒢 g) :
    genericGermPullTopOmega 𝒢 g m = genericGermPullOmegaTop 𝒢 g (globalPullTopEquiv 𝒢 g m) :=
  rfl

/-- **The global sections of `ε^*(⋀^g Ω¹)` are the tree's lattice**: the generic germ is injective
with image `printedDetLattice 𝒢 g`. -/
theorem printedDetLattice_eq_pullTop (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) :
    Function.Injective (genericGermPullTopOmega 𝒢 g) ∧
      LinearMap.range (genericGermPullTopOmega 𝒢 g) = printedDetLattice 𝒢 g :=
  ⟨(printedDetLattice_eq_sheaf 𝒢 g hg).1.comp (globalPullTopEquiv 𝒢 g).injective,
    (LinearMap.range_comp_of_range_eq_top _ (globalPullTopEquiv 𝒢 g).range).trans
      (printedDetLattice_eq_sheaf 𝒢 g hg).2⟩

/-- **The index of a section is preserved**: for `η ∈ M = Γ(S, ε^*(⋀^g Ω¹))`, the tree's index of
its image in `printedDetLattice` is `[M : 𝓞η]`. -/
theorem secIndex_genericGermPullTopOmega (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞))
    (eta : GlobalPullTopOmega 𝒢 g) :
    secIndex (printedDetLattice 𝒢 g) (genericGermPullTopOmega 𝒢 g eta) =
      (Submodule.span (𝓞 L) {eta}).toAddSubgroup.index :=
  (secIndex_genericGermPullOmegaTop 𝒢 g hg (globalPullTopEquiv 𝒢 g eta)).trans
    (index_span_map_equiv (globalPullTopEquiv 𝒢 g) eta)

end Lattice

/-- **Gaudron–Rémond's stable height over `ε*Ω^g`, taken literally** (GR1 §2.3, p. 351):
`x = h_F(A)` computed on a semi-abelian group model `𝒜` of `A` over the ring of integers of a
number field `K'` over the base, with a nonzero element `η` of `M = Γ(Spec 𝓞_{K'}, ε^*(⋀^g Ω¹))`,
the global sections of the pullback along the unit section of the top exterior power of
`Ω¹_{𝒜/𝓞_{K'}}`, with `[M : 𝓞η]` finite, and the metrics of its image in the Hodge line. -/
def IsGR1StableHeightSheaf' {K : Type} [Field K] (A : PkgI3.AbVar K) (x : ℝ) : Prop :=
  ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (𝒜 : GroupModel A K')
    (g : ℕ), IsSemiAbelianModel 𝒜 ∧ A.dim = (g : WithBot ℕ∞) ∧
    ∃ eta : GlobalPullTopOmega 𝒜 g, eta ≠ 0 ∧
      (Submodule.span (𝓞 K') {eta}).toAddSubgroup.index ≠ 0 ∧
      ∃ r : (K' →+* ℂ) → ℝ, (∀ τ, IsAnMetricSq 𝒜 τ (genericGermPullTopOmega 𝒜 g eta) (r τ)) ∧
        x = (Real.log ((Submodule.span (𝓞 K') {eta}).toAddSubgroup.index) -
          (1 / 2) * ∑ τ : K' →+* ℂ, Real.log (r τ)) / Module.finrank ℚ K'

/-- The height over `ε^*(⋀^g Ω¹)` is the height over `⋀^g ε^*Ω¹`. -/
theorem isGR1StableHeightSheaf'_iff_sheaf {K : Type} [Field K] {A : PkgI3.AbVar K} {x : ℝ} :
    IsGR1StableHeightSheaf' A x ↔ IsGR1StableHeightSheaf A x := by
  constructor
  · rintro ⟨K', iF, iN, iA, 𝒜, g, hsa, hg, h⟩
    exact ⟨K', iF, iN, iA, 𝒜, g, hsa, hg,
      (exists_span_index_iff_of_equiv (globalPullTopEquiv 𝒜 g) (genericGermPullOmegaTop 𝒜 g)
        (fun v k => ∃ r : (K' →+* ℂ) → ℝ, (∀ τ, IsAnMetricSq 𝒜 τ v (r τ)) ∧
          x = (Real.log k - (1 / 2) * ∑ τ : K' →+* ℂ, Real.log (r τ)) /
            Module.finrank ℚ K')).1 h⟩
  · rintro ⟨K', iF, iN, iA, 𝒜, g, hsa, hg, h⟩
    exact ⟨K', iF, iN, iA, 𝒜, g, hsa, hg,
      (exists_span_index_iff_of_equiv (globalPullTopEquiv 𝒜 g) (genericGermPullOmegaTop 𝒜 g)
        (fun v k => ∃ r : (K' →+* ℂ) → ℝ, (∀ τ, IsAnMetricSq 𝒜 τ v (r τ)) ∧
          x = (Real.log k - (1 / 2) * ∑ τ : K' →+* ℂ, Real.log (r τ)) /
            Module.finrank ℚ K')).2 h⟩

/-- **The height over `ε*Ω^g`, taken literally, is the tree's predicate.** -/
theorem isGR1StableHeightSheaf'_iff {K : Type} [Field K] {A : PkgI3.AbVar K} {x : ℝ} :
    IsGR1StableHeightSheaf' A x ↔ IsGR1StableHeightOriginal A x :=
  isGR1StableHeightSheaf'_iff_sheaf.trans isGR1StableHeightSheaf_iff

/-- `GaudronRemondThm14GR1` over `IsGR1StableHeightSheaf'`. -/
def GaudronRemondThm14GR1Sheaf' : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (g : ℕ) (x : ℝ), 1 ≤ g →
    A.dim = (g : WithBot ℕ∞) → IsGR1StableHeightSheaf' A x →
    (∃ φ : A.X ⟶ B.X, IsIsogenyPrinted φ) →
    (∃ φ : A.X ⟶ B.X, IsIsogenyPrinted φ ∧
      (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogenyPrinted ψ ∧
      (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x)

/-- **The Thm 1.4 row over `ε*Ω^g` is the bundle's row.** -/
theorem gaudronRemondThm14GR1Sheaf'_iff : GaudronRemondThm14GR1Sheaf' ↔ GaudronRemondThm14GR1 :=
  ⟨fun h K _ _ A B g x hg1 hg hx hiso =>
      h K A B g x hg1 hg (isGR1StableHeightSheaf'_iff.mpr hx) hiso,
    fun h K _ _ A B g x hg1 hg hx hiso =>
      h K A B g x hg1 hg (isGR1StableHeightSheaf'_iff.mp hx) hiso⟩

/-- The field `gaudronRemondThm14GR1` from its statement over `IsGR1StableHeightSheaf'`. -/
theorem gaudronRemondThm14GR1_of_sheaf' (h : GaudronRemondThm14GR1Sheaf') :
    GaudronRemondThm14GR1 :=
  gaudronRemondThm14GR1Sheaf'_iff.mp h

/-- `GaudronRemondSec9LowerGR1Weak` over `IsGR1StableHeightSheaf'`. -/
def GaudronRemondSec9LowerGR1WeakSheaf' : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, IsGR1StableHeightSheaf' A x → -(3 / 2) * (g : ℝ) ≤ x

/-- **The weak Cor. 8.4 row over `ε*Ω^g` is the bundle's row.** -/
theorem gaudronRemondSec9LowerGR1WeakSheaf'_iff :
    GaudronRemondSec9LowerGR1WeakSheaf' ↔ GaudronRemondSec9LowerGR1Weak :=
  ⟨fun h K _ _ A g hg x hx => h K A g hg x (isGR1StableHeightSheaf'_iff.mpr hx),
    fun h K _ _ A g hg x hx => h K A g hg x (isGR1StableHeightSheaf'_iff.mp hx)⟩

/-- The field `gaudronRemondSec9LowerGR1Weak` from its statement over
`IsGR1StableHeightSheaf'`. -/
theorem gaudronRemondSec9LowerGR1Weak_of_sheaf' (h : GaudronRemondSec9LowerGR1WeakSheaf') :
    GaudronRemondSec9LowerGR1Weak :=
  gaudronRemondSec9LowerGR1WeakSheaf'_iff.mp h

end ZInQ.HeightModelM5
