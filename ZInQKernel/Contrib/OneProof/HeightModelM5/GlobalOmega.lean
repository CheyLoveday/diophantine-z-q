import ZInQKernel.Contrib.OneProof.HeightModelM3.StalkInjective
import ZInQKernel.Contrib.OneProof.HeightModelM5.GenericGerm

/-!
# The global sections of `e*Ω¹_{𝒢/𝓞_L}` are the tree's `globalOmega`

For a group model `𝒢` of `A` over `𝓞_L`, with structure map `f = 𝒢.G.hom` and unit section
`e = 𝒢.unitSection`, `pullOmega f e` is the sheaf `e*Ω¹_{𝒢/𝓞_L}` on `S = Spec 𝓞_L`, built from
Mathlib's sheafification of the presheaf of relative Kähler differentials and Mathlib's pullback
of sheaves of modules. `GlobalPullOmega 𝒢` is its module of global sections `Γ(S, e*Ω¹)`.

* `genericGermPullOmega`: the `𝓞_L`-linear map from `Γ(S, e*Ω¹)` to the generic fibre
  `𝒪_{S,η} ⊗ Ω[𝒪_{𝒢,ξ}⁄𝓞_L]`: the germ at the generic point `η`, followed by the stalk formulas
  for the pullback and for `Ω¹`.
* `genericGermPullOmega_injective`: it is injective.
* `range_genericGermPullOmega`: its image is the tree's `globalOmega 𝒢`.
* `printedOmega_eq_sheaf`: the tree's `printedOmega 𝒢` is the preimage under `θ` of the image of
  `Γ(S, e*Ω¹)`.

At each point `s`, the stalk of `e*Ω¹` is `𝒪_{S,s} ⊗ Ω[𝒪_{𝒢,e(s)}⁄𝓞_L]` and its map to the
generic fibre is the tree's `stalkToGeneric` (injective, with image `printedOmegaAt s`). The
general argument is in `GenericGerm.lean`; this file only instantiates it.
-/

open CategoryTheory AlgebraicGeometry Opposite
open NumberField KaehlerDifferential
open ZInQ.DefFaltings ZInQ.HeightDict ZInQ.HeightDict.Conormal
open scoped TensorProduct
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace ZInQ.HeightModelM5

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]
variable (𝒢 : GroupModel A L)

attribute [local instance] Conormal.algXi Conormal.algEta Conormal.algXiEta

/-- The global sections `Γ(S, e*Ω¹_{𝒢/𝓞_L})` of the pullback along the unit section of the
sheaf of relative differentials of `𝒢`. -/
abbrev GlobalPullOmega : Type := Γ(pullOmega 𝒢.G.hom 𝒢.unitSection, ⊤)

/-- `Γ(S, e*Ω¹)` is an `𝓞_L`-module through `𝓞_L ≅ Γ(S, 𝒪_S)`. -/
noncomputable instance : Module (𝓞 L) (GlobalPullOmega 𝒢) :=
  Module.compHom _ (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv.hom

/-- **The generic germ of the global sections of `e*Ω¹`**, in the tree's generic fibre
`𝒪_{S,η} ⊗ Ω[𝒪_{𝒢,ξ}⁄𝓞_L]`. -/
noncomputable def genericGermPullOmega :
    GlobalPullOmega 𝒢 →ₗ[𝓞 L] (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L] where
  toFun m := GG.genericGerm 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes m
  map_add' a b := map_add _ a b
  map_smul' a m := by
    change GG.genericGerm 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes
        ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv.hom a • m) =
      a • GG.genericGerm 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes m
    exact (GG.genericGerm_smul 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes _
      m).trans (algebraMap_smul (Reta L) a _)

theorem genericGermPullOmega_apply (m : GlobalPullOmega 𝒢) :
    genericGermPullOmega 𝒢 m =
      GG.genericGerm 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes m := rfl

/-- The stalk maps of `e*Ω¹` to the generic fibre are the tree's injective `stalkToGeneric`. -/
theorem stalkToGeneric_injective_sheaf (s : Spec (CommRingCat.of (𝓞 L))) :
    Function.Injective
      (GG.stalkToGeneric 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes s) :=
  HeightModelM3.stalkToGeneric_injective 𝒢 s

/-- **The generic germ of `Γ(S, e*Ω¹)` is injective.** -/
theorem genericGermPullOmega_injective : Function.Injective (genericGermPullOmega 𝒢) :=
  GG.genericGerm_injective 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes
    (stalkToGeneric_injective_sheaf 𝒢)

/-- **The image of `Γ(S, e*Ω¹)` in the generic fibre is the tree's `globalOmega`.** -/
theorem range_genericGermPullOmega :
    LinearMap.range (genericGermPullOmega 𝒢) = HeightModelM2.globalOmega 𝒢 := by
  have hR := GG.range_genericGerm 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes
    (stalkToGeneric_injective_sheaf 𝒢)
  ext v
  rw [HeightModelM2.globalOmega_eq, Submodule.mem_iInf, LinearMap.mem_range]
  constructor
  · rintro ⟨m, rfl⟩ s
    have hv : genericGermPullOmega 𝒢 m ∈ Set.range
        (GG.genericGerm 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes) := ⟨m, rfl⟩
    rw [hR, Set.mem_iInter] at hv
    have h2 : genericGermPullOmega 𝒢 m ∈ Set.range (HeightModelM3.stalkToGeneric 𝒢 s) := hv s
    rw [HeightModelM3.range_stalkToGeneric] at h2
    exact h2
  · intro hv
    have h1 : v ∈ ⋂ s, Set.range
        (GG.stalkToGeneric 𝒢.G.hom 𝒢.unitSection HeightModelM2.genericPt_specializes s) :=
      Set.mem_iInter.2 fun s => by
        have h2 : v ∈ (printedOmegaAt 𝒢 s : Set ((Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L])) :=
          hv s
        rw [← HeightModelM3.range_stalkToGeneric] at h2
        exact h2
    rw [← hR] at h1
    obtain ⟨m, hm⟩ := h1
    exact ⟨m, hm⟩

/-- **The tree's `ω` from the sheaf**: `printedOmega 𝒢` is the preimage under `θ` of the image of
`Γ(S, e*Ω¹)` in the generic fibre. -/
theorem printedOmega_eq_sheaf :
    printedOmega 𝒢 = (LinearMap.range (genericGermPullOmega 𝒢)).comap (theta' 𝒢) := by
  rw [range_genericGermPullOmega]
  exact HeightModelM2.printedOmega_eq_comap_globalOmega 𝒢

end ZInQ.HeightModelM5
