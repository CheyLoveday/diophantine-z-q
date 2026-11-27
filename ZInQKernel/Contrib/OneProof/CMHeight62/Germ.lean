import ZInQKernel.Contrib.OneProof.CMHeight62.Periods
import ZInQKernel.Contrib.OneProof.CMHeight62.Eval
import ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.Linearity

/-! # cmheight62-p1, step 4 (evaluation bridge): the germ `t` of `−x/y` along a uniformization

`jacDet` differentiates the evaluation of a chosen representative (`exists_rep`) of the germ
`t = tG ∈ 𝒪_{𝒢,ξ}`. We show that near `0` this evaluation, times `y`, is `−x`, all evaluated at
the image point in `E(ℂ)_{σ|K}`:

1. in the generic fibre `𝒢_L`, the pull-back of the representative of `t` and the pull-back
   (through `gen : 𝒢_L ≅ E_L` and `E_L → E`) of a representative `r` of `t_E` have the same germ
   at the identity `ξ_L` (`originStalkEquiv_spec`), hence agree on an open `W ∋ ξ_L`;
2. a complex point `p` of `𝒢` factors as `gpt p : Spec ℂ → 𝒢_L` followed by the projection,
   and `χ p = gpt p ≫ gen`; so near `0` both values are values of the same section on `W`;
3. on `E`, `r · y = −x` on `V_E ∩ (E ∖ 0)` (injectivity into the function field). -/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.CMHeight62

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice IsLocalRing
open _root_.ZInQ.LeafPush2 (CPts cptObj cDom cEvalAt IsUniformization)
open HDec.CMBranch.CMjBridges
open ZInQ.Contrib.RC53Assist.HodgeLineBinding (originStalkEquiv originStalkEquiv_spec
  gen_genericFibreUnit_eq stalkMapAt)

attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra

/-- Identification of stalks at inseparable points sends germs to germs. -/
theorem stalkCongr_germ {X : Scheme.{0}} {x y : X} (h : Inseparable x y) (V : X.Opens)
    (hx : x ∈ V) (s : Γ(X, V)) :
    (X.presheaf.stalkCongr h).hom (X.presheaf.germ V x hx s) =
      X.presheaf.germ V y (h.mem_open_iff V.isOpen |>.mp hx) s := by
  have h1 := ConcreteCategory.congr_hom (TopCat.Presheaf.germ_stalkSpecializes X.presheaf
    (U := V) hx h.ge) s
  rw [ConcreteCategory.comp_apply] at h1
  exact h1

variable {K : Type} [Field K] {E : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

section GenericFibre

variable (𝒢 : GroupModel E L)

/-- The projection `𝒢_L → 𝒢`. -/
abbrev fstGF : (genericFibre L 𝒢.G).left ⟶ 𝒢.G.left := pullback.fst 𝒢.G.hom (toGeneric L)

/-- The composite `𝒢_L ≅ E_L → E`. -/
def genE : (genericFibre L 𝒢.G).left ⟶ E.X.left := 𝒢.gen.hom.left ≫ bcProj E L

theorem genE_unit : genE 𝒢 (genericFibreUnit 𝒢) = abVarIdentity E := by
  change bcProj E L (𝒢.gen.hom.left (genericFibreUnit 𝒢)) = _
  rw [gen_genericFibreUnit_eq]
  exact bcProj_identity E L

/-- **Germ comparison in the generic fibre.** If `s ∈ Γ(𝒢, U)` represents `t = tG` at `ξ` and
`r ∈ Γ(E, V)` represents `t_E` at the identity, their pull-backs to `𝒢_L` have the same germ at
`ξ_L`. -/
theorem germ_pullbacks_eq (D : ShortData E) {U : 𝒢.G.left.Opens} (hU : 𝒢.genericUnit ∈ U)
    (s : Γ(𝒢.G.left, U)) (hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit hU s = (D.tG 𝒢 : _))
    {V : E.X.left.Opens} (hV : abVarIdentity E ∈ V) (r : Γ(E.X.left, V))
    (hr : E.X.left.presheaf.germ V (abVarIdentity E) hV r = D.tE) :
    (genericFibre L 𝒢.G).left.presheaf.germ (fstGF 𝒢 ⁻¹ᵁ U) (genericFibreUnit 𝒢)
        (by show pullback.fst 𝒢.G.hom (toGeneric L) (genericFibreUnit 𝒢) ∈ U
            rw [fst_genericFibreUnit]; exact hU)
        ((fstGF 𝒢).app U s) =
      (genericFibre L 𝒢.G).left.presheaf.germ (genE 𝒢 ⁻¹ᵁ V) (genericFibreUnit 𝒢)
        (by change genE 𝒢 (genericFibreUnit 𝒢) ∈ V; rw [genE_unit]; exact hV)
        ((genE 𝒢).app V r) := by
  have hspec := originStalkEquiv_spec 𝒢 (D.tG 𝒢 : 𝒢.genStalk)
  have htG : originStalkEquiv 𝒢 (D.tG 𝒢 : 𝒢.genStalk) = ShortData.tL D := by
    change originStalkEquiv 𝒢 ((originStalkEquiv 𝒢).symm (ShortData.tL D)) = _
    exact RingEquiv.apply_symm_apply _ _
  rw [htG, ← hs] at hspec
  -- right side of `hspec`
  have hfu : fstGF 𝒢 (genericFibreUnit 𝒢) ∈ U := by
    show pullback.fst 𝒢.G.hom (toGeneric L) (genericFibreUnit 𝒢) ∈ U
    rw [fst_genericFibreUnit]; exact hU
  erw [stalkCongr_germ _ U hU s] at hspec
  erw [Scheme.Hom.germ_stalkMap_apply (fstGF 𝒢) U (genericFibreUnit 𝒢) hfu s] at hspec
  rw [← hspec]
  -- left side: `tL` is the germ of the pull-back of `r`
  have hbo : bcProj E L (abVarIdentity (E.baseChange L)) ∈ V := by
    rw [bcProj_identity]; exact hV
  have htL : ShortData.tL D = (E.baseChange L).X.left.presheaf.germ (bcProj E L ⁻¹ᵁ V)
      (abVarIdentity (E.baseChange L)) hbo ((bcProj E L).app V r) := by
    change (stalkMapAt (bcProj E L) (bcProj_identity E L)).hom D.tE = _
    rw [← hr]
    unfold stalkMapAt
    rw [CommRingCat.comp_apply]
    erw [stalkCongr_germ _ V hV r]
    exact Scheme.Hom.germ_stalkMap_apply (bcProj E L) V _ hbo r
  rw [htL]
  erw [stalkCongr_germ]
  erw [Scheme.Hom.germ_stalkMap_apply 𝒢.gen.hom.left (bcProj E L ⁻¹ᵁ V) (genericFibreUnit 𝒢)]
  rfl

end GenericFibre

end ZInQ.Contrib.CMHeight62
