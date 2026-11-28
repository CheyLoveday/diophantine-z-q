import ZInQKernel.Contrib.OneProof.HeightModelM5.GenericGermTop

/-!
# The pullback of an exterior power is the exterior power of the pullback

Let `e : S ⟶ X` be a morphism of schemes, `M` a sheaf of modules on `X` and `n : ℕ`. With
`⋀^n = schemeWedge` and `e^* = Scheme.Modules.pullback e`, this file builds the natural morphism

  `wedgePullMap e M n : e^*(⋀^n M) ⟶ ⋀^n (e^* M)`

and proves that it is an isomorphism on stalks and on sections over every open.

* `wedgePullMap` is the adjoint, for `e^* ⊣ e_*`, of a morphism `⋀^n M ⟶ e_* ⋀^n (e^* M)`, itself
  the adjoint, for sheafification, of `⋀^n` of the unit `M(U) → (e^* M)(e⁻¹ U)` followed by the
  canonical map from the exterior power presheaf to its sheafification.
* `pullWedgeStalkMap s`: the composite of the stalk formulas
  `(e^*(⋀^n M))_s ≃ 𝒪_{S,s} ⊗ (⋀^n M)_{e(s)} ≃ 𝒪_{S,s} ⊗ ⋀^n M_{e(s)}
    ≃ ⋀^n (𝒪_{S,s} ⊗ M_{e(s)}) ≃ ⋀^n (e^* M)_s`; it is bijective.
* `wedgeStalkEquiv_germ_wedgePullMap`: on stalks, `wedgePullMap` is that composite.
* `wedgePullMap_stalk_bijective`, `wedgePullMap_app_bijective`, `wedgePullSectionsEquiv`: it is an
  isomorphism on stalks and on sections over every open.
* `globalPullWedgeEquiv`, `genericGermTop_globalPullWedgeEquiv`: for `M = Ω¹_{X/R₀}` and global
  sections over `S = Spec R₀`, the isomorphism `Γ(S, e^*(⋀^n Ω¹)) ≃ Γ(S, ⋀^n e^*Ω¹)` and its
  compatibility with the generic germ.

Everything here uses Mathlib and the sheaf constructions of this directory only.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.HeightModelM5

namespace PW

variable {S X : Scheme.{u}} (e : S ⟶ X) (M : X.Modules) (n : ℕ)

/-- A sheaf of modules as a presheaf of modules over the structure presheaf of commutative rings. -/
noncomputable abbrev valC {Y : Scheme.{u}} (N : Y.Modules) :
    PresheafOfModulesOfCommRing Y.presheaf :=
  N.val

/-- `e^* M`. -/
noncomputable abbrev pullM : S.Modules := (Scheme.Modules.pullback e).obj M

/-- `⋀^n (e^* M)`. -/
noncomputable abbrev wedgePull : S.Modules := schemeWedge (valC (pullM e M)) n

/-- `e^* (⋀^n M)`. -/
noncomputable abbrev pullWedge : S.Modules :=
  (Scheme.Modules.pullback e).obj (schemeWedge (valC M) n)

/-! ## The morphism -/

/-- The unit of `e^* ⊣ e_*` on sections over `U`, semilinear along `e^♯ : Γ(X, U) → Γ(S, e⁻¹ U)`. -/
noncomputable def unitₛₗ (U : X.Opens) :
    (valC M).obj (op U) →ₛₗ[(e.app U).hom] (valC (pullM e M)).obj (op (e ⁻¹ᵁ U)) where
  toFun m := (pullUnit e M).app U m
  map_add' a b := map_add _ a b
  map_smul' r m := Scheme.Modules.Hom.app_smul (pullUnit e M) r m

/-- The canonical map from `⋀^n N(V)` to the sections of the sheaf `⋀^n N`, as a linear map. -/
noncomputable def wedgeUnitₗ (N : PresheafOfModulesOfCommRing S.presheaf) (V : S.Opens) :
    ⋀[Γ(S, V)]^n (N.obj (op V)) →ₗ[Γ(S, V)] Γ(schemeWedge N n, V) where
  toFun := GG.wedgeUnit N n V
  map_add' a b := by unfold GG.wedgeUnit; exact map_add _ a b
  map_smul' c ω := GG.wedgeUnit_smul N n V c ω

theorem wedgeUnitₗ_apply (N : PresheafOfModulesOfCommRing S.presheaf) (V : S.Opens)
    (ω : ⋀[Γ(S, V)]^n (N.obj (op V))) : wedgeUnitₗ n N V ω = GG.wedgeUnit N n V ω := rfl

/-- On sections over `U`: `ω ↦ ⋀^n(unit)(ω)`, sent to the sheaf `⋀^n (e^* M)` over `e⁻¹ U`. -/
noncomputable def psiApp (U : X.Opens) :
    ⋀[Γ(X, U)]^n ((valC M).obj (op U)) →ₛₗ[(e.app U).hom] Γ(wedgePull e M n, e ⁻¹ᵁ U) :=
  (wedgeUnitₗ n (valC (pullM e M)) (e ⁻¹ᵁ U)).comp (wedgeMap (e.app U).hom n (unitₛₗ e M U))

theorem psiApp_apply (U : X.Opens) (ω : ⋀[Γ(X, U)]^n ((valC M).obj (op U))) :
    psiApp e M n U ω =
      GG.wedgeUnit (valC (pullM e M)) n (e ⁻¹ᵁ U) (wedgeMap (e.app U).hom n (unitₛₗ e M U) ω) :=
  rfl

theorem psiApp_ιMulti (U : X.Opens) (t : Fin n → (valC M).obj (op U)) :
    psiApp e M n U (exteriorPower.ιMulti _ n t) =
      GG.wedgeUnit (valC (pullM e M)) n (e ⁻¹ᵁ U)
        (exteriorPower.ιMulti _ n (fun i => (pullUnit e M).app U (t i))) := by
  rw [psiApp_apply, wedgeMap_ιMulti]
  rfl

/-- The canonical map to the sheaf `⋀^n N` commutes with restriction. -/
theorem wedgeUnit_res (N : PresheafOfModulesOfCommRing S.presheaf) {V W : S.Opens} (k : W ⟶ V)
    (ω : ⋀[Γ(S, V)]^n (N.obj (op V))) :
    GG.wedgeUnit N n W (wedgeRes N n k.op ω) =
      (schemeWedge N n).val.presheaf.map k.op (GG.wedgeUnit N n V ω) :=
  PresheafOfModules.naturality_apply
    (@toWedgeSheaf _ _ _ S.presheaf S.ringCatSheaf (𝟙 _) isLocallyInjective_ringCatSheaf
      isLocallySurjective_ringCatSheaf _ _ N n) k.op ω

theorem psiApp_res {U V : X.Opens} (j : V ⟶ U) (ω : ⋀[Γ(X, U)]^n ((valC M).obj (op U))) :
    psiApp e M n V (wedgeRes (valC M) n j.op ω) =
      (wedgePull e M n).val.presheaf.map ((Opens.map e.base).map j).op (psiApp e M n U ω) := by
  rw [psiApp_apply, psiApp_apply, ← wedgeUnit_res]
  congr 1
  unfold wedgeRes
  refine GG.wedgeMap_comp_eq n _ _ _ _ (fun a => ?_) _ _ _ _ (fun m => ?_) ω
  · exact congrArg (fun φ => φ.hom a) (Scheme.Hom.naturality e j.op)
  · rw [PresheafOfModules.restrictₛₗ_apply, PresheafOfModules.restrictₛₗ_apply]
    exact hom_app_map_apply (pullUnit e M) j m

/-- The morphism of presheaves of modules `⋀^n M(U) → Γ(e⁻¹ U, ⋀^n (e^* M))`. -/
noncomputable def psi : wedgePresheaf (valC M) n ⟶
    (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
      ((SheafOfModules.forget X.ringCatSheaf).obj
        ((Scheme.Modules.pushforward e).obj (wedgePull e M n))) :=
  PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (psiApp e M n U.unop).toAddMonoidHom
      naturality := by
        intro U V i
        ext ω
        exact psiApp_res e M n i.unop ω }
    (fun U r ω => (psiApp e M n U.unop).map_smulₛₗ r ω)

/-- The adjoint morphism `⋀^n M ⟶ e_* ⋀^n (e^* M)`, out of the sheafification. -/
noncomputable def bigPsi : schemeWedge (valC M) n ⟶
    (Scheme.Modules.pushforward e).obj (wedgePull e M n) :=
  ((@PresheafOfModules.sheafificationAdjunction _ _ _ _ X.ringCatSheaf (𝟙 _)
    isLocallyInjective_ringCatSheaf isLocallySurjective_ringCatSheaf _ _).homEquiv _ _).symm
    (psi e M n)

theorem bigPsi_app_wedgeUnit (U : X.Opens) (ω : ⋀[Γ(X, U)]^n ((valC M).obj (op U))) :
    (bigPsi e M n).app U (GG.wedgeUnit (valC M) n U ω) = psiApp e M n U ω := by
  have h := ((@PresheafOfModules.sheafificationAdjunction _ _ _ _ X.ringCatSheaf (𝟙 _)
    isLocallyInjective_ringCatSheaf isLocallySurjective_ringCatSheaf _ _).homEquiv _ _
      ).apply_symm_apply (psi e M n)
  have h2 := ((@PresheafOfModules.sheafificationAdjunction _ _ _ _ X.ringCatSheaf (𝟙 _)
    isLocallyInjective_ringCatSheaf isLocallySurjective_ringCatSheaf _ _).homEquiv_unit _ _
      (bigPsi e M n)).symm.trans h
  exact congrArg (fun φ => (φ.app (op U)).hom ω) h2

/-- **The natural morphism `e^*(⋀^n M) ⟶ ⋀^n (e^* M)`**. -/
noncomputable def wedgePullMap : pullWedge e M n ⟶ wedgePull e M n :=
  ((Scheme.Modules.pullbackPushforwardAdjunction e).homEquiv _ _).symm (bigPsi e M n)

theorem wedgePullMap_app_unit (U : X.Opens) (m : Γ(schemeWedge (valC M) n, U)) :
    (wedgePullMap e M n).app (e ⁻¹ᵁ U) ((pullUnit e (schemeWedge (valC M) n)).app U m) =
      (bigPsi e M n).app U m := by
  have h := ((Scheme.Modules.pullbackPushforwardAdjunction e).homEquiv _ _).apply_symm_apply
    (bigPsi e M n)
  have h1 := ((Scheme.Modules.pullbackPushforwardAdjunction e).homEquiv_unit _ _
    (wedgePullMap e M n)).symm.trans h
  have h2 := congrArg (fun φ => (Scheme.Modules.Hom.app φ U) m) h1
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at h2
  exact h2

/-! ## On stalks -/

/-- `wedgePullMap` on stalks, as a linear map. -/
noncomputable def stalkMap (s : S) :
    TopCat.Presheaf.stalk (C := Ab.{u}) (pullWedge e M n).val.presheaf s →ₗ[S.presheaf.stalk s]
      TopCat.Presheaf.stalk (C := Ab.{u}) (wedgePull e M n).val.presheaf s :=
  stalkDesc (pullWedge e M n) s
    (fun U hU => (TopCat.Presheaf.germ (wedgePull e M n).val.presheaf U s hU).hom.comp
      ((wedgePullMap e M n).app U).hom)
    (by
      intro U V i hU a
      change TopCat.Presheaf.germ (wedgePull e M n).val.presheaf U s hU
          ((wedgePullMap e M n).app U ((pullWedge e M n).presheaf.map i.op a)) =
        TopCat.Presheaf.germ (wedgePull e M n).val.presheaf V s (leOfHom i hU)
          ((wedgePullMap e M n).app V a)
      rw [hom_app_map_apply]
      exact germ_map_apply _ s i hU _)
    (by
      intro U hU r a
      change TopCat.Presheaf.germ (wedgePull e M n).val.presheaf U s hU
          ((wedgePullMap e M n).app U (r • a)) =
        S.presheaf.germ U s hU r • TopCat.Presheaf.germ (wedgePull e M n).val.presheaf U s hU
          ((wedgePullMap e M n).app U a)
      rw [Scheme.Modules.Hom.app_smul]
      exact stalk_germ_smul _ s U hU _ _)

theorem stalkMap_germ (s : S) (U : S.Opens) (hU : s ∈ U) (a : Γ(pullWedge e M n, U)) :
    stalkMap e M n s (TopCat.Presheaf.germ (pullWedge e M n).val.presheaf U s hU a) =
      TopCat.Presheaf.germ (wedgePull e M n).val.presheaf U s hU ((wedgePullMap e M n).app U a) :=
  stalkDesc_germ _ _ _ _ _ U hU a

/-- The germ at `s` of `bigPsi` of a section depends only on its germ at `e(s)`. -/
theorem germ_bigPsi_congr (s : S) {V V' : X.Opens} (hV : e s ∈ V) (hV' : e s ∈ V')
    (m : Γ(schemeWedge (valC M) n, V)) (m' : Γ(schemeWedge (valC M) n, V'))
    (h : TopCat.Presheaf.germ (schemeWedge (valC M) n).val.presheaf V (e s) hV m =
      TopCat.Presheaf.germ (schemeWedge (valC M) n).val.presheaf V' (e s) hV' m') :
    TopCat.Presheaf.germ (wedgePull e M n).val.presheaf (e ⁻¹ᵁ V) s hV ((bigPsi e M n).app V m) =
      TopCat.Presheaf.germ (wedgePull e M n).val.presheaf (e ⁻¹ᵁ V') s hV'
        ((bigPsi e M n).app V' m') := by
  obtain ⟨W, hW, iU, iV, heq⟩ :=
    TopCat.Presheaf.germ_eq (schemeWedge (valC M) n).val.presheaf (e s) hV hV' m m' h
  have e1 := hom_app_map_apply (bigPsi e M n) iU m
  have e2 := hom_app_map_apply (bigPsi e M n) iV m'
  have g1 := germ_map_apply (wedgePull e M n) s ((Opens.map e.base).map iU) hW
    ((bigPsi e M n).app V m)
  have g2 := germ_map_apply (wedgePull e M n) s ((Opens.map e.base).map iV) hW
    ((bigPsi e M n).app V' m')
  refine g1.symm.trans (Eq.trans ?_ g2)
  refine (congrArg (TopCat.Presheaf.germ (wedgePull e M n).val.presheaf (e ⁻¹ᵁ W) s hW) e1.symm
    ).trans ?_
  refine Eq.trans ?_ (congrArg (TopCat.Presheaf.germ (wedgePull e M n).val.presheaf (e ⁻¹ᵁ W) s
    hW) e2)
  exact congrArg (fun z => TopCat.Presheaf.germ (wedgePull e M n).val.presheaf (e ⁻¹ᵁ W) s hW
    ((bigPsi e M n).app W z)) heq

/-! ## The stalk formula for `e^*(⋀^n M)` -/

/-- `schemeWedgeStalkEquiv` as a linear equivalence over the local ring. -/
noncomputable def wedgeStalkLin {Y : Scheme.{u}} (N : PresheafOfModulesOfCommRing Y.presheaf)
    (y : Y) :
    TopCat.Presheaf.stalk (C := Ab.{u}) (schemeWedge N n).val.presheaf y ≃ₗ[Y.presheaf.stalk y]
      ⋀[Y.presheaf.stalk y]^n (TopCat.Presheaf.stalk (C := Ab.{u}) N.presheaf y) :=
  { schemeWedgeStalkEquiv N n y with map_smul' := GG.schemeWedgeStalkEquiv_smul N n y }

theorem wedgeStalkLin_apply {Y : Scheme.{u}} (N : PresheafOfModulesOfCommRing Y.presheaf) (y : Y)
    (z : TopCat.Presheaf.stalk (C := Ab.{u}) (schemeWedge N n).val.presheaf y) :
    wedgeStalkLin n N y z = schemeWedgeStalkEquiv N n y z := rfl

/-- `⋀^n` of a linear equivalence is bijective. -/
theorem exteriorPower_map_bijective {R : Type*} [CommRing R] {P Q : Type*} [AddCommGroup P]
    [Module R P] [AddCommGroup Q] [Module R Q] (E : P ≃ₗ[R] Q) :
    Function.Bijective (exteriorPower.map n E.toLinearMap) := by
  have h1 : E.symm.toLinearMap ∘ₗ E.toLinearMap = LinearMap.id :=
    LinearMap.ext fun x => E.symm_apply_apply x
  have h2 : E.toLinearMap ∘ₗ E.symm.toLinearMap = LinearMap.id :=
    LinearMap.ext fun x => E.apply_symm_apply x
  refine Function.bijective_iff_has_inverse.2 ⟨exteriorPower.map n E.symm.toLinearMap,
    fun x => ?_, fun x => ?_⟩
  · rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, h1, exteriorPower.map_id,
      LinearMap.id_apply]
  · rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, h2, exteriorPower.map_id,
      LinearMap.id_apply]

/-- The linear algebra behind the stalk formula: `⋀^n` of a semilinear `u` factoring as
`m ↦ F (1 ⊗ g m)` is `⋀^n F` after the base change of exterior powers and `1 ⊗ ⋀^n g`. -/
theorem wedgeMap_eq_map_baseChange {R A B P₀ P Q : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup P₀] [Module R P₀] [AddCommGroup P] [Module A P] [AddCommGroup Q]
    [Module B Q] (α : R →+* A) (β : R →+* B) (hβ : ∀ r, β r = algebraMap A B (α r))
    (g : P₀ →ₛₗ[α] P) (u : P₀ →ₛₗ[β] Q) (F : B ⊗[A] P →ₗ[B] Q)
    (hF : ∀ m, F ((1 : B) ⊗ₜ[A] g m) = u m) (ω : ⋀[R]^n P₀) :
    wedgeMap β n u ω = exteriorPower.map n F
      ((exteriorPowerBaseChange A B P n).symm ((1 : B) ⊗ₜ[A] wedgeMap α n g ω)) := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨t, rfl⟩ := hz
    rw [wedgeMap_ιMulti, wedgeMap_ιMulti, exteriorPowerBaseChange_symm_tmul, one_smul,
      exteriorPowerToBaseChange_ιMulti, exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    exact (hF (t i)).symm
  | zero => simp only [map_zero, TensorProduct.tmul_zero]
  | add x y _ _ hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | smul c x _ hx =>
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, TensorProduct.tmul_smul,
      ← algebraMap_smul B (α c), LinearEquiv.map_smul, LinearMap.map_smul, hx, hβ]

section StalkFormula

variable (s : S)

attribute [local instance] pullbackStalkAlgebra

/-- **The stalk formula for `e^*(⋀^n M)`**: the composite
`(e^*(⋀^n M))_s ≃ 𝒪_{S,s} ⊗ (⋀^n M)_{e(s)} ≃ 𝒪_{S,s} ⊗ ⋀^n M_{e(s)} ≃ ⋀^n (𝒪_{S,s} ⊗ M_{e(s)})
→ ⋀^n (e^* M)_s` of `stalkPullbackEquiv`, `schemeWedgeStalkEquiv`, `exteriorPowerBaseChange` and
`⋀^n` of the inverse of `stalkPullbackEquiv`. -/
noncomputable def pullWedgeStalkMap :
    TopCat.Presheaf.stalk (C := Ab.{u}) (pullWedge e M n).val.presheaf s →ₗ[S.presheaf.stalk s]
      ⋀[S.presheaf.stalk s]^n (TopCat.Presheaf.stalk (C := Ab.{u}) (pullM e M).val.presheaf s) :=
  exteriorPower.map n (stalkPullbackEquiv e M s).symm.toLinearMap ∘ₗ
    (exteriorPowerBaseChange (X.presheaf.stalk (e s)) (S.presheaf.stalk s)
      (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf (e s)) n).symm.toLinearMap ∘ₗ
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (S.presheaf.stalk s)
      (S.presheaf.stalk s)) (wedgeStalkLin n (valC M) (e s))).toLinearMap ∘ₗ
    (stalkPullbackEquiv e (schemeWedge (valC M) n) s).toLinearMap

theorem pullWedgeStalkMap_bijective : Function.Bijective (pullWedgeStalkMap e M n s) :=
  (exteriorPower_map_bijective n (stalkPullbackEquiv e M s).symm).comp
    ((exteriorPowerBaseChange (X.presheaf.stalk (e s)) (S.presheaf.stalk s)
      (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf (e s)) n).symm.bijective.comp
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (S.presheaf.stalk s)
      (S.presheaf.stalk s)) (wedgeStalkLin n (valC M) (e s))).bijective.comp
    (stalkPullbackEquiv e (schemeWedge (valC M) n) s).bijective))

theorem pullWedgeStalkMap_unitGerm (V : X.Opens) (hV : e s ∈ V)
    (m : Γ(schemeWedge (valC M) n, V)) :
    pullWedgeStalkMap e M n s (unitGerm e (schemeWedge (valC M) n) s V hV m) =
      exteriorPower.map n (stalkPullbackEquiv e M s).symm.toLinearMap
        ((exteriorPowerBaseChange (X.presheaf.stalk (e s)) (S.presheaf.stalk s)
          (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf (e s)) n).symm
          ((1 : S.presheaf.stalk s) ⊗ₜ[X.presheaf.stalk (e s)]
            schemeWedgeStalkEquiv (valC M) n (e s)
              (TopCat.Presheaf.germ (schemeWedge (valC M) n).val.presheaf V (e s) hV m))) := by
  have h1 := stalkPullbackEquiv_unitGerm e (schemeWedge (valC M) n) s V hV m
  have h2 := congrArg (fun z => exteriorPower.map n (stalkPullbackEquiv e M s).symm.toLinearMap
    ((exteriorPowerBaseChange (X.presheaf.stalk (e s)) (S.presheaf.stalk s)
      (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf (e s)) n).symm
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (S.presheaf.stalk s)
        (S.presheaf.stalk s)) (wedgeStalkLin n (valC M) (e s)) z))) h1
  exact h2

/-- The key computation on the image of a section of the presheaf `U ↦ ⋀^n M(U)`. -/
theorem wedgeStalk_germ_psiApp (W : X.Opens) (hW : e s ∈ W)
    (ω : ⋀[Γ(X, W)]^n ((valC M).obj (op W))) :
    schemeWedgeStalkEquiv (valC (pullM e M)) n s
        (TopCat.Presheaf.germ (wedgePull e M n).val.presheaf (e ⁻¹ᵁ W) s hW
          (psiApp e M n W ω)) =
      exteriorPower.map n (stalkPullbackEquiv e M s).symm.toLinearMap
        ((exteriorPowerBaseChange (X.presheaf.stalk (e s)) (S.presheaf.stalk s)
          (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf (e s)) n).symm
          ((1 : S.presheaf.stalk s) ⊗ₜ[X.presheaf.stalk (e s)]
            wedgeGerm (valC M) n (e s) W hW ω)) := by
  have i1 : schemeWedgeStalkEquiv (valC (pullM e M)) n s
      (TopCat.Presheaf.germ (wedgePull e M n).val.presheaf (e ⁻¹ᵁ W) s hW (psiApp e M n W ω)) =
      wedgeGerm (valC (pullM e M)) n s (e ⁻¹ᵁ W) hW
        (wedgeMap (e.app W).hom n (unitₛₗ e M W) ω) :=
    GG.schemeWedgeStalkEquiv_wedgeUnit _ n s (e ⁻¹ᵁ W) hW _
  haveI : RingHomCompTriple (e.app W).hom (S.presheaf.germ (e ⁻¹ᵁ W) s hW).hom
      ((S.presheaf.germ (e ⁻¹ᵁ W) s hW).hom.comp (e.app W).hom) := ⟨rfl⟩
  have i2 : wedgeGerm (valC (pullM e M)) n s (e ⁻¹ᵁ W) hW
      (wedgeMap (e.app W).hom n (unitₛₗ e M W) ω) =
      wedgeMap ((S.presheaf.germ (e ⁻¹ᵁ W) s hW).hom.comp (e.app W).hom) n
        ((germₛₗ (valC (pullM e M)) s (e ⁻¹ᵁ W) hW).comp (unitₛₗ e M W)) ω :=
    wedgeMap_comp_apply _ n _ _ rfl _ _ _ (fun _ => rfl) ω
  refine i1.trans (i2.trans ?_)
  exact wedgeMap_eq_map_baseChange n (X.presheaf.germ W (e s) hW).hom _
    (fun r => (Scheme.Hom.germ_stalkMap_apply e W s hW r).symm) (germₛₗ (valC M) (e s) W hW) _
    (stalkPullbackEquiv e M s).symm.toLinearMap
    (fun m => (stalkPullbackEquiv_symm_tmul e M s 1 W hW m).trans (one_smul _ _)) ω

/-- **On stalks, `wedgePullMap` is the stalk formula**: `schemeWedgeStalkEquiv` after the stalk map
of `wedgePullMap` is `pullWedgeStalkMap`. -/
theorem wedgeStalkLin_comp_stalkMap :
    (wedgeStalkLin n (valC (pullM e M)) s).toLinearMap ∘ₗ stalkMap e M n s =
      pullWedgeStalkMap e M n s := by
  refine stalkPullback_hom_ext fun V hV m => ?_
  obtain ⟨W, -, hW, ω, hω⟩ := GG.schemeWedge_exists_germ (valC M) n (e s) V hV
    (TopCat.Presheaf.germ (schemeWedge (valC M) n).val.presheaf V (e s) hV m)
  have k1 : stalkMap e M n s (unitGerm e (schemeWedge (valC M) n) s V hV m) =
      TopCat.Presheaf.germ (wedgePull e M n).val.presheaf (e ⁻¹ᵁ V) s hV
        ((bigPsi e M n).app V m) :=
    (stalkMap_germ e M n s (e ⁻¹ᵁ V) hV _).trans
      (congrArg (TopCat.Presheaf.germ (wedgePull e M n).val.presheaf (e ⁻¹ᵁ V) s hV)
        (wedgePullMap_app_unit e M n V m))
  have k2 : TopCat.Presheaf.germ (wedgePull e M n).val.presheaf (e ⁻¹ᵁ V) s hV
        ((bigPsi e M n).app V m) =
      TopCat.Presheaf.germ (wedgePull e M n).val.presheaf (e ⁻¹ᵁ W) s hW
        (psiApp e M n W ω) :=
    (germ_bigPsi_congr e M n s hV hW m _ hω.symm).trans
      (congrArg (TopCat.Presheaf.germ (wedgePull e M n).val.presheaf (e ⁻¹ᵁ W) s hW)
        (bigPsi_app_wedgeUnit e M n W ω))
  have k3 : schemeWedgeStalkEquiv (valC M) n (e s)
        (TopCat.Presheaf.germ (schemeWedge (valC M) n).val.presheaf V (e s) hV m) =
      wedgeGerm (valC M) n (e s) W hW ω :=
    (congrArg (schemeWedgeStalkEquiv (valC M) n (e s)) hω.symm).trans
      (GG.schemeWedgeStalkEquiv_wedgeUnit _ n _ W hW ω)
  refine Eq.trans ?_ (pullWedgeStalkMap_unitGerm e M n s V hV m).symm
  refine (congrArg (schemeWedgeStalkEquiv (valC (pullM e M)) n s) (k1.trans k2)).trans ?_
  refine (wedgeStalk_germ_psiApp e M n s W hW ω).trans ?_
  exact congrArg (fun z => exteriorPower.map n (stalkPullbackEquiv e M s).symm.toLinearMap
    ((exteriorPowerBaseChange (X.presheaf.stalk (e s)) (S.presheaf.stalk s)
      (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf (e s)) n).symm
      ((1 : S.presheaf.stalk s) ⊗ₜ[X.presheaf.stalk (e s)] z))) k3.symm

end StalkFormula

/-! ## Isomorphism on stalks and on sections -/

/-- **`wedgePullMap` is bijective on stalks.** -/
theorem stalkMap_bijective (s : S) : Function.Bijective (stalkMap e M n s) := by
  have h : ⇑(stalkMap e M n s) =
      ⇑(wedgeStalkLin n (valC (pullM e M)) s).symm ∘ ⇑(pullWedgeStalkMap e M n s) := by
    funext y
    exact ((wedgeStalkLin n (valC (pullM e M)) s).symm_apply_apply _).symm.trans
      (congrArg (wedgeStalkLin n (valC (pullM e M)) s).symm
        (LinearMap.congr_fun (wedgeStalkLin_comp_stalkMap e M n s) y))
  rw [h]
  exact (LinearEquiv.bijective _).comp (pullWedgeStalkMap_bijective e M n s)

/-- The underlying sheaf of abelian groups of a sheaf of modules. -/
noncomputable def abSheaf {Y : Scheme.{u}} (N : Y.Modules) : TopCat.Sheaf Ab.{u} Y :=
  ⟨(Scheme.Modules.toPresheaf _).obj N, N.isSheaf⟩

/-- `wedgePullMap` as a morphism of sheaves of abelian groups. -/
noncomputable def abSheafHom : abSheaf (pullWedge e M n) ⟶ abSheaf (wedgePull e M n) :=
  ⟨(Scheme.Modules.toPresheaf _).map (wedgePullMap e M n)⟩

theorem stalkFunctor_map_abSheafHom (s : S)
    (y : TopCat.Presheaf.stalk (C := Ab.{u}) (pullWedge e M n).val.presheaf s) :
    ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab.{u} s).map (abSheafHom e M n).hom) y =
      stalkMap e M n s y := by
  obtain ⟨U, hU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ y
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply U s hU (abSheafHom e M n).hom a).trans ?_
  exact (stalkMap_germ e M n s U hU a).symm

/-- **`wedgePullMap` is an isomorphism on stalks**, as a morphism of sheaves of abelian groups. -/
theorem wedgePullMap_stalk_bijective (s : S) :
    Function.Bijective
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab.{u} s).map (abSheafHom e M n).hom)) :=
  (funext (stalkFunctor_map_abSheafHom e M n s) ▸ stalkMap_bijective e M n s :)

/-- **`wedgePullMap` is bijective on sections over every open.** -/
theorem wedgePullMap_app_bijective (U : S.Opens) :
    Function.Bijective ((wedgePullMap e M n).app U) :=
  TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective (abSheafHom e M n) U
    (fun s _ => wedgePullMap_stalk_bijective e M n s)

/-- **`wedgePullMap` is an isomorphism of sheaves of abelian groups.** -/
theorem isIso_abSheafHom : IsIso (abSheafHom e M n) := by
  haveI : ∀ s : S, IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} s).map (abSheafHom e M n).hom) :=
    fun s => (ConcreteCategory.isIso_iff_bijective _).2 (wedgePullMap_stalk_bijective e M n s)
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso (abSheafHom e M n)

/-- **`e^*(⋀^n M) ≃ ⋀^n (e^* M)` on sections over `U`**, linear over `Γ(S, U)`. -/
noncomputable def wedgePullSectionsEquiv (U : S.Opens) :
    Γ(pullWedge e M n, U) ≃ₗ[Γ(S, U)] Γ(wedgePull e M n, U) :=
  LinearEquiv.ofBijective
    { toFun := (wedgePullMap e M n).app U
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a => Scheme.Modules.Hom.app_smul _ r a }
    (wedgePullMap_app_bijective e M n U)

theorem wedgePullSectionsEquiv_apply (U : S.Opens) (a : Γ(pullWedge e M n, U)) :
    wedgePullSectionsEquiv e M n U a = (wedgePullMap e M n).app U a := rfl

/-- **Compatibility with stalks**: the germ of the image of a section is the stalk formula
applied to its germ. -/
theorem wedgeStalkEquiv_germ_wedgePullMap (s : S) (U : S.Opens) (hU : s ∈ U)
    (a : Γ(pullWedge e M n, U)) :
    schemeWedgeStalkEquiv (valC (pullM e M)) n s
        (TopCat.Presheaf.germ (wedgePull e M n).val.presheaf U s hU
          (wedgePullSectionsEquiv e M n U a)) =
      pullWedgeStalkMap e M n s
        (TopCat.Presheaf.germ (pullWedge e M n).val.presheaf U s hU a) := by
  exact (congrArg (schemeWedgeStalkEquiv (valC (pullM e M)) n s)
    (stalkMap_germ e M n s U hU a).symm).trans
    (LinearMap.congr_fun (wedgeStalkLin_comp_stalkMap e M n s)
      (TopCat.Presheaf.germ (pullWedge e M n).val.presheaf U s hU a))

end PW

/-! ## Transport of a section and its index along a linear equivalence -/

/-- The index of `R x` is preserved by a linear equivalence. -/
theorem index_span_map_equiv {R P Q : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (φ : P ≃ₗ[R] Q) (m : P) :
    (Submodule.span R {φ m}).toAddSubgroup.index = (Submodule.span R {m}).toAddSubgroup.index := by
  have h : (Submodule.span R {φ m}).toAddSubgroup =
      (Submodule.span R {m}).toAddSubgroup.map (φ.toLinearMap : P →+ Q) := by
    rw [← Submodule.map_toAddSubgroup, Submodule.map_span, Set.image_singleton]
    rfl
  rw [h]
  exact AddSubgroup.index_map_equiv _ φ.toAddEquiv

/-- A nonzero section with finite index and a property of its image and index exists on one side
of a linear equivalence if and only if it exists on the other. -/
theorem exists_span_index_iff_of_equiv {R P Q H : Type*} [CommRing R] [AddCommGroup P]
    [Module R P] [AddCommGroup Q] [Module R Q] (φ : P ≃ₗ[R] Q) (γ : Q → H)
    (Prop' : H → ℕ → Prop) :
    (∃ m : P, m ≠ 0 ∧ (Submodule.span R {m}).toAddSubgroup.index ≠ 0 ∧
        Prop' (γ (φ m)) (Submodule.span R {m}).toAddSubgroup.index) ↔
      ∃ q : Q, q ≠ 0 ∧ (Submodule.span R {q}).toAddSubgroup.index ≠ 0 ∧
        Prop' (γ q) (Submodule.span R {q}).toAddSubgroup.index := by
  constructor
  · rintro ⟨m, hm, hi, hP⟩
    refine ⟨φ m, (map_ne_zero_iff φ φ.injective).2 hm, ?_, ?_⟩
    · rw [index_span_map_equiv]; exact hi
    · rw [index_span_map_equiv]; exact hP
  · rintro ⟨q, hq, hi, hP⟩
    obtain ⟨m, rfl⟩ := φ.surjective q
    refine ⟨m, fun h => hq (by rw [h, map_zero]), ?_, ?_⟩
    · rw [index_span_map_equiv] at hi; exact hi
    · rw [index_span_map_equiv] at hP; exact hP

/-! ## Global sections of `e^*(⋀^n Ω¹)` over an affine base -/

namespace GG

variable {R₀ : Type u} [CommRing R₀] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R₀))
  (e : Spec (CommRingCat.of R₀) ⟶ X) {η : Spec (CommRingCat.of R₀)} (hη : ∀ s, η ⤳ s) (n : ℕ)

/-- **The pullback of the top exterior power**: `ε^* Ω^n = e^*(⋀^n Ω¹_{X/R₀})` on `Spec R₀`. -/
noncomputable abbrev pullTopOmega : (Spec (CommRingCat.of R₀)).Modules :=
  (Scheme.Modules.pullback e).obj (schemeWedge (relOmegaPre f) n)

/-- **`Γ(S, e^*(⋀^n Ω¹)) ≃ Γ(S, ⋀^n e^*Ω¹)`**, linear over `Γ(S, 𝒪_S)`. -/
noncomputable def globalPullWedgeEquiv :
    Γ(pullTopOmega f e n, ⊤) ≃ₗ[Γ(Spec (CommRingCat.of R₀), ⊤)] Γ(pullOmegaTop f e n, ⊤) :=
  PW.wedgePullSectionsEquiv e (relOmega f) n ⊤

/-- **Compatibility with the generic germ**: the generic germ of the image of `σ` is `⋀^n` of the
map to the generic fibre applied to the stalk formula at `η` of the germ of `σ`. -/
theorem genericGermTop_globalPullWedgeEquiv (σ : Γ(pullTopOmega f e n, ⊤)) :
    letI := algSt f (e η)
    letI := algBO e η
    genericGermTop f e hη n (globalPullWedgeEquiv f e n σ) =
      wedgeMap (sig hη η) n (phiₛₗ f e hη η) (PW.pullWedgeStalkMap e (relOmega f) n η
        (TopCat.Presheaf.germ (pullTopOmega f e n).val.presheaf ⊤ η trivial σ)) := by
  letI := algSt f (e η)
  letI := algBO e η
  change wedgeMap (sig hη η) n (phiₛₗ f e hη η) (schemeWedgeStalkEquiv (pullPre f e) n η
    (TopCat.Presheaf.germ (pullOmegaTop f e n).val.presheaf ⊤ η trivial
      (PW.wedgePullSectionsEquiv e (relOmega f) n ⊤ σ))) = _
  exact congrArg (wedgeMap (sig hη η) n (phiₛₗ f e hη η))
    (PW.wedgeStalkEquiv_germ_wedgePullMap e (relOmega f) n η ⊤ trivial σ)

/-- **The generic germ of `Γ(S, e^*(⋀^n Ω¹))`**: through `globalPullWedgeEquiv`. -/
noncomputable def genericGermPullTop :
    letI := algSt f (e η)
    letI := algBO e η
    Γ(pullTopOmega f e n, ⊤) →+
      ⋀[(Spec (CommRingCat.of R₀)).presheaf.stalk η]^n (GenT f e (η := η)) :=
  (genericGermTop f e hη n).comp (globalPullWedgeEquiv f e n).toLinearMap.toAddMonoidHom

/-- **The generic germ of `Γ(S, e^*(⋀^n Ω¹))` is injective** for smooth `f`. -/
theorem genericGermPullTop_injective [Smooth f] (hσ : ∀ s, Function.Injective (sig hη s)) :
    Function.Injective (genericGermPullTop f e hη n) :=
  (genericGermTop_injective f e hη n hσ).comp (globalPullWedgeEquiv f e n).injective

end GG

end ZInQ.HeightModelM5
