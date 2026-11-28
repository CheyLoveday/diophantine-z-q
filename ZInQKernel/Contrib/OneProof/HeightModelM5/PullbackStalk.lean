import Mathlib

/-!
# Stalks of the pullback of a sheaf of modules

Let `e : S ⟶ X` be a morphism of schemes, `M` a sheaf of modules on `X` and `s` a point of `S`.
This file proves the stalk formula

  `(e^* M)_s ≃ₗ[𝒪_{S,s}] 𝒪_{S,s} ⊗[𝒪_{X,e(s)}] M_{e(s)}`

for `e^* = Scheme.Modules.pullback e`, in canonical form: the germ at `s` of the image of a
section `m` of `M` under the unit of the adjunction `e^* ⊣ e_*` is sent to `1 ⊗ₜ germ m`.

## Method

* `stalkDesc`: a compatible family of maps out of the sections near `y` induces a linear map
  out of the stalk at `y`.
* `skyMod y N`: the skyscraper sheaf of modules at `y` with value an `𝒪_{Y,y}`-module `N`;
  its sections over `U` are the functions `y ∈ U → N`.
* `toSky` and `fromSky`: linear maps out of a stalk versus morphisms into a skyscraper.
* Linear maps out of `(e^* M)_s` are determined by their values on germs of unit images
  (`stalkPullback_hom_ext`), through the adjunction `e^* ⊣ e_*`.
* The inverse map is `fromSky` of the adjoint of a morphism `M ⟶ e_* (skyMod s T)`.

The `𝒪_{X,e(s)}`-algebra structure on `𝒪_{S,s}` is `(e.stalkMap s).hom.toAlgebra`; it is the
reducible definition `pullbackStalkAlgebra e s`, a local instance in the main section. The headline
statement is `stalkPullbackFormula`; the equivalence itself is `stalkPullbackEquiv`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry TensorProduct

namespace ZInQ.HeightModelM5

section StalkModule

variable {Y : Scheme.{u}}

/-- The `𝒪_{Y,y}`-module structure on the stalk of a sheaf of modules. -/
noncomputable instance stalkModule (M : Y.Modules) (y : Y) :
    Module (Y.presheaf.stalk y) (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf y) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := Y.presheaf) M.val y

lemma stalk_germ_smul (M : Y.Modules) (y : Y) (U : Y.Opens) (hU : y ∈ U) (r : Γ(Y, U))
    (a : Γ(M, U)) :
    TopCat.Presheaf.germ M.val.presheaf U y hU (r • a) =
      Y.presheaf.germ U y hU r • TopCat.Presheaf.germ M.val.presheaf U y hU a :=
  PresheafOfModules.germ_smul (R := Y.presheaf) M.val y U hU r a

lemma germ_map_apply (M : Y.Modules) (y : Y) {U V : Y.Opens} (i : U ⟶ V) (hU : y ∈ U)
    (a : Γ(M, V)) :
    TopCat.Presheaf.germ M.val.presheaf U y hU (M.presheaf.map i.op a) =
      TopCat.Presheaf.germ M.val.presheaf V y (leOfHom i hU) a :=
  TopCat.Presheaf.germ_res_apply M.val.presheaf i y hU a

lemma hom_app_map_apply {M N : Y.Modules} (θ : M ⟶ N) {U V : Y.Opens} (i : U ⟶ V)
    (a : Γ(M, V)) :
    θ.app U (M.presheaf.map i.op a) = N.presheaf.map i.op (θ.app V a) :=
  ConcreteCategory.congr_hom (θ.mapPresheaf.naturality i.op) a

end StalkModule

section StalkDesc

variable {Y : Scheme.{u}} (M : Y.Modules) (y : Y) {N : Type u} [AddCommGroup N]
  [Module (Y.presheaf.stalk y) N]

/-- The additive map out of a stalk induced by a compatible family of additive maps. -/
noncomputable def stalkDescAdd (f : ∀ U : Y.Opens, y ∈ U → Γ(M, U) →+ N)
    (hf : ∀ (U V : Y.Opens) (i : U ⟶ V) (hU : y ∈ U) (a : Γ(M, V)),
      f U hU (M.presheaf.map i.op a) = f V (leOfHom i hU) a) :
    TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf y ⟶ AddCommGrpCat.of N :=
  Limits.colimit.desc ((OpenNhds.inclusion y).op ⋙ M.val.presheaf)
    { pt := AddCommGrpCat.of N
      ι :=
        { app := fun U => AddCommGrpCat.ofHom (f U.unop.1 U.unop.2)
          naturality := by
            intro U V i
            ext a
            exact hf V.unop.1 U.unop.1 ((OpenNhds.inclusion y).map i.unop) V.unop.2 a } }

omit [Module (Y.presheaf.stalk y) N] in
lemma stalkDescAdd_germ (f : ∀ U : Y.Opens, y ∈ U → Γ(M, U) →+ N)
    (hf : ∀ (U V : Y.Opens) (i : U ⟶ V) (hU : y ∈ U) (a : Γ(M, V)),
      f U hU (M.presheaf.map i.op a) = f V (leOfHom i hU) a)
    (U : Y.Opens) (hU : y ∈ U) (a : Γ(M, U)) :
    stalkDescAdd M y f hf (TopCat.Presheaf.germ M.val.presheaf U y hU a) = f U hU a := by
  have := Limits.colimit.ι_desc
    ({ pt := AddCommGrpCat.of N
       ι :=
        { app := fun U => AddCommGrpCat.ofHom (f U.unop.1 U.unop.2)
          naturality := by
            intro U V i
            ext a
            exact hf V.unop.1 U.unop.1 ((OpenNhds.inclusion y).map i.unop) V.unop.2 a } } :
      Limits.Cocone ((OpenNhds.inclusion y).op ⋙ M.val.presheaf)) (op ⟨U, hU⟩)
  exact ConcreteCategory.congr_hom this a

/-- The linear map out of a stalk induced by a compatible family of linear maps. -/
noncomputable def stalkDesc (f : ∀ U : Y.Opens, y ∈ U → Γ(M, U) →+ N)
    (hf : ∀ (U V : Y.Opens) (i : U ⟶ V) (hU : y ∈ U) (a : Γ(M, V)),
      f U hU (M.presheaf.map i.op a) = f V (leOfHom i hU) a)
    (hsmul : ∀ (U : Y.Opens) (hU : y ∈ U) (r : Γ(Y, U)) (a : Γ(M, U)),
      f U hU (r • a) = Y.presheaf.germ U y hU r • f U hU a) :
    TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf y →ₗ[Y.presheaf.stalk y] N where
  toFun := stalkDescAdd M y f hf
  map_add' := map_add _
  map_smul' := by
    intro r t
    obtain ⟨U, hU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf t
    obtain ⟨V, hV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf r
    have hW : y ∈ U ⊓ V := ⟨hU, hV⟩
    have e1 : TopCat.Presheaf.germ M.val.presheaf U y hU a =
        TopCat.Presheaf.germ M.val.presheaf (U ⊓ V) y hW
          (M.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op a) :=
      (germ_map_apply M y _ hW a).symm
    have e2 : Y.presheaf.germ V y hV b =
        Y.presheaf.germ (U ⊓ V) y hW (Y.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op b) :=
      (TopCat.Presheaf.germ_res_apply Y.presheaf _ y hW b).symm
    rw [e1, e2, ← stalk_germ_smul, stalkDescAdd_germ, stalkDescAdd_germ, hsmul, RingHom.id_apply]

lemma stalkDesc_germ (f : ∀ U : Y.Opens, y ∈ U → Γ(M, U) →+ N)
    (hf : ∀ (U V : Y.Opens) (i : U ⟶ V) (hU : y ∈ U) (a : Γ(M, V)),
      f U hU (M.presheaf.map i.op a) = f V (leOfHom i hU) a)
    (hsmul : ∀ (U : Y.Opens) (hU : y ∈ U) (r : Γ(Y, U)) (a : Γ(M, U)),
      f U hU (r • a) = Y.presheaf.germ U y hU r • f U hU a)
    (U : Y.Opens) (hU : y ∈ U) (a : Γ(M, U)) :
    stalkDesc M y f hf hsmul (TopCat.Presheaf.germ M.val.presheaf U y hU a) = f U hU a :=
  stalkDescAdd_germ M y f hf U hU a

end StalkDesc

section Sky

variable {Y : Scheme.{u}} (y : Y) (N : Type u) [AddCommGroup N] [Module (Y.presheaf.stalk y) N]

/-- Sections of the skyscraper sheaf at `y` over `U`: functions on proofs of `y ∈ U`. -/
def SkySec (U : Y.Opens) : Type u := PLift (y ∈ U) → N

noncomputable instance (U : Y.Opens) : AddCommGroup (SkySec y N U) :=
  inferInstanceAs (AddCommGroup (PLift (y ∈ U) → N))

noncomputable instance (U : Y.Opens) : Module Γ(Y, U) (SkySec y N U) :=
  @Pi.module (PLift (y ∈ U)) (fun _ => N) Γ(Y, U) _ _
    (fun h => Module.compHom N (Y.presheaf.germ U y h.down).hom)

variable {y N} in
lemma skySec_smul_apply {U : Y.Opens} (r : Γ(Y, U)) (f : SkySec y N U) (h : y ∈ U) :
    (r • f) ⟨h⟩ = Y.presheaf.germ U y h r • f ⟨h⟩ := rfl

/-- The skyscraper presheaf of abelian groups at `y` with value `N`. -/
noncomputable def skyAb : (Y.Opens)ᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (SkySec y N U.unop)
  map i := AddCommGrpCat.ofHom
    { toFun := fun f h => f ⟨leOfHom i.unop h.down⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable instance skyAbModule (U : (Y.Opens)ᵒᵖ) :
    Module (Y.ringCatSheaf.obj.obj U) ((skyAb y N).obj U) :=
  inferInstanceAs (Module Γ(Y, U.unop) (SkySec y N U.unop))

omit [Module (Y.presheaf.stalk y) N] in
lemma skyAb_isSheaf : TopCat.Presheaf.IsSheaf (X := Y.toTopCat) (skyAb y N) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  refine ⟨(fun h => sf (Opens.mem_iSup.1 h.down).choose ⟨(Opens.mem_iSup.1 h.down).choose_spec⟩ :
    SkySec y N (iSup U)), ?_, ?_⟩
  · intro i
    funext ⟨h⟩
    exact congrFun (hsf (Opens.mem_iSup.1 ((le_iSup U i : U i ≤ iSup U) h)).choose i)
      ⟨⟨(Opens.mem_iSup.1 ((le_iSup U i : U i ≤ iSup U) h)).choose_spec, h⟩⟩
  · intro t ht
    funext ⟨h⟩
    exact congrFun (ht (Opens.mem_iSup.1 h).choose) ⟨(Opens.mem_iSup.1 h).choose_spec⟩

/-- The skyscraper sheaf of modules at `y` with value `N`. -/
noncomputable def skyMod : Y.Modules :=
  SheafOfModules.mk (R := Y.ringCatSheaf)
    (PresheafOfModules.ofPresheaf (skyAb y N) (by
      intro U V i r m
      funext ⟨h⟩
      exact congrArg (· • m ⟨leOfHom i.unop h⟩)
        (TopCat.Presheaf.germ_res_apply Y.presheaf i.unop y h r).symm))
    (skyAb_isSheaf y N)

variable {y N}

/-- Evaluation of a section of the skyscraper sheaf at a proof of `y ∈ U`. -/
def skyApp {U : Y.Opens} (h : y ∈ U) (f : Γ(skyMod y N, U)) : N := (f : SkySec y N U) ⟨h⟩

/-- A linear map out of the stalk at `y` gives a morphism into the skyscraper sheaf. -/
noncomputable def toSky {F : Y.Modules}
    (f : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y →ₗ[Y.presheaf.stalk y] N) :
    F ⟶ skyMod y N :=
  SheafOfModules.Hom.mk (PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun a =>
            (fun h => f (TopCat.Presheaf.germ F.val.presheaf U.unop y h.down a) :
              SkySec y N U.unop)
          map_zero' := funext fun _ => (congrArg f (map_zero _)).trans f.map_zero
          map_add' := fun a b => funext fun _ =>
            (congrArg f (map_add _ a b)).trans (f.map_add _ _) }
      naturality := by
        intro U V i
        ext a
        funext ⟨h⟩
        exact congrArg f (germ_map_apply F y i.unop h a) }
    (by
      intro U r a
      funext ⟨h⟩
      exact (congrArg f (stalk_germ_smul F y U.unop h r a)).trans (f.map_smul _ _)))

lemma toSky_app {F : Y.Modules}
    (f : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y →ₗ[Y.presheaf.stalk y] N)
    (U : Y.Opens) (a : Γ(F, U)) (h : y ∈ U) :
    skyApp h ((toSky f).app U a) = f (TopCat.Presheaf.germ F.val.presheaf U y h a) := rfl

/-- A morphism into the skyscraper sheaf gives a linear map out of the stalk at `y`. -/
noncomputable def fromSky {F : Y.Modules} (θ : F ⟶ skyMod y N) :
    TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y →ₗ[Y.presheaf.stalk y] N :=
  stalkDesc F y
    (fun U h =>
      { toFun := fun a => skyApp h (θ.app U a)
        map_zero' := by simp only [map_zero]; rfl
        map_add' := by intro a b; simp only [map_add]; rfl })
    (by
      intro U V i hU a
      change skyApp hU (θ.app U (F.presheaf.map i.op a)) = _
      rw [hom_app_map_apply]
      rfl)
    (by
      intro U hU r a
      change skyApp hU (θ.app U (r • a)) = _
      rw [Scheme.Modules.Hom.app_smul]
      rfl)

lemma fromSky_germ {F : Y.Modules} (θ : F ⟶ skyMod y N) (U : Y.Opens) (h : y ∈ U)
    (a : Γ(F, U)) :
    fromSky θ (TopCat.Presheaf.germ F.val.presheaf U y h a) = skyApp h (θ.app U a) :=
  stalkDesc_germ _ _ _ _ _ U h a

end Sky

section Main

variable {S X : Scheme.{u}} (e : S ⟶ X) (M : X.Modules) (s : S)

/-- The unit of the adjunction `e^* ⊣ e_*` at `M`. -/
noncomputable abbrev pullUnit :
    M ⟶ (Scheme.Modules.pushforward e).obj ((Scheme.Modules.pullback e).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction e).unit.app M

/-- The germ at `s` of the image of a section `m` of `M` under the unit of `e^* ⊣ e_*`. -/
noncomputable def unitGerm (V : X.Opens) (hV : e s ∈ V) (m : Γ(M, V)) :
    TopCat.Presheaf.stalk (C := Ab.{u}) ((Scheme.Modules.pullback e).obj M).val.presheaf s :=
  TopCat.Presheaf.germ ((Scheme.Modules.pullback e).obj M).val.presheaf (e ⁻¹ᵁ V) s hV
    ((pullUnit e M).app V m)

variable {e M s} in
/-- Linear maps out of `(e^* M)_s` are determined by their values on germs of unit images. -/
lemma stalkPullback_hom_ext {N : Type u} [AddCommGroup N] [Module (S.presheaf.stalk s) N]
    {f g : TopCat.Presheaf.stalk (C := Ab.{u}) ((Scheme.Modules.pullback e).obj M).val.presheaf s
      →ₗ[S.presheaf.stalk s] N}
    (h : ∀ (V : X.Opens) (hV : e s ∈ V) (m : Γ(M, V)),
      f (unitGerm e M s V hV m) = g (unitGerm e M s V hV m)) : f = g := by
  have key : toSky f = toSky g := by
    apply ((Scheme.Modules.pullbackPushforwardAdjunction e).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    ext V m
    funext ⟨hs⟩
    exact h V hs m
  ext t
  obtain ⟨U, hU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ t
  exact congrArg (fun φ => skyApp hU (φ.app U a)) key

/-- The `𝒪_{X,e(s)}`-algebra structure on `𝒪_{S,s}` given by the stalk map of `e`. -/
noncomputable abbrev pullbackStalkAlgebra : Algebra (X.presheaf.stalk (e s)) (S.presheaf.stalk s) :=
  (e.stalkMap s).hom.toAlgebra

/-- The `𝒪_{X,e(s)}`-module structure on `(e^* M)_s`, by restriction of scalars. -/
noncomputable abbrev pullStalkModule : Module (X.presheaf.stalk (e s))
    (TopCat.Presheaf.stalk (C := Ab.{u}) ((Scheme.Modules.pullback e).obj M).val.presheaf s) :=
  Module.compHom _ (e.stalkMap s).hom

attribute [local instance] pullbackStalkAlgebra pullStalkModule

lemma pullStalk_isScalarTower : IsScalarTower (X.presheaf.stalk (e s)) (S.presheaf.stalk s)
    (TopCat.Presheaf.stalk (C := Ab.{u}) ((Scheme.Modules.pullback e).obj M).val.presheaf s) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] pullStalk_isScalarTower

/-- The `𝒪_{X,e(s)}`-linear map `M_{e(s)} → (e^* M)_s` induced by the unit of `e^* ⊣ e_*`. -/
noncomputable def stalkPullbackFwdAux :
    TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf (e s) →ₗ[X.presheaf.stalk (e s)]
      TopCat.Presheaf.stalk (C := Ab.{u}) ((Scheme.Modules.pullback e).obj M).val.presheaf s :=
  stalkDesc M (e s)
    (fun V hV => (TopCat.Presheaf.germ ((Scheme.Modules.pullback e).obj M).val.presheaf
      (e ⁻¹ᵁ V) s hV).hom.comp ((pullUnit e M).app V).hom)
    (by
      intro U V i hU a
      change TopCat.Presheaf.germ ((Scheme.Modules.pullback e).obj M).val.presheaf (e ⁻¹ᵁ U) s hU
          ((pullUnit e M).app U (M.presheaf.map i.op a)) =
        TopCat.Presheaf.germ ((Scheme.Modules.pullback e).obj M).val.presheaf (e ⁻¹ᵁ V) s
          (leOfHom i hU) ((pullUnit e M).app V a)
      rw [hom_app_map_apply]
      exact germ_map_apply _ s ((Opens.map e.base).map i) hU _)
    (by
      intro V hV r a
      change TopCat.Presheaf.germ ((Scheme.Modules.pullback e).obj M).val.presheaf (e ⁻¹ᵁ V) s hV
          ((pullUnit e M).app V (r • a)) =
        (e.stalkMap s) (X.presheaf.germ V (e s) hV r) •
          TopCat.Presheaf.germ ((Scheme.Modules.pullback e).obj M).val.presheaf (e ⁻¹ᵁ V) s hV
            ((pullUnit e M).app V a)
      rw [Scheme.Modules.Hom.app_smul, Scheme.Hom.germ_stalkMap_apply]
      exact stalk_germ_smul _ s (e ⁻¹ᵁ V) hV _ _)

lemma stalkPullbackFwdAux_germ (V : X.Opens) (hV : e s ∈ V) (m : Γ(M, V)) :
    stalkPullbackFwdAux e M s (TopCat.Presheaf.germ M.val.presheaf V (e s) hV m) =
      unitGerm e M s V hV m :=
  stalkDesc_germ _ _ _ _ _ V hV m

/-- The map `𝒪_{S,s} ⊗[𝒪_{X,e(s)}] M_{e(s)} → (e^* M)_s`. -/
noncomputable def stalkPullbackFwd :
    TensorProduct (X.presheaf.stalk (e s)) (S.presheaf.stalk s)
        (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf (e s)) →ₗ[S.presheaf.stalk s]
      TopCat.Presheaf.stalk (C := Ab.{u}) ((Scheme.Modules.pullback e).obj M).val.presheaf s :=
  LinearMap.liftBaseChange _ (stalkPullbackFwdAux e M s)

/-- The morphism `M ⟶ e_* (skyMod s T)`, `m ↦ 1 ⊗ₜ germ m`, for
`T = 𝒪_{S,s} ⊗[𝒪_{X,e(s)}] M_{e(s)}`. -/
noncomputable def toPushSky : M ⟶ (Scheme.Modules.pushforward e).obj (skyMod s
    (TensorProduct (X.presheaf.stalk (e s)) (S.presheaf.stalk s)
      (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf (e s)))) :=
  SheafOfModules.Hom.mk (PresheafOfModules.homMk
    { app := fun V => AddCommGrpCat.ofHom
        { toFun := fun m => (fun h => (1 : S.presheaf.stalk s) ⊗ₜ[X.presheaf.stalk (e s)]
              TopCat.Presheaf.germ M.val.presheaf V.unop (e s) h.down m :
            SkySec s _ (e ⁻¹ᵁ V.unop))
          map_zero' := funext fun _ =>
            (congrArg (fun z => (1 : S.presheaf.stalk s) ⊗ₜ[X.presheaf.stalk (e s)] z)
              (map_zero _)).trans (tmul_zero _ _)
          map_add' := fun a b => funext fun _ =>
            (congrArg (fun z => (1 : S.presheaf.stalk s) ⊗ₜ[X.presheaf.stalk (e s)] z)
              (map_add _ a b)).trans (tmul_add _ _ _) }
      naturality := by
        intro U V i
        ext a
        funext ⟨h⟩
        exact congrArg (fun z => (1 : S.presheaf.stalk s) ⊗ₜ[X.presheaf.stalk (e s)] z)
          (germ_map_apply M (e s) i.unop h a) }
    (by
      intro V r a
      funext ⟨h⟩
      change (1 : S.presheaf.stalk s) ⊗ₜ[X.presheaf.stalk (e s)]
          TopCat.Presheaf.germ M.val.presheaf V.unop (e s) h (r • a) =
        S.presheaf.germ (e ⁻¹ᵁ V.unop) s h (e.app V.unop r) •
          ((1 : S.presheaf.stalk s) ⊗ₜ[X.presheaf.stalk (e s)]
            TopCat.Presheaf.germ M.val.presheaf V.unop (e s) h a)
      refine (congrArg (fun z => (1 : S.presheaf.stalk s) ⊗ₜ[X.presheaf.stalk (e s)] z)
        (stalk_germ_smul M (e s) V.unop h r a)).trans ?_
      rw [tmul_smul, ← algebraMap_smul (S.presheaf.stalk s)]
      exact congrArg (· • _) (Scheme.Hom.germ_stalkMap_apply e V.unop s h r)))

/-- The map `(e^* M)_s → 𝒪_{S,s} ⊗[𝒪_{X,e(s)}] M_{e(s)}`. -/
noncomputable def stalkPullbackInv :
    TopCat.Presheaf.stalk (C := Ab.{u}) ((Scheme.Modules.pullback e).obj M).val.presheaf s
      →ₗ[S.presheaf.stalk s] TensorProduct (X.presheaf.stalk (e s)) (S.presheaf.stalk s)
        (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf (e s)) :=
  fromSky (((Scheme.Modules.pullbackPushforwardAdjunction e).homEquiv _ _).symm
    (toPushSky e M s))

lemma stalkPullbackInv_unitGerm (V : X.Opens) (hV : e s ∈ V) (m : Γ(M, V)) :
    stalkPullbackInv e M s (unitGerm e M s V hV m) =
      (1 : S.presheaf.stalk s) ⊗ₜ[X.presheaf.stalk (e s)]
        TopCat.Presheaf.germ M.val.presheaf V (e s) hV m := by
  have H := ((Scheme.Modules.pullbackPushforwardAdjunction e).homEquiv _ _).apply_symm_apply
    (toPushSky e M s)
  rw [Adjunction.homEquiv_unit] at H
  rw [stalkPullbackInv, unitGerm]
  exact (fromSky_germ _ (e ⁻¹ᵁ V) hV ((pullUnit e M).app V m)).trans
    (congrArg (fun φ => skyApp (U := e ⁻¹ᵁ V) hV (φ.app V m)) H)

lemma stalkPullbackFwd_tmul (a : S.presheaf.stalk s) (V : X.Opens) (hV : e s ∈ V)
    (m : Γ(M, V)) :
    stalkPullbackFwd e M s (a ⊗ₜ[X.presheaf.stalk (e s)]
        TopCat.Presheaf.germ M.val.presheaf V (e s) hV m) = a • unitGerm e M s V hV m := by
  rw [stalkPullbackFwd, LinearMap.liftBaseChange_tmul, stalkPullbackFwdAux_germ]

lemma stalkPullbackInv_comp_fwd :
    stalkPullbackInv e M s ∘ₗ stalkPullbackFwd e M s = LinearMap.id := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a t
  obtain ⟨V, hV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf t
  calc stalkPullbackInv e M s (stalkPullbackFwd e M s (a ⊗ₜ[X.presheaf.stalk (e s)]
          TopCat.Presheaf.germ M.val.presheaf V (e s) hV m))
      = stalkPullbackInv e M s (a • unitGerm e M s V hV m) :=
        congrArg _ (stalkPullbackFwd_tmul e M s a V hV m)
    _ = a • ((1 : S.presheaf.stalk s) ⊗ₜ[X.presheaf.stalk (e s)]
          TopCat.Presheaf.germ M.val.presheaf V (e s) hV m) := by
        rw [LinearMap.map_smul]
        exact congrArg (a • ·) (stalkPullbackInv_unitGerm e M s V hV m)
    _ = _ := by rw [smul_tmul', smul_eq_mul, mul_one]; rfl

lemma stalkPullbackFwd_comp_inv :
    stalkPullbackFwd e M s ∘ₗ stalkPullbackInv e M s = LinearMap.id := by
  apply stalkPullback_hom_ext
  intro V hV m
  rw [LinearMap.comp_apply, stalkPullbackInv_unitGerm, stalkPullbackFwd_tmul, one_smul,
    LinearMap.id_apply]

/-- The stalk formula: `(e^* M)_s ≃ₗ[𝒪_{S,s}] 𝒪_{S,s} ⊗[𝒪_{X,e(s)}] M_{e(s)}`. -/
noncomputable def stalkPullbackEquiv :
    TopCat.Presheaf.stalk (C := Ab.{u}) ((Scheme.Modules.pullback e).obj M).val.presheaf s
      ≃ₗ[S.presheaf.stalk s] TensorProduct (X.presheaf.stalk (e s)) (S.presheaf.stalk s)
        (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf (e s)) :=
  LinearEquiv.ofLinearMap (stalkPullbackInv e M s) (stalkPullbackFwd e M s)
    (stalkPullbackInv_comp_fwd e M s) (stalkPullbackFwd_comp_inv e M s)

/-- The stalk formula sends the germ of the unit image of `m` to `1 ⊗ₜ germ m`. -/
theorem stalkPullbackEquiv_unitGerm (V : X.Opens) (hV : e s ∈ V) (m : Γ(M, V)) :
    stalkPullbackEquiv e M s (unitGerm e M s V hV m) =
      (1 : S.presheaf.stalk s) ⊗ₜ[X.presheaf.stalk (e s)]
        TopCat.Presheaf.germ M.val.presheaf V (e s) hV m :=
  stalkPullbackInv_unitGerm e M s V hV m

/-- The inverse of the stalk formula on pure tensors. -/
theorem stalkPullbackEquiv_symm_tmul (a : S.presheaf.stalk s) (V : X.Opens) (hV : e s ∈ V)
    (m : Γ(M, V)) :
    (stalkPullbackEquiv e M s).symm (a ⊗ₜ[X.presheaf.stalk (e s)]
        TopCat.Presheaf.germ M.val.presheaf V (e s) hV m) = a • unitGerm e M s V hV m :=
  stalkPullbackFwd_tmul e M s a V hV m

end Main

/-- The stalk formula S2 in canonical form, stated with Mathlib objects only: for a morphism of
schemes `e : S ⟶ X`, a sheaf of modules `M` on `X` and `s : S`, there is an
`𝒪_{S,s}`-linear isomorphism `(e^* M)_s ≃ 𝒪_{S,s} ⊗[𝒪_{X,e(s)}] M_{e(s)}` sending the germ at
`s` of the unit image of a section `m` to `1 ⊗ₜ germ m`. -/
theorem stalkPullbackFormula {S X : Scheme.{u}} (e : S ⟶ X) (M : X.Modules) (s : S) :
    letI : Algebra (X.presheaf.stalk (e s)) (S.presheaf.stalk s) :=
      (e.stalkMap s).hom.toAlgebra
    ∃ φ : TopCat.Presheaf.stalk (C := Ab.{u}) ((Scheme.Modules.pullback e).obj M).val.presheaf s
        ≃ₗ[S.presheaf.stalk s] TensorProduct (X.presheaf.stalk (e s)) (S.presheaf.stalk s)
          (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf (e s)),
      ∀ (V : X.Opens) (hV : e s ∈ V) (m : Γ(M, V)),
        φ (TopCat.Presheaf.germ ((Scheme.Modules.pullback e).obj M).val.presheaf (e ⁻¹ᵁ V) s hV
            (((Scheme.Modules.pullbackPushforwardAdjunction e).unit.app M).app V m)) =
          (1 : S.presheaf.stalk s) ⊗ₜ[X.presheaf.stalk (e s)]
            TopCat.Presheaf.germ M.val.presheaf V (e s) hV m :=
  ⟨stalkPullbackEquiv e M s, stalkPullbackEquiv_unitGerm e M s⟩

end ZInQ.HeightModelM5
