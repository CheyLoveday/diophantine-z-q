import Mathlib

/-!
# Exterior powers of presheaves of modules

For a presheaf of commutative rings `R` and a presheaf of `R`-modules `M`, this file builds the
presheaf of modules `U ↦ ⋀^n_{R(U)} M(U)`, its sheafification, and computes stalks: over a
topological space, the stalk of the exterior power presheaf at `x` is `⋀^n` over `R_x` of the
stalk `M_x`, and the same holds for its sheafification.

Main declarations:
* `wedgeMap`: functoriality of `⋀^n` along a semilinear map `M →ₛₗ[φ] N` over a ring map `φ`;
* `wedgePresheaf M n`: the presheaf of modules `U ↦ ⋀^n_{R(U)} M(U)`;
* `wedgeSheaf α M n`: its sheafification, for a sheaf of rings receiving `α`;
* `stalkWedgeEquiv`: the `R_x`-linear equivalence `(⋀^n M)_x ≃ ⋀^n_{R_x} M_x`;
* `stalkWedgeSheafEquiv`: the additive equivalence for the stalk of the sheafification;
* `schemeWedge`, `schemeWedgeStalkEquiv`: the same on a scheme, over `𝒪_X`.

The stalk computation uses that a stalk is a filtered colimit: finitely many germs have
representatives on a common open neighbourhood, and two such representatives agree on a smaller
one. No construction here is specific to differentials.
-/

open CategoryTheory TopologicalSpace

universe u

namespace ZInQ.HeightModelM5

section Module

variable {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (n : ℕ)
  {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]

theorem fun_update_eq {ι α β : Type*} [DecidableEq ι] (f : α → β) (m : ι → α) (i : ι) (v : α) :
    (fun j => f (Function.update m i v j)) = Function.update (fun j => f (m j)) i (f v) := by
  funext j
  exact Function.apply_update (fun _ => f) m i v j

/-- The `A`-alternating map `m ↦ ι(f ∘ m)` into `⋀[B]^n N`, where `A` acts through `φ`. -/
noncomputable def wedgeAlt (f : M →ₛₗ[φ] N) :
    letI : Module A (⋀[B]^n N) := Module.compHom _ φ
    M [⋀^Fin n]→ₗ[A] ⋀[B]^n N :=
  letI : Module A (⋀[B]^n N) := Module.compHom _ φ
  { toFun := fun m => exteriorPower.ιMulti B n (fun i => f (m i))
    map_update_add' := fun m i x y => by
      simp only [fun_update_eq, map_add, AlternatingMap.map_update_add]
    map_update_smul' := fun m i a x => by
      simp only [fun_update_eq, LinearMap.map_smulₛₗ, AlternatingMap.map_update_smul]
      rfl
    map_eq_zero_of_eq' := fun m i j h hij =>
      (exteriorPower.ιMulti B n).map_eq_zero_of_eq _ (by simp only [h]) hij }

/-- Functoriality of `⋀^n` along a semilinear map: `⋀[A]^n M → ⋀[B]^n N`. -/
noncomputable def wedgeMap (f : M →ₛₗ[φ] N) : ⋀[A]^n M →ₛₗ[φ] ⋀[B]^n N :=
  letI : Module A (⋀[B]^n N) := Module.compHom _ φ
  let g := exteriorPower.alternatingMapLinearEquiv (wedgeAlt φ n f)
  { toFun := g
    map_add' := g.map_add
    map_smul' := g.map_smul }

@[simp]
theorem wedgeMap_ιMulti (f : M →ₛₗ[φ] N) (m : Fin n → M) :
    wedgeMap φ n f (exteriorPower.ιMulti A n m) = exteriorPower.ιMulti B n (fun i => f (m i)) := by
  let : Module A (⋀[B]^n N) := Module.compHom _ φ
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (wedgeAlt φ n f) m

/-- Semilinear maps out of `⋀[A]^n M` are determined by their values on `ιMulti`. -/
theorem wedge_ext {Q : Type*} [AddCommGroup Q] [Module B Q] {g h : ⋀[A]^n M →ₛₗ[φ] Q}
    (H : ∀ m, g (exteriorPower.ιMulti A n m) = h (exteriorPower.ιMulti A n m)) : g = h :=
  LinearMap.ext_on (exteriorPower.ιMulti_span A n M) (by rintro _ ⟨m, rfl⟩; exact H m)

theorem wedgeMap_apply_eq_self (φ : A →+* A) (hφ : φ = RingHom.id A) (f : M →ₛₗ[φ] M)
    (hf : ∀ x, f x = x) (ω : ⋀[A]^n M) : wedgeMap φ n f ω = ω := by
  subst hφ
  have : wedgeMap (RingHom.id A) n f = LinearMap.id :=
    wedge_ext _ n (fun m => by simp [hf])
  rw [this, LinearMap.id_apply]

theorem wedgeMap_comp_apply {C P : Type*} [CommRing C] [AddCommGroup P] [Module C P]
    (ψ : B →+* C) (χ : A →+* C) (hχ : ψ.comp φ = χ) (f : M →ₛₗ[φ] N) (g : N →ₛₗ[ψ] P)
    (h : M →ₛₗ[χ] P) (hh : ∀ x, g (f x) = h x) (ω : ⋀[A]^n M) :
    wedgeMap ψ n g (wedgeMap φ n f ω) = wedgeMap χ n h ω := by
  have : RingHomCompTriple φ ψ χ := ⟨hχ⟩
  have : (wedgeMap ψ n g).comp (wedgeMap φ n f) = wedgeMap χ n h :=
    wedge_ext χ n (fun m => by simp only [LinearMap.comp_apply, wedgeMap_ιMulti, hh])
  exact LinearMap.congr_fun this ω

/-- A semilinear map, seen as a morphism into the restriction of scalars. -/
noncomputable def toRestrict {P Q : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q]
    [Module B Q] (g : P →ₛₗ[φ] Q) :
    ModuleCat.of A P ⟶ (ModuleCat.restrictScalars φ).obj (ModuleCat.of B Q) :=
  ModuleCat.ofHom (X := ModuleCat.of A P)
    (Y := (ModuleCat.restrictScalars φ).obj (ModuleCat.of B Q))
    (show P →ₗ[A] ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B Q)) from
      { toFun := g
        map_add' := g.map_add
        map_smul' := g.map_smulₛₗ })

@[simp]
theorem toRestrict_apply {P Q : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q]
    [Module B Q] (g : P →ₛₗ[φ] Q) (p : P) : (toRestrict φ g).hom p = g p := rfl

end Module

section Presheaf

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (n : ℕ)

theorem map_id_apply' (X : Cᵒᵖ) (x : M.obj X) : (M.map (𝟙 X)).hom x = x := by
  rw [M.map_id]
  rfl

/-- The restriction maps of the exterior power presheaf, as semilinear maps. -/
noncomputable def wedgeRes {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ⋀[R.obj X]^n (M.obj X) →ₛₗ[(R.map f).hom] ⋀[R.obj Y]^n (M.obj Y) :=
  wedgeMap (R.map f).hom n (M.restrictₛₗ f)

/-- The restriction maps of the exterior power presheaf. -/
noncomputable def wedgePresheafMap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ModuleCat.of (R.obj X) (⋀[R.obj X]^n (M.obj X)) ⟶
      (ModuleCat.restrictScalars (R.map f).hom).obj
        (ModuleCat.of (R.obj Y) (⋀[R.obj Y]^n (M.obj Y))) :=
  toRestrict (R.map f).hom (wedgeMap (R.map f).hom n (M.restrictₛₗ f))

theorem wedgePresheafMap_ιMulti {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : Fin n → M.obj X) :
    (wedgePresheafMap M n f).hom (exteriorPower.ιMulti _ n m) =
      exteriorPower.ιMulti _ n (fun i => (M.map f).hom (m i)) := by
  rw [wedgePresheafMap, toRestrict_apply]
  exact wedgeMap_ιMulti _ n _ m

theorem wedgePresheafMap_id (X : Cᵒᵖ) (ω : ⋀[R.obj X]^n (M.obj X)) :
    (wedgePresheafMap M n (𝟙 X)).hom ω = ω := by
  rw [wedgePresheafMap, toRestrict_apply]
  exact wedgeMap_apply_eq_self n _ (by rw [R.map_id]; rfl) _ (fun x => map_id_apply' M X x) ω

theorem wedgePresheafMap_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (ω : ⋀[R.obj X]^n (M.obj X)) :
    (wedgePresheafMap M n g).hom ((wedgePresheafMap M n f).hom ω) =
      (wedgePresheafMap M n (f ≫ g)).hom ω := by
  rw [wedgePresheafMap, wedgePresheafMap, wedgePresheafMap, toRestrict_apply, toRestrict_apply,
    toRestrict_apply]
  exact wedgeMap_comp_apply _ n _ _ (by rw [R.map_comp]; rfl) _ _ _
    (fun x => (PresheafOfModules.map_comp_apply M f g x).symm) ω

/-- The exterior power presheaf `U ↦ ⋀^n_{R(U)} M(U)` of a presheaf of modules. -/
noncomputable def wedgePresheaf : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) where
  obj X := ModuleCat.of (R.obj X) (⋀[R.obj X]^n (M.obj X))
  map f := wedgePresheafMap M n f
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact wedgePresheafMap_id M n X ω
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    exact (wedgePresheafMap_comp M n f g ω).symm

@[simp]
theorem wedgePresheaf_map {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (wedgePresheaf M n).map f = wedgePresheafMap M n f := rfl

end Presheaf

section Stalk

open Opposite TopCat.Presheaf

variable {X : TopCat.{u}} {R : TopCat.Presheaf CommRingCat.{u} X}
  (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (n : ℕ) (x : X)

/-- The germ map of a presheaf of modules, semilinear along the germ map of the rings. -/
noncomputable def germₛₗ (U : Opens X) (hx : x ∈ U) :
    M.obj (op U) →ₛₗ[(R.germ U x hx).hom]
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) M.presheaf x where
  toFun m := TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X) M.presheaf U x hx m
  map_add' a b := map_add _ a b
  map_smul' r m := PresheafOfModules.germ_smul M x U hx r m

theorem germₛₗ_apply (U : Opens X) (hx : x ∈ U) (m : M.obj (op U)) :
    germₛₗ M x U hx m =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X) M.presheaf U x hx m := rfl

theorem germₛₗ_res {U V : Opens X} (i : V ⟶ U) (hx : x ∈ V) (m : M.obj (op U)) :
    germₛₗ M x V hx (M.map i.op m) = germₛₗ M x U (leOfHom i hx) m := by
  exact TopCat.Presheaf.germ_res_apply M.presheaf i x hx m

/-- The map `⋀^n_{R(U)} M(U) → ⋀^n_{R_x} M_x` induced by the germ maps. -/
noncomputable def wedgeGerm (U : Opens X) (hx : x ∈ U) :
    ⋀[R.obj (op U)]^n (M.obj (op U)) →ₛₗ[(R.germ U x hx).hom]
      ⋀[R.stalk x]^n (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) M.presheaf x) :=
  wedgeMap _ n (germₛₗ M x U hx)

theorem wedgeGerm_ιMulti (U : Opens X) (hx : x ∈ U) (s : Fin n → M.obj (op U)) :
    wedgeGerm M n x U hx (exteriorPower.ιMulti _ n s) =
      exteriorPower.ιMulti _ n (fun i => germₛₗ M x U hx (s i)) :=
  wedgeMap_ιMulti _ n _ s

theorem wedgeGerm_res {U V : Opens X} (i : V ⟶ U) (hx : x ∈ V)
    (ω : ⋀[R.obj (op U)]^n (M.obj (op U))) :
    wedgeGerm M n x V hx (wedgeRes M n i.op ω) = wedgeGerm M n x U (leOfHom i hx) ω := by
  refine wedgeMap_comp_apply _ n _ _ ?_ _ _ _ (fun m => ?_) ω
  · ext r
    exact congrArg (fun f => f r) (congrArg CommRingCat.Hom.hom (R.germ_res i x hx))
  · rw [PresheafOfModules.restrictₛₗ_apply]
    exact germₛₗ_res M x i hx m

/-- The map from the stalk of the exterior power presheaf to `⋀^n_{R_x} M_x`. -/
noncomputable def stalkToWedgeHom :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) (wedgePresheaf M n).presheaf x ⟶
      AddCommGrpCat.of
        (⋀[R.stalk x]^n (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) M.presheaf x)) :=
  Limits.colimit.desc _
    { pt := _
      ι :=
        { app := fun U => AddCommGrpCat.ofHom (wedgeGerm M n x U.unop.1 U.unop.2).toAddMonoidHom
          naturality := fun U V i => by
            ext ω
            exact wedgeGerm_res M n x i.unop V.unop.2 ω } }

theorem stalkToWedgeHom_germ (U : Opens X) (hx : x ∈ U) (ω : ⋀[R.obj (op U)]^n (M.obj (op U))) :
    stalkToWedgeHom M n x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X) (wedgePresheaf M n).presheaf U x hx
          ω) = wedgeGerm M n x U hx ω :=
  by
  unfold stalkToWedgeHom
  erw [Limits.colimit.ι_desc_apply]
  rfl

theorem exists_rep
    (m : Fin n → TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) M.presheaf x) :
    ∃ (U : Opens X) (hx : x ∈ U) (s : Fin n → M.obj (op U)),
      ∀ i, germₛₗ M x U hx (s i) = m i := by
  choose U hU s hs using fun i => TopCat.Presheaf.exists_germ_eq M.presheaf (m i)
  let W : Opens X := ⟨⋂ i, (U i : Set X), isOpen_iInter_of_finite fun i => (U i).isOpen⟩
  have hW : x ∈ W := Set.mem_iInter.2 hU
  have hle : ∀ i, W ≤ U i := fun i => Set.iInter_subset _ i
  refine ⟨W, hW, fun i => M.map (homOfLE (hle i)).op (s i), fun i => ?_⟩
  exact (germₛₗ_res M x _ hW (s i)).trans (hs i)

theorem germ_ιMulti_eq {U V : Opens X} (hU : x ∈ U) (hV : x ∈ V) (s : Fin n → M.obj (op U))
    (t : Fin n → M.obj (op V)) (h : ∀ i, germₛₗ M x U hU (s i) = germₛₗ M x V hV (t i)) :
    germₛₗ (wedgePresheaf M n) x U hU (exteriorPower.ιMulti _ n s) =
      germₛₗ (wedgePresheaf M n) x V hV (exteriorPower.ιMulti _ n t) := by
  choose W hW iU iV hst using fun i =>
    TopCat.Presheaf.germ_eq M.presheaf x hU hV (s i) (t i) (h i)
  let W₀ : Opens X :=
    U ⊓ V ⊓ ⟨⋂ i, (W i : Set X), isOpen_iInter_of_finite fun i => (W i).isOpen⟩
  have hW₀ : x ∈ W₀ := ⟨⟨hU, hV⟩, Set.mem_iInter.2 hW⟩
  have hWU : W₀ ≤ U := inf_le_left.trans inf_le_left
  have hWV : W₀ ≤ V := inf_le_left.trans inf_le_right
  have hWi : ∀ i, W₀ ≤ W i := fun i => inf_le_right.trans (Set.iInter_subset _ i)
  have key : ∀ i, M.map (homOfLE hWU).op (s i) = M.map (homOfLE hWV).op (t i) := by
    intro i
    have e1 : homOfLE hWU = homOfLE (hWi i) ≫ iU i := Subsingleton.elim _ _
    have e2 : homOfLE hWV = homOfLE (hWi i) ≫ iV i := Subsingleton.elim _ _
    rw [e1, e2, op_comp, op_comp, PresheafOfModules.map_comp_apply,
      PresheafOfModules.map_comp_apply]
    exact congrArg _ ((PresheafOfModules.presheaf_map_apply_coe M (iU i).op (s i)).symm.trans
      ((hst i).trans (PresheafOfModules.presheaf_map_apply_coe M (iV i).op (t i))))
  calc germₛₗ (wedgePresheaf M n) x U hU (exteriorPower.ιMulti _ n s)
      = germₛₗ (wedgePresheaf M n) x W₀ hW₀
          ((wedgePresheaf M n).map (homOfLE hWU).op (exteriorPower.ιMulti _ n s)) :=
        (germₛₗ_res _ x (homOfLE hWU) hW₀ _).symm
    _ = germₛₗ (wedgePresheaf M n) x W₀ hW₀
          (exteriorPower.ιMulti _ n (fun i => M.map (homOfLE hWU).op (s i))) :=
        congrArg _ (wedgePresheafMap_ιMulti M n (homOfLE hWU).op s)
    _ = germₛₗ (wedgePresheaf M n) x W₀ hW₀
          (exteriorPower.ιMulti _ n (fun i => M.map (homOfLE hWV).op (t i))) :=
        congrArg _ (congrArg _ (funext key))
    _ = germₛₗ (wedgePresheaf M n) x W₀ hW₀
          ((wedgePresheaf M n).map (homOfLE hWV).op (exteriorPower.ιMulti _ n t)) :=
        congrArg _ (wedgePresheafMap_ιMulti M n (homOfLE hWV).op t).symm
    _ = germₛₗ (wedgePresheaf M n) x V hV (exteriorPower.ιMulti _ n t) :=
        germₛₗ_res _ x (homOfLE hWV) hW₀ _

theorem stalkToWedgeHom_germₛₗ (U : Opens X) (hx : x ∈ U)
    (ω : ⋀[R.obj (op U)]^n (M.obj (op U))) :
    stalkToWedgeHom M n x (germₛₗ (wedgePresheaf M n) x U hx ω) = wedgeGerm M n x U hx ω :=
  stalkToWedgeHom_germ M n x U hx ω

theorem germₛₗ_update [DecidableEq (Fin n)] {U : Opens X} (hU : x ∈ U)
    (t : Fin n → M.obj (op U))
    (m : Fin n → TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) M.presheaf x)
    (ht : ∀ j, germₛₗ M x U hU (t j) = m j) (i : Fin n) (v : M.obj (op U))
    (w : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) M.presheaf x)
    (hv : germₛₗ M x U hU v = w) (j : Fin n) :
    germₛₗ M x U hU (Function.update t i v j) = Function.update m i w j := by
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self, hv]
  · simp only [Function.update_of_ne hj, ht]

/-- The germ map of the exterior power presheaf, with its domain written as `⋀^n`. -/
noncomputable def wedgeStalkGerm (U : Opens X) (hx : x ∈ U) :
    ⋀[R.obj (op U)]^n (M.obj (op U)) →ₛₗ[(R.germ U x hx).hom]
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) (wedgePresheaf M n).presheaf x :=
  germₛₗ (wedgePresheaf M n) x U hx

/-- The germ of `ιMulti` of a chosen common representative of `m`. -/
noncomputable def wedgeToStalkFun
    (m : Fin n → TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) M.presheaf x) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) (wedgePresheaf M n).presheaf x :=
  wedgeStalkGerm M n x (exists_rep M n x m).choose (exists_rep M n x m).choose_spec.choose
    (exteriorPower.ιMulti _ n (exists_rep M n x m).choose_spec.choose_spec.choose)

theorem wedgeToStalkFun_eq
    (m : Fin n → TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) M.presheaf x)
    {V : Opens X} (hV : x ∈ V) (t : Fin n → M.obj (op V))
    (ht : ∀ i, germₛₗ M x V hV (t i) = m i) :
    wedgeToStalkFun M n x m = wedgeStalkGerm M n x V hV (exteriorPower.ιMulti _ n t) :=
  germ_ιMulti_eq M n x _ hV _ t
    (fun i => ((exists_rep M n x m).choose_spec.choose_spec.choose_spec i).trans (ht i).symm)

/-- The alternating map `M_x^n → (⋀^n M)_x` on germs of common representatives. -/
noncomputable def wedgeToStalkAlt :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) M.presheaf x [⋀^Fin n]→ₗ[R.stalk x]
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) (wedgePresheaf M n).presheaf x where
  toFun := wedgeToStalkFun M n x
  map_update_add' := by
    intro _ m i a b
    obtain ⟨U, hU, s, hs⟩ := exists_rep M n x m
    obtain ⟨Ua, hUa, sa, hsa⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf a
    obtain ⟨Ub, hUb, sb, hsb⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf b
    let W : Opens X := U ⊓ (Ua ⊓ Ub)
    have hW : x ∈ W := ⟨hU, hUa, hUb⟩
    let s' : Fin n → M.obj (op W) := fun j => M.map (homOfLE (inf_le_left : W ≤ U)).op (s j)
    let a' : M.obj (op W) := M.map (homOfLE (inf_le_right.trans inf_le_left : W ≤ Ua)).op sa
    let b' : M.obj (op W) := M.map (homOfLE (inf_le_right.trans inf_le_right : W ≤ Ub)).op sb
    have hs' : ∀ j, germₛₗ M x W hW (s' j) = m j := fun j => (germₛₗ_res M x _ hW _).trans (hs j)
    have ha' : germₛₗ M x W hW a' = a := (germₛₗ_res M x _ hW _).trans hsa
    have hb' : germₛₗ M x W hW b' = b := (germₛₗ_res M x _ hW _).trans hsb
    rw [wedgeToStalkFun_eq M n x _ hW (Function.update s' i (a' + b'))
        (germₛₗ_update M n x hW s' m hs' i _ _ (by rw [map_add, ha', hb'])),
      wedgeToStalkFun_eq M n x _ hW (Function.update s' i a')
        (germₛₗ_update M n x hW s' m hs' i _ _ ha'),
      wedgeToStalkFun_eq M n x _ hW (Function.update s' i b')
        (germₛₗ_update M n x hW s' m hs' i _ _ hb'),
      AlternatingMap.map_update_add, map_add]
  map_update_smul' := by
    intro _ m i r a
    obtain ⟨U, hU, s, hs⟩ := exists_rep M n x m
    obtain ⟨Ua, hUa, sa, hsa⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf a
    obtain ⟨Ur, hUr, sr, hsr⟩ := TopCat.Presheaf.exists_germ_eq R r
    let W : Opens X := U ⊓ (Ua ⊓ Ur)
    have hW : x ∈ W := ⟨hU, hUa, hUr⟩
    let s' : Fin n → M.obj (op W) := fun j => M.map (homOfLE (inf_le_left : W ≤ U)).op (s j)
    let a' : M.obj (op W) := M.map (homOfLE (inf_le_right.trans inf_le_left : W ≤ Ua)).op sa
    let r' : R.obj (op W) := R.map (homOfLE (inf_le_right.trans inf_le_right : W ≤ Ur)).op sr
    have hs' : ∀ j, germₛₗ M x W hW (s' j) = m j := fun j => (germₛₗ_res M x _ hW _).trans (hs j)
    have ha' : germₛₗ M x W hW a' = a := (germₛₗ_res M x _ hW _).trans hsa
    have hr' : (R.germ W x hW).hom r' = r :=
      (TopCat.Presheaf.germ_res_apply R _ x hW sr).trans hsr
    rw [wedgeToStalkFun_eq M n x _ hW (Function.update s' i (r' • a'))
        (germₛₗ_update M n x hW s' m hs' i _ _ (by rw [LinearMap.map_smulₛₗ, ha', hr'])),
      wedgeToStalkFun_eq M n x _ hW (Function.update s' i a')
        (germₛₗ_update M n x hW s' m hs' i _ _ ha'),
      AlternatingMap.map_update_smul, LinearMap.map_smulₛₗ, hr']
  map_eq_zero_of_eq' := by
    intro m i j hij hne
    obtain ⟨U, hU, s, hs⟩ := exists_rep M n x m
    obtain ⟨W, hW, iU, iV, he⟩ := TopCat.Presheaf.germ_eq M.presheaf x hU hU (s i) (s j)
      (((hs i).trans hij).trans (hs j).symm)
    have e : iU = iV := Subsingleton.elim _ _
    subst e
    let s' : Fin n → M.obj (op W) := fun k => M.map iU.op (s k)
    have hs' : ∀ k, germₛₗ M x W hW (s' k) = m k := fun k => (germₛₗ_res M x _ hW _).trans (hs k)
    have hsij : s' i = s' j :=
      ((PresheafOfModules.presheaf_map_apply_coe M iU.op (s i)).symm.trans he).trans
        (PresheafOfModules.presheaf_map_apply_coe M iU.op (s j))
    show wedgeToStalkFun M n x m = 0
    rw [wedgeToStalkFun_eq M n x m hW s' hs',
      (exteriorPower.ιMulti _ n).map_eq_zero_of_eq s' hsij hne, map_zero]

theorem wedgeStalkGerm_res {U V : Opens X} (i : V ⟶ U) (hx : x ∈ V)
    (ω : ⋀[R.obj (op U)]^n (M.obj (op U))) :
    wedgeStalkGerm M n x V hx (wedgeRes M n i.op ω) = wedgeStalkGerm M n x U (leOfHom i hx) ω :=
  germₛₗ_res (wedgePresheaf M n) x i hx ω

theorem stalkToWedgeHom_wedgeStalkGerm (U : Opens X) (hx : x ∈ U)
    (ω : ⋀[R.obj (op U)]^n (M.obj (op U))) :
    stalkToWedgeHom M n x (wedgeStalkGerm M n x U hx ω) = wedgeGerm M n x U hx ω :=
  stalkToWedgeHom_germ M n x U hx ω

/-- The `R_x`-linear map `⋀^n_{R_x} M_x → (⋀^n M)_x`. -/
noncomputable def wedgeToStalk :
    ⋀[R.stalk x]^n (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) M.presheaf x)
      →ₗ[R.stalk x]
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) (wedgePresheaf M n).presheaf x :=
  exteriorPower.alternatingMapLinearEquiv (wedgeToStalkAlt M n x)

theorem wedgeToStalk_ιMulti
    (m : Fin n → TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) M.presheaf x) :
    wedgeToStalk M n x (exteriorPower.ιMulti _ n m) = wedgeToStalkFun M n x m :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ m

theorem stalkToWedgeHom_smul (r : R.stalk x)
    (y : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) (wedgePresheaf M n).presheaf x) :
    stalkToWedgeHom M n x (r • y) = r • stalkToWedgeHom M n x y := by
  obtain ⟨U, hU, ω, hy⟩ := TopCat.Presheaf.exists_germ_eq (wedgePresheaf M n).presheaf y
  obtain ⟨V, hV, a, ha⟩ := TopCat.Presheaf.exists_germ_eq R r
  let W : Opens X := U ⊓ V
  have hW : x ∈ W := ⟨hU, hV⟩
  let ω' := wedgeRes M n (homOfLE (inf_le_left : W ≤ U)).op ω
  let a' : R.obj (op W) := R.map (homOfLE (inf_le_right : W ≤ V)).op a
  have hy' : wedgeStalkGerm M n x W hW ω' = y :=
    (wedgeStalkGerm_res M n x (homOfLE inf_le_left) hW ω).trans hy
  have ha' : (R.germ W x hW).hom a' = r := (TopCat.Presheaf.germ_res_apply R _ x hW a).trans ha
  rw [← hy', ← ha', ← LinearMap.map_smulₛₗ, stalkToWedgeHom_wedgeStalkGerm,
    stalkToWedgeHom_wedgeStalkGerm, LinearMap.map_smulₛₗ]

/-- The `R_x`-linear map `(⋀^n M)_x → ⋀^n_{R_x} M_x`. -/
noncomputable def stalkToWedge :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) (wedgePresheaf M n).presheaf x
      →ₗ[R.stalk x]
      ⋀[R.stalk x]^n (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) M.presheaf x) where
  toFun := stalkToWedgeHom M n x
  map_add' := map_add _
  map_smul' := stalkToWedgeHom_smul M n x

theorem stalkToWedge_comp_wedgeToStalk :
    (stalkToWedge M n x).comp (wedgeToStalk M n x) = LinearMap.id := by
  apply exteriorPower.linearMap_ext
  refine AlternatingMap.ext fun m => ?_
  obtain ⟨U, hU, s, hs⟩ := exists_rep M n x m
  rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    LinearMap.id_apply, wedgeToStalk_ιMulti, wedgeToStalkFun_eq M n x m hU s hs]
  refine (stalkToWedgeHom_wedgeStalkGerm M n x U hU _).trans ?_
  rw [wedgeGerm_ιMulti]
  exact congrArg _ (funext hs)

theorem wedgeToStalk_comp_stalkToWedge :
    (wedgeToStalk M n x).comp (stalkToWedge M n x) = LinearMap.id := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨U, hU, ω, hy⟩ := TopCat.Presheaf.exists_germ_eq (wedgePresheaf M n).presheaf y
  have hy' : wedgeStalkGerm M n x U hU ω = y := hy
  rw [← hy', LinearMap.comp_apply, LinearMap.id_apply]
  have key : (wedgeToStalk M n x).comp (wedgeGerm M n x U hU) = wedgeStalkGerm M n x U hU :=
    wedge_ext _ n fun s => by
      rw [LinearMap.comp_apply, wedgeGerm_ιMulti, wedgeToStalk_ιMulti]
      exact wedgeToStalkFun_eq M n x _ hU s (fun i => rfl)
  exact (congrArg (wedgeToStalk M n x) (stalkToWedgeHom_wedgeStalkGerm M n x U hU ω)).trans
    (LinearMap.congr_fun key ω)

/-- **The stalk of the exterior power presheaf.** For a presheaf of modules `M` over a presheaf
of commutative rings `R` on a topological space, `(⋀^n M)_x ≃ ⋀^n_{R_x} M_x`. -/
noncomputable def stalkWedgeEquiv :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) (wedgePresheaf M n).presheaf x
      ≃ₗ[R.stalk x]
      ⋀[R.stalk x]^n (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) M.presheaf x) :=
  LinearEquiv.ofLinearMap (stalkToWedge M n x) (wedgeToStalk M n x)
    (stalkToWedge_comp_wedgeToStalk M n x) (wedgeToStalk_comp_stalkToWedge M n x)

/-- The stalk equivalence sends the germ of `s₁ ∧ ⋯ ∧ sₙ` to the wedge of the germs. -/
theorem stalkWedgeEquiv_germ_ιMulti (U : Opens X) (hx : x ∈ U) (s : Fin n → M.obj (op U)) :
    stalkWedgeEquiv M n x (wedgeStalkGerm M n x U hx (exteriorPower.ιMulti _ n s)) =
      exteriorPower.ιMulti _ n (fun i => germₛₗ M x U hx (s i)) :=
  (stalkToWedgeHom_wedgeStalkGerm M n x U hx _).trans (wedgeGerm_ιMulti M n x U hx s)

end Stalk

section Sheaf

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R₀ : Cᵒᵖ ⥤ CommRingCat.{u}}
  {R : Sheaf J RingCat.{u}} (α : R₀ ⋙ forget₂ CommRingCat RingCat ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  (M : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)) (n : ℕ)

/-- The sheaf of modules associated to `U ↦ ⋀^n_{R₀(U)} M(U)`. -/
noncomputable def wedgeSheaf : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification α).obj (wedgePresheaf M n)

/-- The canonical map from the exterior power presheaf to its sheafification. -/
noncomputable def toWedgeSheaf : wedgePresheaf M n ⟶
    (PresheafOfModules.restrictScalars α).obj ((SheafOfModules.forget R).obj (wedgeSheaf α M n)) :=
  (PresheafOfModules.sheafificationAdjunction α).unit.app (wedgePresheaf M n)

end Sheaf

section SheafStalk

open Opposite

variable {X : TopCat.{u}} {R : TopCat.Presheaf CommRingCat.{u} X}
  {Rs : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  (α : R ⋙ forget₂ CommRingCat RingCat ⟶ Rs.obj)
  [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) α]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) α]
  (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (n : ℕ) (x : X)

theorem toPresheaf_map_toWedgeSheaf :
    (PresheafOfModules.toPresheaf _).map (toWedgeSheaf α M n) =
      toSheafify (Opens.grothendieckTopology X) (wedgePresheaf M n).presheaf :=
  PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app α _

/-- **The stalk of the sheafified exterior power.** The stalk at `x` of the sheafification of
`⋀^n M` is `⋀^n_{R_x} M_x`, as additive groups (see `stalkWedgeSheafEquiv_germ`). -/
noncomputable def stalkWedgeSheafEquiv :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) (wedgeSheaf α M n).val.presheaf x ≃+
      ⋀[R.stalk x]^n (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) M.presheaf x) :=
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
    (wedgePresheaf M n).presheaf
  (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X)
        (wedgePresheaf M n).presheaf))).symm.addCommGroupIsoToAddEquiv.trans
    (stalkWedgeEquiv M n x).toAddEquiv

/-- The sheaf stalk equivalence sends the germ of the image of `ω` to `ω` at `x`. -/
theorem stalkWedgeSheafEquiv_germ (U : Opens X) (hx : x ∈ U)
    (ω : ⋀[R.obj (op U)]^n (M.obj (op U))) :
    stalkWedgeSheafEquiv α M n x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X) (wedgeSheaf α M n).val.presheaf U x
          hx (((PresheafOfModules.toPresheaf _).map (toWedgeSheaf α M n)).app (op U) ω)) =
      wedgeGerm M n x U hx ω := by
  have h := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    (toSheafify (Opens.grothendieckTopology X) (wedgePresheaf M n).presheaf) ω
  rw [toPresheaf_map_toWedgeSheaf]
  erw [← h]
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
    (wedgePresheaf M n).presheaf
  show stalkWedgeEquiv M n x ((asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) (wedgePresheaf M n).presheaf))).inv
    ((asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) (wedgePresheaf M n).presheaf))).hom
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X) (wedgePresheaf M n).presheaf U x hx
        ω))) = _
  exact (congrArg (stalkWedgeEquiv M n x) (Iso.hom_inv_id_apply _ _)).trans
    (stalkToWedgeHom_germ M n x U hx ω)

end SheafStalk

section Scheme

open AlgebraicGeometry

variable {X : Scheme.{u}} (M : PresheafOfModulesOfCommRing X.presheaf) (n : ℕ)

theorem isLocallyInjective_ringCatSheaf :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) (𝟙 X.ringCatSheaf.obj) :=
  inferInstance

theorem isLocallySurjective_ringCatSheaf :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) (𝟙 X.ringCatSheaf.obj) :=
  inferInstance

/-- The `𝒪_X`-module `⋀^n M` on a scheme: the sheafification of `U ↦ ⋀^n_{Γ(X, U)} M(U)`.
Applied to the presheaf of relative Kähler differentials it gives `Ω^n`. -/
noncomputable def schemeWedge : X.Modules :=
  @wedgeSheaf _ _ _ X.presheaf X.ringCatSheaf (𝟙 _) isLocallyInjective_ringCatSheaf
    isLocallySurjective_ringCatSheaf _ _ M n

/-- The stalk of `⋀^n M` on a scheme at `x` is `⋀^n` over `𝒪_{X,x}` of the stalk of `M`. -/
noncomputable def schemeWedgeStalkEquiv (x : X) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toPresheafedSpace)
        (schemeWedge M n).val.presheaf x ≃+
      ⋀[X.presheaf.stalk x]^n
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toPresheafedSpace) M.presheaf x) :=
  @stalkWedgeSheafEquiv _ X.presheaf X.ringCatSheaf (𝟙 _) isLocallyInjective_ringCatSheaf
    isLocallySurjective_ringCatSheaf M n x

theorem schemeWedgeStalkEquiv_germ (x : X) (U : X.Opens) (hx : x ∈ U)
    (ω : ⋀[Γ(X, U)]^n (M.obj (Opposite.op U))) :
    schemeWedgeStalkEquiv M n x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X.toPresheafedSpace)
          (schemeWedge M n).val.presheaf U x hx
          (((PresheafOfModules.toPresheaf _).map
            (@toWedgeSheaf _ _ _ X.presheaf X.ringCatSheaf (𝟙 _) isLocallyInjective_ringCatSheaf
              isLocallySurjective_ringCatSheaf _ _ M n)).app (Opposite.op U) ω)) =
      wedgeGerm M n x U hx ω :=
  @stalkWedgeSheafEquiv_germ _ X.presheaf X.ringCatSheaf (𝟙 _) isLocallyInjective_ringCatSheaf
    isLocallySurjective_ringCatSheaf M n x U hx ω

end Scheme

end ZInQ.HeightModelM5

