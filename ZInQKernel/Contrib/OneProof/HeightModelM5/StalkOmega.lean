import Mathlib
import ZInQKernel.Contrib.OneProof.HeightModelM5.Defs

/-!
# The stalks of the sheaf of relative differentials

For `f : X ⟶ Spec R` and a point `x : X` we prove the stalk formula
`(Ω¹_{X/R})_x ≃ₗ Ω[𝒪_{X,x}⁄R]`, sending the germ of `dSheaf f U b` to `D (germ b)`.

The proof has two steps.
* The stalk of the sheafification is the stalk of the presheaf
  (`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`), and the comparison map is linear
  over the local ring.
* The stalk of the presheaf `U ↦ Ω[Γ(X, U)⁄R]` is `Ω[𝒪_{X,x}⁄R]`: the maps
  `Ω[Γ(X, U)⁄R] → Ω[𝒪_{X,x}⁄R]` induced by the germs descend to the stalk, and the derivation
  `germ b ↦ germ (d b)` of `𝒪_{X,x}` gives the inverse through the universal property of
  Kähler differentials.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace ZInQ.HeightModelM5

/-! ## Descending maps to stalks -/

namespace S1

section Helpers

variable {X : TopCat.{u}} (x : X)
variable {C₁ : Type*} [Category.{u} C₁] [Limits.HasColimits C₁] {FC₁ : C₁ → C₁ → Type*}
  {CC₁ : C₁ → Type u} [∀ A B, FunLike (FC₁ A B) (CC₁ A) (CC₁ B)] [ConcreteCategory C₁ FC₁]
  [Limits.PreservesFilteredColimits (forget C₁)]
variable {C₂ : Type*} [Category.{u} C₂] [Limits.HasColimits C₂] {FC₂ : C₂ → C₂ → Type*}
  {CC₂ : C₂ → Type u} [∀ A B, FunLike (FC₂ A B) (CC₂ A) (CC₂ B)] [ConcreteCategory C₂ FC₂]
  [Limits.PreservesFilteredColimits (forget C₂)]

/-- Two elements of stalks of two presheaves are germs of sections over one open set. -/
lemma exists_common_germ (F : X.Presheaf C₁) (G : X.Presheaf C₂) (s : ToType (F.stalk x))
    (t : ToType (G.stalk x)) :
    ∃ (U : Opens X) (hx : x ∈ U) (a : ToType (F.obj (op U))) (b : ToType (G.obj (op U))),
      F.germ U x hx a = s ∧ G.germ U x hx b = t := by
  obtain ⟨U, hU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq F s
  obtain ⟨V, hV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq G t
  refine ⟨U ⊓ V, ⟨hU, hV⟩, F.map (homOfLE inf_le_left).op a, G.map (homOfLE inf_le_right).op b,
    ?_, ?_⟩
  · exact TopCat.Presheaf.germ_res_apply F _ x _ a
  · exact TopCat.Presheaf.germ_res_apply G _ x _ b

/-- A family of maps on sections compatible with restriction, descended to the stalk. -/
noncomputable def stalkLift (F : X.Presheaf C₁) {T : Type*}
    (g : ∀ U : Opens X, x ∈ U → ToType (F.obj (op U)) → T) (t : ToType (F.stalk x)) : T :=
  g _ (TopCat.Presheaf.exists_germ_eq F t).choose_spec.choose
    (TopCat.Presheaf.exists_germ_eq F t).choose_spec.choose_spec.choose

lemma stalkLift_germ (F : X.Presheaf C₁) {T : Type*}
    (g : ∀ U : Opens X, x ∈ U → ToType (F.obj (op U)) → T)
    (hg : ∀ (U V : Opens X) (i : V ⟶ U) (hV : x ∈ V) (hU : x ∈ U) (s : ToType (F.obj (op U))),
      g V hV (F.map i.op s) = g U hU s)
    (U : Opens X) (hx : x ∈ U) (s : ToType (F.obj (op U))) :
    stalkLift x F g (F.germ U x hx s) = g U hx s := by
  have h := (TopCat.Presheaf.exists_germ_eq F (F.germ U x hx s)).choose_spec.choose_spec.choose_spec
  obtain ⟨W, hW, i₁, i₂, e⟩ := TopCat.Presheaf.germ_eq F x _ hx _ s h
  unfold stalkLift
  rw [← hg _ W i₁ hW, e, hg]

end Helpers

end S1

/-! ## The stalk of the sheafification -/

section Sheafification

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (x : X)

/-- The stalk of the presheaf `U ↦ Ω[Γ(X, U)⁄R]`. -/
noncomputable abbrev stalkPre : Type u :=
  ↑(TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.toPresheafedSpace.carrier) (preOmega f).presheaf x)

/-- The map of stalks induced by the unit of sheafification. -/
noncomputable def stalkUnit :
    TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.toPresheafedSpace.carrier) (preOmega f).presheaf x
      ⟶ TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.toPresheafedSpace.carrier)
        (relOmega f).val.presheaf x :=
  (TopCat.Presheaf.stalkFunctor Ab.{u} x).map
    ((PresheafOfModules.toPresheaf _).map (unitOmega f))

instance isIso_stalkUnit : IsIso (stalkUnit f x) := by
  have h := PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
    (R := X.ringCatSheaf) (𝟙 _) (preOmega f)
  have key := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x Ab.{u}
    (preOmega f).presheaf
  unfold stalkUnit unitOmega
  erw [h]
  exact key

lemma stalkUnit_germ (U : X.Opens) (hx : x ∈ U) (m : (preOmega f).obj (op U)) :
    (stalkUnit f x).hom (TopCat.Presheaf.germ (preOmega f).presheaf U x hx m) =
      TopCat.Presheaf.germ (relOmega f).val.presheaf U x hx
        (((unitOmega f).app (op U)).hom m) := by
  unfold stalkUnit
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rfl

lemma stalkUnit_smul (r : X.presheaf.stalk x) (m : stalkPre f x) :
    (stalkUnit f x).hom (r • m) = r • (stalkUnit f x).hom m := by
  obtain ⟨U, hx, a, n, rfl, rfl⟩ :=
    S1.exists_common_germ x X.presheaf (preOmega f).presheaf r m
  erw [← PresheafOfModules.germ_smul, stalkUnit_germ, stalkUnit_germ]
  erw [map_smul]
  exact germ_smul_stalkOmega f x U hx a _

/-- The stalk of the sheafification is the stalk of the presheaf, linearly over `𝒪_{X,x}`. -/
noncomputable def stalkUnitEquiv : stalkPre f x ≃ₗ[X.presheaf.stalk x] stalkOmega f x :=
  { (asIso (stalkUnit f x)).addCommGroupIsoToAddEquiv with
    map_smul' := stalkUnit_smul f x }

lemma stalkUnitEquiv_germ (U : X.Opens) (hx : x ∈ U) (m : (preOmega f).obj (op U)) :
    stalkUnitEquiv f x (TopCat.Presheaf.germ (preOmega f).presheaf U x hx m) =
      TopCat.Presheaf.germ (relOmega f).val.presheaf U x hx
        (((unitOmega f).app (op U)).hom m) :=
  stalkUnit_germ f x U hx m

end Sheafification

/-! ## The stalk of the presheaf of differentials -/

namespace S1

section Kaehler

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (x : X)

lemma baseHom_germ (U : X.Opens) (hx : x ∈ U) :
    (baseHom f).app (op U) ≫ X.presheaf.germ U x hx =
      (Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial := by
  simp only [baseHom, Category.assoc, TopCat.Presheaf.germ_res]

lemma algebraMap_stalk_eq (U : X.Opens) (hx : x ∈ U) (r : R) :
    letI := stalkAlgebra f x
    algebraMap R (X.presheaf.stalk x) r =
      (X.presheaf.germ U x hx).hom ((baseHom f).app (op U) r) := by
  change _ = ((baseHom f).app (op U) ≫ X.presheaf.germ U x hx).hom r
  rw [baseHom_germ]
  rfl

/-- The `R`-algebra structure on `Γ(X, U)`. -/
noncomputable abbrev algU (U : X.Opens) : Algebra R Γ(X, U) :=
  ((baseHom f).app (op U)).hom.toAlgebra

/-- The `Γ(X, U)`-algebra structure on the stalk at a point of `U`. -/
noncomputable abbrev algGerm (U : X.Opens) (hx : x ∈ U) : Algebra Γ(X, U) (X.presheaf.stalk x) :=
  (X.presheaf.germ U x hx).hom.toAlgebra

lemma isScalarTower_germ (U : X.Opens) (hx : x ∈ U) :
    letI := stalkAlgebra f x
    letI := algU f U
    letI := algGerm x U hx
    IsScalarTower R Γ(X, U) (X.presheaf.stalk x) :=
  letI := stalkAlgebra f x
  letI := algU f U
  letI := algGerm x U hx
  IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (baseHom_germ f x U hx)).symm

/-- The map `Ω[Γ(X, U)⁄R] → Ω[𝒪_{X,x}⁄R]` induced by the germ. -/
noncomputable def psiU (U : X.Opens) (hx : x ∈ U) :
    letI := stalkAlgebra f x
    (preOmega f).obj (op U) →+ Ω[X.presheaf.stalk x⁄R] :=
  letI := stalkAlgebra f x
  letI := algU f U
  letI := algGerm x U hx
  haveI := isScalarTower_germ f x U hx
  (KaehlerDifferential.map R R Γ(X, U) (X.presheaf.stalk x)).toAddMonoidHom

lemma psiU_d (U : X.Opens) (hx : x ∈ U) (b : Γ(X, U)) :
    letI := stalkAlgebra f x
    psiU f x U hx ((dPre f).d b) =
      KaehlerDifferential.D R (X.presheaf.stalk x) ((X.presheaf.germ U x hx).hom b) :=
  letI := stalkAlgebra f x
  letI := algU f U
  letI := algGerm x U hx
  haveI := isScalarTower_germ f x U hx
  KaehlerDifferential.map_D R R Γ(X, U) (X.presheaf.stalk x) b

lemma psiU_smul (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) (ω : (preOmega f).obj (op U)) :
    letI := stalkAlgebra f x
    psiU f x U hx (a • ω) = (X.presheaf.germ U x hx).hom a • psiU f x U hx ω := by
  let := stalkAlgebra f x
  let := algU f U
  let := algGerm x U hx
  have := isScalarTower_germ f x U hx
  exact ((KaehlerDifferential.map R R Γ(X, U) (X.presheaf.stalk x)).map_smul a ω).trans
    (algebraMap_smul (X.presheaf.stalk x) a _).symm

/-- Restriction of differentials, as an additive map. -/
noncomputable def resP {U V : X.Opens} (i : V ⟶ U) :
    (preOmega f).obj (op U) →+ (preOmega f).obj (op V) :=
  ((preOmega f).presheaf.map i.op).hom

/-- The universal derivation on sections, as an additive map. -/
noncomputable def dP (U : X.Opens) : Γ(X, U) →+ (preOmega f).obj (op U) :=
  (dPre f).d

/-- The germ map of the presheaf of differentials, as an additive map. -/
noncomputable def germP (U : X.Opens) (hx : x ∈ U) : (preOmega f).obj (op U) →+ stalkPre f x :=
  (TopCat.Presheaf.germ (preOmega f).presheaf U x hx).hom

lemma resP_smul {U V : X.Opens} (i : V ⟶ U) (a : Γ(X, U)) (ω : (preOmega f).obj (op U)) :
    resP f i (a • ω) = X.presheaf.map i.op a • resP f i ω :=
  PresheafOfModules.map_smul (preOmega f) i.op a ω

lemma resP_dP {U V : X.Opens} (i : V ⟶ U) (b : Γ(X, U)) :
    resP f i (dP f U b) = dP f V (X.presheaf.map i.op b) :=
  ((dPre f).d_map i.op b).symm

lemma dP_mul (U : X.Opens) (a b : Γ(X, U)) : dP f U (a * b) = a • dP f U b + b • dP f U a :=
  (dPre f).d_mul a b

lemma germP_resP {U V : X.Opens} (i : V ⟶ U) (hV : x ∈ V) (hU : x ∈ U)
    (ω : (preOmega f).obj (op U)) : germP f x V hV (resP f i ω) = germP f x U hU ω :=
  TopCat.Presheaf.germ_res_apply (preOmega f).presheaf i x hV ω

lemma germP_smul (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) (ω : (preOmega f).obj (op U)) :
    germP f x U hx (a • ω) = (X.presheaf.germ U x hx).hom a • germP f x U hx ω :=
  PresheafOfModules.germ_smul (preOmega f) x U hx a ω

lemma psiU_res {U V : X.Opens} (i : V ⟶ U) (hV : x ∈ V) (hU : x ∈ U)
    (ω : (preOmega f).obj (op U)) :
    psiU f x V hV (resP f i ω) = psiU f x U hU ω := by
  let := stalkAlgebra f x
  let := algU f U
  have hω : ω ∈ Submodule.span Γ(X, U) (Set.range (KaehlerDifferential.D R Γ(X, U))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨b, rfl⟩ := h
    have e := resP_dP f i b
    have e₁ := psiU_d f x V hV (X.presheaf.map i.op b)
    have e₂ := psiU_d f x U hU b
    have e₃ := TopCat.Presheaf.germ_res_apply X.presheaf i x hV b
    exact (congrArg (psiU f x V hV) e).trans (e₁.trans (e₃ ▸ e₂.symm))
  | zero => rw [map_zero, map_zero, map_zero]
  | add _ _ _ _ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | smul a ω _ h =>
    have e₁ := congrArg (psiU f x V hV) (resP_smul f i a ω)
    have e₂ := psiU_smul f x V hV (X.presheaf.map i.op a) (resP f i ω)
    have e₃ := psiU_smul f x U hU a ω
    rw [h, TopCat.Presheaf.germ_res_apply] at e₂
    exact e₁.trans (e₂.trans e₃.symm)

/-- The map from the stalk of the presheaf of differentials to `Ω[𝒪_{X,x}⁄R]`. -/
noncomputable def psiFun :
    letI := stalkAlgebra f x
    stalkPre f x → Ω[X.presheaf.stalk x⁄R] :=
  stalkLift x (preOmega f).presheaf (fun U hx ω ↦ psiU f x U hx ω)

lemma psiFun_germ (U : X.Opens) (hx : x ∈ U) (ω : (preOmega f).obj (op U)) :
    psiFun f x (germP f x U hx ω) = psiU f x U hx ω := by
  have hg : ∀ (U V : X.Opens) (i : V ⟶ U) (hV : x ∈ V) (hU : x ∈ U)
      (s : (preOmega f).obj (op U)), psiU f x V hV (resP f i s) = psiU f x U hU s :=
    fun _ _ i hV hU s ↦ psiU_res f x i hV hU s
  have h := stalkLift_germ x (preOmega f).presheaf (fun U hx ω ↦ psiU f x U hx ω) hg U hx ω
  exact h

/-- The stalk of the presheaf of differentials maps linearly to `Ω[𝒪_{X,x}⁄R]`. -/
noncomputable def psiLin :
    letI := stalkAlgebra f x
    stalkPre f x →ₗ[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R] :=
  letI := stalkAlgebra f x
  { toFun := psiFun f x
    map_add' := fun s t ↦ by
      obtain ⟨U, hx, a, b, rfl, rfl⟩ :=
        exists_common_germ x (preOmega f).presheaf (preOmega f).presheaf s t
      refine (congrArg (psiFun f x) ((germP f x U hx).map_add a b).symm).trans ?_
      exact (psiFun_germ f x U hx (a + b)).trans
        (((psiU f x U hx).map_add a b).trans
          (congrArg₂ (· + ·) (psiFun_germ f x U hx a).symm (psiFun_germ f x U hx b).symm))
    map_smul' := fun r t ↦ by
      obtain ⟨U, hx, a, n, rfl, rfl⟩ :=
        exists_common_germ x X.presheaf (preOmega f).presheaf r t
      have e := germP_smul f x U hx a n
      exact (congrArg (psiFun f x) e.symm).trans ((psiFun_germ f x U hx _).trans
        ((psiU_smul f x U hx a n).trans (congrArg _ (psiFun_germ f x U hx n).symm))) }

lemma psiLin_germ (U : X.Opens) (hx : x ∈ U) (ω : (preOmega f).obj (op U)) :
    psiLin f x (germP f x U hx ω) = psiU f x U hx ω :=
  psiFun_germ f x U hx ω

/-- The derivation `germ b ↦ germ (d b)` from `𝒪_{X,x}` to the stalk of the presheaf. -/
noncomputable def deltaFun : X.presheaf.stalk x → stalkPre f x :=
  stalkLift x X.presheaf (fun U hx b ↦ germP f x U hx (dP f U b))

lemma deltaFun_germ (U : X.Opens) (hx : x ∈ U) (b : Γ(X, U)) :
    deltaFun f x ((X.presheaf.germ U x hx).hom b) = germP f x U hx (dP f U b) := by
  refine stalkLift_germ x X.presheaf _ (fun U V i hV hU b ↦ ?_) U hx b
  exact (congrArg (germP f x V hV) (resP_dP f i b).symm).trans (germP_resP f x i hV hU _)

lemma deltaFun_add (s t : X.presheaf.stalk x) :
    deltaFun f x (s + t) = deltaFun f x s + deltaFun f x t := by
  obtain ⟨U, hx, a, b, rfl, rfl⟩ := exists_common_germ x X.presheaf X.presheaf s t
  rw [← map_add, deltaFun_germ, deltaFun_germ, deltaFun_germ, map_add, map_add]

lemma deltaFun_mul (s t : X.presheaf.stalk x) :
    deltaFun f x (s * t) = s • deltaFun f x t + t • deltaFun f x s := by
  obtain ⟨U, hx, a, b, rfl, rfl⟩ := exists_common_germ x X.presheaf X.presheaf s t
  rw [← map_mul, deltaFun_germ, deltaFun_germ, deltaFun_germ, dP_mul, map_add, germP_smul,
    germP_smul]

lemma deltaFun_algebraMap (r : R) :
    letI := stalkAlgebra f x
    deltaFun f x (algebraMap R (X.presheaf.stalk x) r) = 0 := by
  let := stalkAlgebra f x
  have e := deltaFun_germ f x ⊤ trivial ((baseHom f).app (op ⊤) r)
  have e₀ : dP f ⊤ ((baseHom f).app (op ⊤) r) = 0 :=
    PresheafOfModulesOfCommRing.Derivation'.d_app (dPre f) (X := op ⊤) r
  rw [algebraMap_stalk_eq f x ⊤ trivial]
  exact e.trans ((congrArg _ e₀).trans (map_zero _))

end Kaehler

section FormulaAux

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (x : X)

/-- The `R`-module structure on the stalk of the presheaf, through `𝒪_{X,x}`. -/
noncomputable abbrev moduleStalkPre : Module R (stalkPre f x) :=
  letI := stalkAlgebra f x
  Module.compHom (stalkPre f x) (algebraMap R (X.presheaf.stalk x))

lemma isScalarTower_stalkPre :
    letI := stalkAlgebra f x
    letI := moduleStalkPre f x
    IsScalarTower R (X.presheaf.stalk x) (stalkPre f x) :=
  letI := stalkAlgebra f x
  letI := moduleStalkPre f x
  ⟨fun r s m ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩

/-- The derivation `germ b ↦ germ (d b)`. -/
noncomputable def deltaDer :
    letI := stalkAlgebra f x
    letI := moduleStalkPre f x
    Derivation R (X.presheaf.stalk x) (stalkPre f x) :=
  letI := stalkAlgebra f x
  letI := moduleStalkPre f x
  Derivation.mk'
    { toFun := deltaFun f x
      map_add' := deltaFun_add f x
      map_smul' := fun r s ↦ by
        rw [Algebra.smul_def, deltaFun_mul, deltaFun_algebraMap, smul_zero, add_zero]
        rfl }
    (deltaFun_mul f x)

/-- The inverse map `Ω[𝒪_{X,x}⁄R] → (stalk of the presheaf)`. -/
noncomputable def chiLin :
    letI := stalkAlgebra f x
    Ω[X.presheaf.stalk x⁄R] →ₗ[X.presheaf.stalk x] stalkPre f x :=
  letI := stalkAlgebra f x
  letI := moduleStalkPre f x
  haveI := isScalarTower_stalkPre f x
  (deltaDer f x).liftKaehlerDifferential

lemma chiLin_D (s : X.presheaf.stalk x) :
    letI := stalkAlgebra f x
    chiLin f x (KaehlerDifferential.D R (X.presheaf.stalk x) s) = deltaFun f x s := by
  let := stalkAlgebra f x
  let := moduleStalkPre f x
  have := isScalarTower_stalkPre f x
  exact (deltaDer f x).liftKaehlerDifferential_comp_D s

lemma psiLin_chiLin :
    letI := stalkAlgebra f x
    (psiLin f x).comp (chiLin f x) = LinearMap.id := by
  let := stalkAlgebra f x
  refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun s ↦ ?_)
  obtain ⟨U, hx, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf s
  exact (congrArg (psiLin f x) ((chiLin_D f x _).trans (deltaFun_germ f x U hx b))).trans
    ((psiLin_germ f x U hx _).trans (psiU_d f x U hx b))

lemma chiLin_psiU (U : X.Opens) (hx : x ∈ U) (ω : (preOmega f).obj (op U)) :
    chiLin f x (psiU f x U hx ω) = germP f x U hx ω := by
  let := stalkAlgebra f x
  let := algU f U
  have hω : ω ∈ Submodule.span Γ(X, U) (Set.range (KaehlerDifferential.D R Γ(X, U))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨b, rfl⟩ := h
    have e := psiU_d f x U hx b
    exact (congrArg (chiLin f x) e).trans ((chiLin_D f x _).trans (deltaFun_germ f x U hx b))
  | zero => rw [map_zero, map_zero, map_zero]
  | add _ _ _ _ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | smul a ω _ h =>
    have e₁ := psiU_smul f x U hx a ω
    have e₂ := germP_smul f x U hx a ω
    have e₃ : chiLin f x ((X.presheaf.germ U x hx).hom a • psiU f x U hx ω) =
        (X.presheaf.germ U x hx).hom a • chiLin f x (psiU f x U hx ω) := map_smul _ _ _
    exact (congrArg (chiLin f x) e₁).trans (e₃.trans ((congrArg _ h).trans e₂.symm))

lemma chiLin_psiLin :
    letI := stalkAlgebra f x
    (chiLin f x).comp (psiLin f x) = LinearMap.id := by
  let := stalkAlgebra f x
  refine LinearMap.ext fun t ↦ ?_
  obtain ⟨U, hx, ω, rfl⟩ := TopCat.Presheaf.exists_germ_eq (preOmega f).presheaf t
  exact (congrArg (chiLin f x) (psiLin_germ f x U hx ω)).trans (chiLin_psiU f x U hx ω)

/-- The stalk of the presheaf `U ↦ Ω[Γ(X, U)⁄R]` at `x` is `Ω[𝒪_{X,x}⁄R]`. -/
noncomputable def stalkPreEquiv :
    letI := stalkAlgebra f x
    stalkPre f x ≃ₗ[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R] :=
  letI := stalkAlgebra f x
  LinearEquiv.ofLinearMap (psiLin f x) (chiLin f x) (psiLin_chiLin f x) (chiLin_psiLin f x)

end FormulaAux

end S1

/-! ## The stalk formula -/

section Formula

open S1

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (x : X)

/-- The stalk formula: `(Ω¹_{X/R})_x ≃ₗ Ω[𝒪_{X,x}⁄R]`. -/
noncomputable def stalkOmegaEquiv :
    letI := stalkAlgebra f x
    stalkOmega f x ≃ₗ[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R] :=
  letI := stalkAlgebra f x
  (stalkUnitEquiv f x).symm.trans (stalkPreEquiv f x)

/-- The stalk formula sends the germ of `d b` to `D (germ b)`. -/
theorem stalkOmegaEquiv_germ_dSheaf (U : X.Opens) (hx : x ∈ U) (b : Γ(X, U)) :
    letI := stalkAlgebra f x
    stalkOmegaEquiv f x ((TopCat.Presheaf.germ (C := Ab) (X := X.toPresheafedSpace)
        (relOmega f).val.presheaf U x hx).hom (dSheaf f U b)) =
      KaehlerDifferential.D R (X.presheaf.stalk x) ((X.presheaf.germ U x hx).hom b) := by
  let := stalkAlgebra f x
  have e := stalkUnitEquiv_germ f x U hx (dP f U b)
  have e₂ : (stalkUnitEquiv f x).symm
      ((TopCat.Presheaf.germ (C := Ab) (X := X.toPresheafedSpace)
        (relOmega f).val.presheaf U x hx).hom (dSheaf f U b)) = germP f x U hx (dP f U b) :=
    (LinearEquiv.symm_apply_eq _).2 e.symm
  change stalkPreEquiv f x ((stalkUnitEquiv f x).symm _) = _
  rw [e₂]
  change psiLin f x _ = _
  rw [psiLin_germ]
  exact psiU_d f x U hx b

/-- S1 (canonical): `(Ω¹_{X/R})_x ≃ₗ Ω[𝒪_{X,x}⁄R]`, with `germ (d b) ↦ D (germ b)`. -/
def StalkOmegaFormulaCanonical : Prop :=
  ∀ x : X,
    letI : Algebra R (X.presheaf.stalk x) :=
      ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom.toAlgebra
    ∃ φ : stalkOmega f x ≃ₗ[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄R],
      ∀ (U : X.Opens) (hx : x ∈ U) (b : Γ(X, U)),
        φ ((TopCat.Presheaf.germ (C := Ab) (X := X.toPresheafedSpace) (relOmega f).val.presheaf
            U x hx).hom (dSheaf f U b)) =
          KaehlerDifferential.D R (X.presheaf.stalk x) ((X.presheaf.germ U x hx).hom b)

/-- The stalk formula S1 holds. -/
theorem stalkOmegaFormulaCanonical : StalkOmegaFormulaCanonical f :=
  fun x ↦ ⟨stalkOmegaEquiv f x, stalkOmegaEquiv_germ_dSheaf f x⟩

end Formula

end ZInQ.HeightModelM5
