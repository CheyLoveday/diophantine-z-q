import Mathlib

/-!
# The sheaf of relative differentials of a scheme over an affine base

For a morphism of schemes `f : X ⟶ Spec R` we build the sheaf of relative differentials
`Ω¹_{X/R}` from Mathlib constructions: the presheaf `U ↦ Ω[Γ(X, U)⁄R]` of
`PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'`, sheafified by
`PresheafOfModules.sheafification` (Stacks 01UM). We also define its pullback along a section,
the global sections of that pullback, the stalks, and the differential `dSheaf`.

The basic API: `dSheaf` is additive, satisfies the Leibniz rule, kills the base ring, and is
compatible with restriction; the stalks carry their module structure over the local rings.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace ZInQ.HeightModelM5

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)

/-- The structure map `R ⟶ Γ(X, U)`, as a morphism from the constant presheaf. -/
noncomputable def baseHom : (Functor.const (TopologicalSpace.Opens X)ᵒᵖ).obj R ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.presheaf.map (homOfLE le_top).op
  naturality U V i := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc,
      ← Functor.map_comp]
    rfl

/-- The presheaf of modules `U ↦ Ω[Γ(X, U)⁄R]`. -/
noncomputable def preOmega : PresheafOfModulesOfCommRing X.presheaf :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' (baseHom f)

/-- `Ω¹_{X/R}`: the sheafification of `U ↦ Ω[Γ(X, U)⁄R]` (Stacks 01UM). -/
noncomputable def relOmega : X.Modules :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 _)).obj (preOmega f)

/-- The pullback `e*Ω¹_{X/R}` along a morphism `e : Spec R ⟶ X`. -/
noncomputable def pullOmega (e : Spec R ⟶ X) : (Spec R).Modules :=
  (Scheme.Modules.pullback e).obj (relOmega f)

/-- The global sections `Γ(Spec R, e*Ω¹_{X/R})`. -/
noncomputable def globalPullOmega (e : Spec R ⟶ X) : Ab :=
  ((Scheme.Modules.toPresheaf (Spec R)).obj (pullOmega f e)).obj (Opposite.op ⊤)

/-- The stalk of `Ω¹_{X/R}` at a point. -/
noncomputable abbrev stalkOmega (x : X) : Type u :=
  ↑(TopCat.Presheaf.stalk (C := Ab) (X := X.toPresheafedSpace) (relOmega f).val.presheaf x)

/-- The unit of sheafification, from the presheaf of differentials to `Ω¹_{X/R}`. -/
noncomputable def unitOmega : preOmega f ⟶ (PresheafOfModules.restrictScalars (𝟙 _)).obj
    ((SheafOfModules.forget X.ringCatSheaf).obj (relOmega f)) :=
  (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 _)).unit.app (preOmega f)

/-- The differential `d : Γ(X, U) → Γ(U, Ω¹_{X/R})`. -/
noncomputable def dSheaf (U : X.Opens) (b : Γ(X, U)) :
    ((relOmega f).val.presheaf.obj (Opposite.op U) : Type u) :=
  ((unitOmega f).app (Opposite.op U)).hom
    ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' (baseHom f)).d b)

/-- The `R`-algebra structure on a stalk of the structure sheaf. -/
noncomputable abbrev stalkAlgebra (x : X) : Algebra R (X.presheaf.stalk x) :=
  ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom.toAlgebra

/-! ## Basic API -/

/-- The universal derivation of the presheaf of differentials. -/
noncomputable abbrev dPre :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' (baseHom f)

lemma dSheaf_eq (U : X.Opens) (b : Γ(X, U)) :
    dSheaf f U b = ((unitOmega f).app (op U)).hom ((dPre f).d b) := rfl

/-- `Ω¹_{X/R}` as a presheaf of modules over the structure presheaf of commutative rings. -/
noncomputable abbrev relOmegaPre : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
  (relOmega f).val

lemma dSheaf_add (U : X.Opens) (a b : Γ(X, U)) :
    dSheaf f U (a + b) = dSheaf f U a + dSheaf f U b := by
  rw [dSheaf_eq, (dPre f).d.map_add]
  exact map_add _ _ _

lemma dSheaf_zero (U : X.Opens) : dSheaf f U 0 = 0 := by
  rw [dSheaf_eq, (dPre f).d.map_zero]
  exact map_zero _

lemma dSheaf_one (U : X.Opens) : dSheaf f U 1 = 0 := by
  rw [dSheaf_eq, (dPre f).d_one]
  exact map_zero _

lemma dSheaf_mul (U : X.Opens) (a b : Γ(X, U)) :
    (show (relOmegaPre f).obj (op U) from dSheaf f U (a * b)) =
      a • (show (relOmegaPre f).obj (op U) from dSheaf f U b) +
        b • (show (relOmegaPre f).obj (op U) from dSheaf f U a) := by
  dsimp only
  rw [dSheaf_eq, dSheaf_eq, dSheaf_eq, (dPre f).d_mul]
  erw [map_add, map_smul, map_smul]
  rfl

lemma dSheaf_baseHom (U : X.Opens) (r : R) :
    dSheaf f U ((baseHom f).app (op U) r) = 0 := by
  rw [dSheaf_eq]
  erw [PresheafOfModulesOfCommRing.Derivation'.d_app (dPre f) (X := op U) r]
  exact map_zero _

lemma dSheaf_map {U V : X.Opens} (i : V ⟶ U) (b : Γ(X, U)) :
    (relOmega f).val.presheaf.map i.op (dSheaf f U b) = dSheaf f V (X.presheaf.map i.op b) := by
  rw [dSheaf_eq, dSheaf_eq]
  erw [(dPre f).d_map i.op b]
  exact (PresheafOfModules.naturality_apply (unitOmega f) i.op ((dPre f).d b)).symm

/-- The stalk of `Ω¹_{X/R}` is a module over the local ring. -/
noncomputable instance moduleStalkOmega (x : X) :
    Module (X.presheaf.stalk x) (stalkOmega f x) :=
  inferInstanceAs (Module (X.presheaf.stalk x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.toPresheafedSpace.carrier)
      (relOmegaPre f).presheaf x))

lemma germ_smul_stalkOmega (x : X) (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U))
    (m : (relOmegaPre f).obj (op U)) :
    (TopCat.Presheaf.germ (C := Ab) (X := X.toPresheafedSpace) (relOmega f).val.presheaf
        U x hx).hom (a • m) =
      (X.presheaf.germ U x hx).hom a •
        ((TopCat.Presheaf.germ (C := Ab) (X := X.toPresheafedSpace) (relOmega f).val.presheaf
          U x hx).hom m : stalkOmega f x) := by
  exact PresheafOfModules.germ_smul (R := X.presheaf) (relOmegaPre f) x U hx a m

end ZInQ.HeightModelM5
