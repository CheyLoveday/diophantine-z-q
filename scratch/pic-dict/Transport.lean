import ZInQKernel.Contrib.OneProof.PicDictionary
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FreeGeneratorPullback

/-! # pic-dict: transport of Mumford's formula along an automorphism (towards `WeilFormulaGalois`) -/

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

namespace PicDict.Transport

open Scheme.Modules

universe u

variable {X Y Z : Scheme.{u}}

/-- `𝒪 → (f ≫ h)_* 𝒪` is the composite of `𝒪 → h_* 𝒪 → h_* f_* 𝒪`. -/
lemma unitToPushforward_comp (f : X ⟶ Y) (h : Y ⟶ Z) :
    SheafOfModules.unitToPushforwardObjUnit (f ≫ h).toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom ≫
        (pushforward h).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          (pushforwardComp f h).hom.app (unit X) := by
  ext U x
  rfl

/-- **`pullbackObjUnitIso` is compatible with `pullbackComp`.** -/
lemma pullbackObjUnitIso_comp (f : X ⟶ Y) (h : Y ⟶ Z) :
    (pullbackComp f h).inv.app (unit Z) ≫ (Scheme.Modules.pullback f).map (pullbackObjUnitIso h).hom ≫
      (pullbackObjUnitIso f).hom = (pullbackObjUnitIso (f ≫ h)).hom := by
  haveI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  haveI : (SheafOfModules.pushforward h.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction h).isRightAdjoint
  haveI : (SheafOfModules.pushforward (f ≫ h).toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction (f ≫ h)).isRightAdjoint
  apply ((pullbackPushforwardAdjunction (f ≫ h)).homEquiv _ _).injective
  have hR : (pullbackPushforwardAdjunction (f ≫ h)).homEquiv _ _ (pullbackObjUnitIso (f ≫ h)).hom =
      SheafOfModules.unitToPushforwardObjUnit (f ≫ h).toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hf : (pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackObjUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hh : (pullbackPushforwardAdjunction h).homEquiv _ _ (pullbackObjUnitIso h).hom =
      SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [hR, unitToPushforward_comp]
  set adj₁ := (pullbackPushforwardAdjunction h).comp (pullbackPushforwardAdjunction f)
  set adj₂ := pullbackPushforwardAdjunction (f ≫ h)
  set Yf := (Scheme.Modules.pullback f).map (pullbackObjUnitIso h).hom ≫ (pullbackObjUnitIso f).hom
  have hc := conjugateEquiv_pullbackComp_inv f h
  have hu := unit_conjugateEquiv adj₁ adj₂ (pullbackComp f h).inv (unit Z)
  rw [hc] at hu
  have key : adj₂.homEquiv _ _ ((pullbackComp f h).inv.app (unit Z) ≫ Yf) =
      adj₁.homEquiv _ _ Yf ≫ (pushforwardComp f h).hom.app (unit X) := by
    rw [adj₂.homEquiv_unit, adj₁.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hu,
      Category.assoc, Category.assoc]
    congr 1
  rw [key, ← Category.assoc]
  refine congrArg (fun φ => φ ≫ (pushforwardComp f h).hom.app (unit X)) ?_
  rw [Adjunction.comp_homEquiv]
  show (pullbackPushforwardAdjunction h).homEquiv _ _ ((pullbackPushforwardAdjunction f).homEquiv _ _
    ((Scheme.Modules.pullback f).map (pullbackObjUnitIso h).hom ≫ (pullbackObjUnitIso f).hom)) = _
  rw [Adjunction.homEquiv_naturality_left, hf, Adjunction.homEquiv_naturality_right, hh]

end PicDict.Transport

namespace PicDict.Transport

open Scheme.Modules

universe v

variable {X Y Z W : Scheme.{v}}

lemma pullbackCongr_hom_app {f f' : X ⟶ Y} (e : f = f') (M : Y.Modules) :
    (pullbackCongr e).hom.app M = eqToHom (by rw [e]) := by
  subst e; rfl

/-- naturality of `pullbackComp` in the first variable -/
lemma eqToHom_comp_pullbackComp {f f' : X ⟶ Y} (e : f = f') (h : Y ⟶ Z) (M : Z.Modules)
    (p : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback h).obj M) =
      (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback h).obj M)) :
    eqToHom p ≫ (pullbackComp f' h).hom.app M =
      (pullbackComp f h).hom.app M ≫ eqToHom (by rw [e]) := by
  subst e; simp

/-- naturality of `pullbackComp` in the second variable -/
lemma map_eqToHom_comp_pullbackComp (f : X ⟶ Y) {h h' : Y ⟶ Z} (e : h = h') (M : Z.Modules)
    (p : (Scheme.Modules.pullback h).obj M = (Scheme.Modules.pullback h').obj M) :
    (Scheme.Modules.pullback f).map (eqToHom p) ≫ (pullbackComp f h').hom.app M =
      (pullbackComp f h).hom.app M ≫ eqToHom (by rw [e]) := by
  subst e; simp

/-- associativity of `pullbackComp`, on objects -/
lemma pullbackComp_assoc_app (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫
        (pullbackComp f (g ≫ h)).hom.app M =
      (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (pullbackComp (f ≫ g) h).hom.app M ≫ eqToHom (by rw [Category.assoc]) := by
  have H := congrArg (fun τ => τ.app M) (pseudofunctor_associativity f g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at H
  have H1 := (Iso.inv_comp_eq ((pullbackComp f (g ≫ h)).app M)).mp H
  have H2 := (Iso.inv_comp_eq ((Scheme.Modules.pullback f).mapIso ((pullbackComp g h).app M))).mp H1
  simp only [Functor.mapIso_hom, Iso.app_hom] at H2
  rw [← Category.assoc ((pullbackComp f g).hom.app _), H2]
  simp

end PicDict.Transport
