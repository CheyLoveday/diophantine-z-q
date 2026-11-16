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

lemma pullbackCongr_inv_app {f f' : X ⟶ Y} (e : f = f') (M : Y.Modules) :
    (pullbackCongr e).inv.app M = eqToHom (by rw [e]) := by
  subst e; rfl

lemma pullbackComp_assoc_inv₁ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).inv.app M) ≫
        (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
          (pullbackComp (f ≫ g) h).hom.app M =
      (pullbackComp f (g ≫ h)).hom.app M ≫ eqToHom (by rw [Category.assoc]) := by
  rw [← cancel_epi ((Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M)),
    ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    reassoc_of% (pullbackComp_assoc_app f g h M)]
  simp

lemma pullbackComp_assoc_inv₂ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫
          (pullbackComp f (g ≫ h)).hom.app M =
      (pullbackComp (f ≫ g) h).hom.app M ≫ eqToHom (by rw [Category.assoc]) := by
  rw [pullbackComp_assoc_app, Iso.inv_hom_id_app_assoc]

/-- `g^* m^* M ≅ m^* g^* M` for `g ≫ m = m ≫ g`. -/
def Qiso (g m : X ⟶ X) (hb : g ≫ m = m ≫ g) (M : X.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback m).obj M) ≅
      (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback g).obj M) :=
  (pullbackComp g m).app M ≪≫ (pullbackCongr hb).app M ≪≫ ((pullbackComp m g).app M).symm

/-- `t'^* g^* ≅ g^* t^*` for `t' ≫ g = g ≫ t`. -/
def Niso (t' g t : X ⟶ X) (ha : t' ≫ g = g ≫ t) :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback t' ≅
      Scheme.Modules.pullback t ⋙ Scheme.Modules.pullback g :=
  pullbackComp t' g ≪≫ pullbackCongr ha ≪≫ (pullbackComp g t).symm

/-- **Coherence (II).** -/
lemma coherence_II (t' g m t : X ⟶ X) (ha : t' ≫ g = g ≫ t) (hb : g ≫ m = m ≫ g)
    (h : t ≫ m = m) (h' : t' ≫ m = m) (M : X.Modules) :
    (Niso t' g t ha).inv.app ((Scheme.Modules.pullback m).obj M) ≫
        (Scheme.Modules.pullback t').map (Qiso g m hb M).hom ≫
          (pullbackComp t' m).hom.app ((Scheme.Modules.pullback g).obj M) ≫
            (pullbackCongr h').hom.app ((Scheme.Modules.pullback g).obj M) ≫ (Qiso g m hb M).inv =
      (Scheme.Modules.pullback g).map
        ((pullbackComp t m).hom.app M ≫ (pullbackCongr h).hom.app M) := by
  rw [← cancel_mono ((pullbackComp g m).hom.app M)]
  simp only [Niso, Qiso, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, pullbackCongr_hom_app, pullbackCongr_inv_app]
  -- RHS
  rw [map_eqToHom_comp_pullbackComp g h M, reassoc_of% (pullbackComp_assoc_app g t m M)]
  -- LHS
  rw [reassoc_of% (eqToHom_comp_pullbackComp h' g M)]
  rw [reassoc_of% (pullbackComp_assoc_inv₁ t' m g M)]
  rw [reassoc_of% (map_eqToHom_comp_pullbackComp t' hb M)]
  rw [reassoc_of% (pullbackComp_assoc_inv₂ t' g m M)]
  rw [reassoc_of% (eqToHom_comp_pullbackComp ha.symm m M)]
  simp

end PicDict.Transport
