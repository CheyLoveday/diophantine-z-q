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
