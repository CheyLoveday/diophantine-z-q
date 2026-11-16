import ZInQKernel.Contrib.OneProof.PicDictionary

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory Limits

namespace WeilProof.PBM
open Scheme.Modules

universe u
variable {X Y Z : Scheme.{u}}

attribute [local instance] Scheme.Modules.presheafPullbackCompSheafificationMonoidal

abbrev PP (f : X ⟶ Y) :=
  PresheafOfModules.pullbackOfCommRingCat (F := TopologicalSpace.Opens.map f.base)
    (R := X.sheaf.obj) (S := Y.sheaf.obj) f.toRingCatPresheafHom

abbrev GG (f : X ⟶ Y) := PP f ⋙ sheafification X

abbrev ee (f : X ⟶ Y) : Scheme.Modules.sheafification Y ⋙ Scheme.Modules.pullback f ≅
    PP f ⋙ Scheme.Modules.sheafification X :=
  SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom

example (f : X ⟶ Y) : (PP f).Monoidal := inferInstance
example (f : X ⟶ Y) : (GG f).Monoidal := inferInstance
example : (sheafification X).Monoidal := inferInstance

lemma mu_sheafified (f : X ⟶ Y) (A B : Y.PresheafOfModules) :
    Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) ((sheafification Y).obj A)
        ((sheafification Y).obj B) =
      ((ee f).hom.app A ⊗ₘ (ee f).hom.app B) ≫
        Functor.LaxMonoidal.μ (sheafification X) ((PP f).obj A) ((PP f).obj B) ≫
        (sheafification X).map (Functor.LaxMonoidal.μ (PP f) A B) ≫
        (ee f).inv.app (A ⊗ B) ≫
        (Scheme.Modules.pullback f).map (Functor.OplaxMonoidal.δ (sheafification Y) A B) := by
  let _ : (GG f).Monoidal := presheafPullbackCompSheafificationMonoidal f
  let _ := Scheme.Modules.pullbackLocalizationLifting f
  exact Localization.Monoidal.functorMonoidalOfComp_μ (sheafification Y) _ (Scheme.Modules.pullback f)
    (GG f) A B

abbrev PQ (f : X ⟶ Y) := PresheafOfModules.pullback f.toRingCatSheafHom.hom

def pcQ (f : X ⟶ Y) (g : Y ⟶ Z) : PQ g ⋙ PQ f ≅ PQ (f ≫ g) :=
  PresheafOfModules.pullbackComp _ _

def pcP (f : X ⟶ Y) (g : Y ⟶ Z) : PP g ⋙ PP f ≅ PP (f ≫ g) := pcQ f g

local notation "L" => Scheme.Modules.sheafification

/-- (E) -/
lemma ee_comp (f : X ⟶ Y) (g : Y ⟶ Z) (A : Z.PresheafOfModules) :
    (Scheme.Modules.pullback f).map ((ee g).hom.app A) ≫ (ee f).hom.app ((PP g).obj A) ≫
        (L X).map ((pcP f g).hom.app A) =
      (pullbackComp f g).hom.app ((L Z).obj A) ≫ (ee (f ≫ g)).hom.app A := by
  sorry

/-- (P) -/
lemma pcP_monoidal (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Z.PresheafOfModules) :
    Functor.LaxMonoidal.μ (PP f) ((PP g).obj A) ((PP g).obj B) ≫
        (PP f).map (Functor.LaxMonoidal.μ (PP g) A B) ≫ (pcP f g).hom.app (A ⊗ B) =
      ((pcP f g).hom.app A ⊗ₘ (pcP f g).hom.app B) ≫ Functor.LaxMonoidal.μ (PP (f ≫ g)) A B := by
  sorry

end WeilProof.PBM
