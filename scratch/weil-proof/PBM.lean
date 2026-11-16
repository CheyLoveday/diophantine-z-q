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

/-- The main identity on sheafified objects. -/
theorem main_sheafified (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Z.PresheafOfModules) :
    Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) ((Scheme.Modules.pullback g).obj ((L Z).obj A))
        ((Scheme.Modules.pullback g).obj ((L Z).obj B)) ≫
      (Scheme.Modules.pullback f).map
        (Functor.LaxMonoidal.μ (Scheme.Modules.pullback g) ((L Z).obj A) ((L Z).obj B)) ≫
        (pullbackComp f g).hom.app ((L Z).obj A ⊗ (L Z).obj B) =
      ((pullbackComp f g).hom.app ((L Z).obj A) ⊗ₘ (pullbackComp f g).hom.app ((L Z).obj B)) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.pullback (f ≫ g)) ((L Z).obj A) ((L Z).obj B) := by
  -- precompose with the iso `f^*(e_g⁻¹) ⊗ f^*(e_g⁻¹)`
  rw [← cancel_epi ((Scheme.Modules.pullback f).map ((ee g).inv.app A) ⊗ₘ
    (Scheme.Modules.pullback f).map ((ee g).inv.app B))]
  -- LHS: naturality of `μ_f`
  have n1 := Functor.LaxMonoidal.μ_natural (Scheme.Modules.pullback f) ((ee g).inv.app A) ((ee g).inv.app B)
  simp only [Functor.comp_obj] at n1
  rw [reassoc_of% n1]
  rw [mu_sheafified f, mu_sheafified g, mu_sheafified (f ≫ g)]
  simp only [Functor.map_comp, Category.assoc]
  have c1 : (Scheme.Modules.pullback f).map ((ee g).inv.app A ⊗ₘ (ee g).inv.app B) ≫
      (Scheme.Modules.pullback f).map ((ee g).hom.app A ⊗ₘ (ee g).hom.app B) = 𝟙 _ := by
    rw [← Functor.map_comp, tensorHom_comp_tensorHom, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    simp
  have c2 : (Scheme.Modules.pullback f).map (Functor.OplaxMonoidal.δ (L Y) ((PP g).obj A) ((PP g).obj B)) ≫
      (Scheme.Modules.pullback f).map (Functor.LaxMonoidal.μ (L Y) ((PP g).obj A) ((PP g).obj B)) = 𝟙 _ := by
    rw [← Functor.map_comp, Functor.Monoidal.δ_μ, CategoryTheory.Functor.map_id]
  have c3 : (ee f).inv.app ((PP g).obj A ⊗ (PP g).obj B) ≫
      (Scheme.Modules.pullback f).map ((L Y).map (Functor.LaxMonoidal.μ (PP g) A B)) =
      (L X).map ((PP f).map (Functor.LaxMonoidal.μ (PP g) A B)) ≫ (ee f).inv.app ((PP g).obj (A ⊗ B)) :=
    ((ee f).inv.naturality (Functor.LaxMonoidal.μ (PP g) A B)).symm
  have c4 : (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map (Functor.OplaxMonoidal.δ (L Z) A B)) ≫
      (pullbackComp f g).hom.app ((L Z).obj A ⊗ (L Z).obj B) =
      (pullbackComp f g).hom.app ((L Z).obj (A ⊗ B)) ≫
        (Scheme.Modules.pullback (f ≫ g)).map (Functor.OplaxMonoidal.δ (L Z) A B) :=
    (pullbackComp f g).hom.naturality (Functor.OplaxMonoidal.δ (L Z) A B)
  have hE : ∀ C : Z.PresheafOfModules, (pullbackComp f g).hom.app ((L Z).obj C) =
      (Scheme.Modules.pullback f).map ((ee g).hom.app C) ≫ (ee f).hom.app ((PP g).obj C) ≫
        (L X).map ((pcP f g).hom.app C) ≫ (ee (f ≫ g)).inv.app C := by
    intro C
    rw [reassoc_of% (ee_comp f g C), Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have c5 : (ee f).inv.app ((PP g).obj (A ⊗ B)) ≫ (Scheme.Modules.pullback f).map ((ee g).inv.app (A ⊗ B)) ≫
      (pullbackComp f g).hom.app ((L Z).obj (A ⊗ B)) =
      (L X).map ((pcP f g).hom.app (A ⊗ B)) ≫ (ee (f ≫ g)).inv.app (A ⊗ B) := by
    rw [hE]
    simp [← Functor.map_comp_assoc]
  have c6 : ∀ C : Z.PresheafOfModules, (Scheme.Modules.pullback f).map ((ee g).inv.app C) ≫
      (pullbackComp f g).hom.app ((L Z).obj C) ≫ (ee (f ≫ g)).hom.app C =
      (ee f).hom.app ((PP g).obj C) ≫ (L X).map ((pcP f g).hom.app C) := by
    intro C
    rw [hE]
    simp [← Functor.map_comp_assoc]
  rw [reassoc_of% c1]
  try simp only [Category.id_comp]
  rw [reassoc_of% c2]
  try simp only [Category.id_comp]
  rw [reassoc_of% c3, c4, reassoc_of% c5]
  rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]
  rw [c6, c6, ← tensorHom_comp_tensorHom_assoc, Functor.LaxMonoidal.μ_natural_assoc]
  have hP := congrArg (fun φ => (L X).map φ) (pcP_monoidal f g A B)
  simp only [Functor.map_comp] at hP
  rw [reassoc_of% hP]

end WeilProof.PBM
