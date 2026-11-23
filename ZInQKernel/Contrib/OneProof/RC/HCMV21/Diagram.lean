import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Logic.Equiv.Defs

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory

variable {C D : Type*} [Category C] [Category D]
  (F : C ⥤ D) {X Y Z : C}

/-- Extend a single morphism using the bijectivity of generic fibre on this pair
of models; for abelian schemes the bijectivity is the Néron mapping property. -/
noncomputable def extendMorphism (h : Function.Bijective (F.map (X := X) (Y := Y)))
    (f : F.obj X ⟶ F.obj Y) : X ⟶ Y :=
  (Equiv.ofBijective _ h).symm f

theorem map_extendMorphism (h : Function.Bijective (F.map (X := X) (Y := Y)))
    (f : F.obj X ⟶ F.obj Y) : F.map (extendMorphism F h f) = f :=
  (Equiv.ofBijective _ h).apply_symm_apply f

/-- The extension preserves composition, so commutative diagrams and equations
between composites of generic-fibre morphisms hold on the good models. -/
theorem extendMorphism_comp
    (hXY : Function.Bijective (F.map (X := X) (Y := Y)))
    (hYZ : Function.Bijective (F.map (X := Y) (Y := Z)))
    (hXZ : Function.Bijective (F.map (X := X) (Y := Z)))
    (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z) :
    extendMorphism F hXZ (f ≫ g) = extendMorphism F hXY f ≫ extendMorphism F hYZ g := by
  apply hXZ.1
  rw [map_extendMorphism, F.map_comp, map_extendMorphism, map_extendMorphism]

theorem extendMorphism_id (h : Function.Bijective (F.map (X := X) (Y := X))) :
    extendMorphism F h (𝟙 (F.obj X)) = 𝟙 X := by
  apply h.1
  rw [map_extendMorphism, F.map_id]

end ZInQ.Manuscript.RC.HCMV21
