import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-- The scheme step for a prime-to-residue-characteristic isogeny. Its two
composites with the extended dual are multiplication by a unit, hence étale.
Properness of the extended morphism and étaleness then imply finiteness. -/
theorem finiteEtale_of_etale_composites {X Y : Scheme} (f : X ⟶ Y) (g : Y ⟶ X)
    [IsProper f] [LocallyOfFiniteType g] [Etale (f ≫ g)] [Etale (g ≫ f)] :
    IsFinite f ∧ Etale f := by
  let : FormallyUnramified g := FormallyUnramified.of_comp g f
  have hf : Etale f := Etale.of_comp f g
  let : LocallyQuasiFinite f := by
    rw [HasRingHomProperty.eq_affineLocally @LocallyQuasiFinite]
    rw [HasRingHomProperty.eq_affineLocally @Etale] at hf
    refine affineLocally_le (fun {R S _ _} {φ} hφ => ?_) f hf
    let := φ.toAlgebra
    let : Algebra.Etale R S := hφ
    exact (inferInstance : Algebra.QuasiFinite R S)
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite f, hf⟩

/-- In particular, taking the fibre over the unit section gives a finite étale
kernel. The base change map is to the base of the unit section. -/
theorem finiteEtale_kernel_of_etale_composites {S X Y : Scheme}
    (f : X ⟶ Y) (g : Y ⟶ X) (zeroY : S ⟶ Y)
    [IsProper f] [LocallyOfFiniteType g] [Etale (f ≫ g)] [Etale (g ≫ f)] :
    IsFinite (pullback.snd f zeroY) ∧ Etale (pullback.snd f zeroY) := by
  obtain ⟨hfin, het⟩ := finiteEtale_of_etale_composites f g
  let : IsFinite f := hfin
  let : Etale f := het
  exact ⟨inferInstance, inferInstance⟩

end ZInQ.Manuscript.RC.HCMV21
