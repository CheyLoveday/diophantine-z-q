import ZInQKernel.Contrib.OneProof.RC.HCMV21.Reciprocity
import Mathlib.FieldTheory.Galois.Basic

/-! Field generation needs the freeness of the Artin orbit of the descended
value. This is separate from integrality and inclusion in the class field. -/

namespace ZInQ.Manuscript.RC.HCMV21

open NumberField TauCeti.ClassFieldTheory

/-- If the Artin orbit of a value in the Hilbert class field has no
stabilizer, the value generates the field. This gives the required
reverse degree inequality once freeness of the singular values is known. -/
theorem hilbertField_eq_adjoin_of_freeArtinOrbit {F : Type} [Field F] [NumberField F]
    (x : hilbertClassField F)
    (hfix : ∀ c : ClassGroup (𝓞 F), hilbertClassArtinEquiv F c x = x → c = 1) :
    IntermediateField.adjoin F {(x : SeparableClosure F)} = hilbertClassField F := by
  let H := hilbertClassField F
  let E := IntermediateField.adjoin F {x}
  have hst : E.fixingSubgroup = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro σ hσ
    have hsx := (IntermediateField.mem_fixingSubgroup_iff E σ).mp hσ x
      (IntermediateField.mem_adjoin_simple_self F x)
    obtain ⟨c, rfl⟩ := (hilbertClassArtinEquiv F).surjective σ
    rw [hfix c hsx, map_one]
    exact Subgroup.one_mem _
  have hE : E = ⊤ := by
    rw [← IsGalois.fixedField_fixingSubgroup E, hst, IntermediateField.fixedField_bot]
  have h := IntermediateField.lift_adjoin_simple (F := F) H x
  rw [show IntermediateField.adjoin F {x} = E from rfl, hE, IntermediateField.lift_top] at h
  exact h.symm

end ZInQ.Manuscript.RC.HCMV21
