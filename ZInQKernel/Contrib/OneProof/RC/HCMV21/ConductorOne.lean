import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClass.Field

namespace ZInQ.Manuscript.RC.HCMV21

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory

/-- The ring class field of the maximal order and the Hilbert class field
are the same subfield of the separable closure, by equality of norm subgroups. -/
theorem ringClassField_maximal_eq_hilbertClassField (K : Type) [Field K] [NumberField K] :
    ringClassField (maximalNumberFieldOrder K) = hilbertClassField K := by
  have h : ringClassNormSubgroup (maximalNumberFieldOrder K) = rayNormSubgroup (Modulus.one K) := by
    apply Subtype.ext
    ext x
    change x ∈ (ringClassIdeleQuotient (maximalNumberFieldOrder K)).ker ↔
      x ∈ raySubgroup (Modulus.one K)
    rw [ker_ringClassIdeleQuotient_maximalNumberFieldOrder]
  change ringClassField (maximalNumberFieldOrder K) = rayClassField (Modulus.one K)
  rw [ringClassField_def, rayClassField_def, h]

end ZInQ.Manuscript.RC.HCMV21
