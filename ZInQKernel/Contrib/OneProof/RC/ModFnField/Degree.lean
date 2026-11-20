import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Algebra.Polynomial.BigOperators

/-! The field-degree step of the converse theorem, on-the-spot (c) for the
rational map at tex 1785–1787 and 2836–2838. -/

noncomputable section

open Polynomial

namespace ZInQ.Manuscript.RC.ModFnField

/-- A product of linear factors with coefficients descending to the base
gives a monic equation of degree at most the number of factors. -/
theorem integral_degree_of_orbit_product {F L : Type*} [Field F] [Field L] [Algebra F L]
    {ι : Type*} (s : Finset ι) (g : ι → L) {x : L} (hx : ∃ j ∈ s, x = g j)
    (P : F[X]) (hP : P.map (algebraMap F L) = ∏ i ∈ s, (X - C (g i))) :
    IsIntegral F x ∧ (minpoly F x).natDegree ≤ s.card := by
  classical
  have hm : P.Monic := by
    apply (algebraMap F L).injective.monic_map_iff.mpr
    rw [hP]
    exact monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (g i)
  obtain ⟨j, hj, rfl⟩ := hx
  have hroot : aeval (g j) P = 0 := by
    rw [aeval_def, ← eval_map, hP, eval_prod]
    exact Finset.prod_eq_zero hj (by simp)
  have hdegree : P.natDegree = s.card := by
    rw [← natDegree_map_eq_of_injective (algebraMap F L).injective, hP,
      natDegree_finsetProd_X_sub_C_eq_card]
  have hint : IsIntegral F (g j) := ⟨P, hm, hroot⟩
  refine ⟨hint, hdegree ▸ ?_⟩
  exact (minpoly.monic hint).natDegree_le_of_dvd hm.ne_zero (minpoly.dvd F (g j) hroot)

/-- If every element has degree at most the known degree of a finite
intermediate field, that field is the whole extension. To apply the
elementwise bound, use a primitive element of the compositum with each
one-element extension. -/
theorem intermediateField_eq_top_of_degree_bound
    {F L : Type*} [Field F] [CharZero F] [Field L] [Algebra F L]
    (D : IntermediateField F L) [FiniteDimensional F D]
    (hbound : ∀ x : L, IsIntegral F x ∧ (minpoly F x).natDegree ≤ Module.finrank F D) :
    D = ⊤ := by
  apply top_unique
  intro x _
  let S := IntermediateField.adjoin F ({x} : Set L)
  let M := D ⊔ S
  have : FiniteDimensional F S := IntermediateField.adjoin.finiteDimensional (hbound x).1
  have : FiniteDimensional F M := IntermediateField.finiteDimensional_sup D S
  obtain ⟨z, hz⟩ := Field.exists_primitive_element F M
  have hdegree : Module.finrank F M = (minpoly F (z : L)).natDegree := by
    calc
      Module.finrank F M = (minpoly F z).natDegree :=
        ((Field.primitive_element_iff_minpoly_natDegree_eq F z).mp hz).symm
      _ = (minpoly F (z : L)).natDegree :=
        congrArg natDegree (minpoly.algHom_eq M.val M.val.injective z).symm
  have heq : D = M := IntermediateField.eq_of_le_of_finrank_le le_sup_left
    (hdegree ▸ (hbound (z : L)).2)
  rw [heq]
  exact (le_sup_right : S ≤ M) (IntermediateField.mem_adjoin_simple_self F x)

#print axioms integral_degree_of_orbit_product
#print axioms intermediateField_eq_top_of_degree_bound

end ZInQ.Manuscript.RC.ModFnField
