import ZInQKernel.Contrib.OneProof.RC.ModFnField.Degree

/-! A uniform degree bound for linear combinations suffices for the
compositum comparison. Provenance (c). -/

noncomputable section

open IntermediateField Polynomial

namespace ZInQ.Manuscript.RC.ModFnClassify

/-- In characteristic zero, a degree bound on the line through two
integral elements bounds their compositum. Scalars can range over
any infinite field of constants below the base field. -/
theorem mem_adjoin_of_linear_degree_bound
    {R F L : Type*} [Field R] [Infinite R] [Field F] [CharZero F] [Field L]
    [Algebra R F] [Algebra R L] [Algebra F L] [IsScalarTower R F L]
    {x y : L} (hx : IsIntegral F x) (hy : IsIntegral F y)
    (h : ∀ c : R, (minpoly F (x + algebraMap R L c * y)).natDegree ≤ (minpoly F x).natDegree) :
    y ∈ IntermediateField.adjoin F ({x} : Set L) := by
  let S := IntermediateField.adjoin F ({x} : Set L)
  let M := IntermediateField.adjoin F ({x, y} : Set L)
  let := IntermediateField.adjoin.finiteDimensional hx
  let : FiniteDimensional F M := IntermediateField.finiteDimensional_adjoin_pair hx hy
  let a : M := ⟨x, IntermediateField.mem_adjoin_pair_left F x y⟩
  let b : M := ⟨y, IntermediateField.mem_adjoin_pair_right F x y⟩
  let z (c : R) : M := a + algebraMap F M (algebraMap R F c) * b
  let B (c : R) : IntermediateField F M := IntermediateField.adjoin F ({z c} : Set M)
  let : Finite (IntermediateField F M) :=
    Field.finite_intermediateField_of_exists_primitive_element F M (Field.exists_primitive_element F M)
  obtain ⟨c, d, hcd, he⟩ := Finite.exists_ne_map_eq_of_infinite B
  have hzc : z c ∈ B c := IntermediateField.mem_adjoin_simple_self F _
  have hzd : z d ∈ B c := he.symm ▸ IntermediateField.mem_adjoin_simple_self F _
  have hsub : (algebraMap F M (algebraMap R F c - algebraMap R F d)) * b ∈ B c := by
    convert (B c).sub_mem hzc hzd using 1
    simp only [z, map_sub]
    ring
  have hcd' : algebraMap F M (algebraMap R F c - algebraMap R F d) ≠ 0 :=
    (_root_.map_ne_zero (algebraMap F M)).mpr (sub_ne_zero.mpr ((algebraMap R F).injective.ne hcd))
  have hb : b ∈ B c := by
    have hm := (B c).div_mem hsub ((B c).algebraMap_mem (algebraMap R F c - algebraMap R F d))
    rwa [mul_div_cancel_left₀ _ hcd'] at hm
  have ha : a ∈ B c := by
    have hm := (B c).sub_mem hzc ((B c).mul_mem ((B c).algebraMap_mem (algebraMap R F c)) hb)
    simpa [z] using hm
  have htop : B c = ⊤ := by
    have hM : M ≤ (B c).map M.val := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      intro v hv
      rcases hv with (rfl | rfl)
      · exact ⟨a, ha, rfl⟩
      · exact ⟨b, hb, rfl⟩
    apply top_unique
    intro v _
    obtain ⟨w, hw, hev⟩ := hM v.2
    exact (M.val.injective hev) ▸ hw
  have hz : M.val (z c) = x + algebraMap R L c * y := by
    change x + ((algebraMap F L) (algebraMap R F c)) * y = _
    rw [← IsScalarTower.algebraMap_apply R F L]
  have hdeg : Module.finrank F M ≤ Module.finrank F S := by
    rw [adjoin.finrank hx, ← (Field.primitive_element_iff_minpoly_natDegree_eq F (z c)).mp htop,
      ← minpoly.algHom_eq M.val M.val.injective (z c), hz]
    exact h c
  have heq : S = M := IntermediateField.eq_of_le_of_finrank_le
    (IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))) hdeg
  change y ∈ S
  rw [heq]
  exact IntermediateField.mem_adjoin_pair_right F x y

#print axioms mem_adjoin_of_linear_degree_bound

end ZInQ.Manuscript.RC.ModFnClassify
