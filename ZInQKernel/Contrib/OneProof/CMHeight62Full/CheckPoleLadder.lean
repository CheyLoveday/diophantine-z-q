import ZInQKernel.Contrib.OneProof.CMHeight62Full.PoleLadder

/-! Axiom check for node N9-alg (`PoleLadder.lean`). -/

open ZInQ.Contrib.CMHeight62Full

#print axioms polePart
#print axioms mem_polePart_iff
#print axioms polePart_mono
#print axioms mem_polePart_of_mul_pow_mem_nonunits
#print axioms mul_pow_mem_nonunits_iff
#print axioms exists_polePart_succ_le
#print axioms exists_finset_polePart_le_span
#print axioms finiteDimensional_polePart
#print axioms finrank_polePart_le
#print axioms span_eq_polePart_of_linearIndependent
#print axioms exists_not_mem_polePart_of_linearIndependent
#print axioms not_mem_polePart_iff_valuation_eq_one
#print axioms exists_exactPoleOrder_two_three
#print axioms polePart_gap_of_baseChange
#print axioms valuation_algebraMap_eq_one_of_isUnit
#print axioms isUnit_of_valuation_eq_one'
#print axioms eq_zero_of_sum_residueHom_mul_reduce
#print axioms linearIndependent_reduce
#print axioms exists_reduce_not_mem_polePart
