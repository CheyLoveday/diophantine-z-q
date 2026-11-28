import ZInQKernel.Contrib.OneProof.CMHeight62Full.PlaceAssembly

/-!
# Axiom check for `PlaceAssembly.lean` (blueprint node L6)

Prints the axioms of every declaration of `PlaceAssembly.lean`. Each should depend only on
`propext`, `Classical.choice` and `Quot.sound`.
-/

namespace ZInQ.Contrib.CMHeight62Full.PlaceAssembly

-- Units of the local ring of the ring of integers
#print axioms valuation_algebraMap_of_isUnit

-- Wedges of germs that agree modulo the square of the maximal ideal
#print axioms toHodgeOne_eq_div_smul_of_ne_zero
#print axioms wedge_eq_div_smul_of_sub_mem_sq

-- Germs of order at least two at the generic point of the section
#print axioms mem_maximalIdeal_sq_of_ringEquiv
#print axioms mem_maximalIdeal_sq_of_valuation

-- Part 1: the comparison tuple from the local data
#print axioms hcmp_of_localData

-- Part 2: the per-place assembly
#print axioms placeInstances
#print axioms not_mem_of_valuation_mul_pow_succ
#print axioms localComparison_core

end ZInQ.Contrib.CMHeight62Full.PlaceAssembly
