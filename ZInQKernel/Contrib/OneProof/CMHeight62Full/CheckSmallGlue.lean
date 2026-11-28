import ZInQKernel.Contrib.OneProof.CMHeight62Full.SmallGlue

/-!
# Axiom check for `SmallGlue.lean` (blueprint node L7)

Prints the axioms of every declaration of `SmallGlue.lean`. Each should depend only on
`propext`, `Classical.choice` and `Quot.sound`.
-/

namespace ZInQ.Contrib.CMHeight62Full.SmallGlue

-- Injectivity of `R → A`
#print axioms faithfulSMul_of_irreducible_mem_nonZeroDivisors

-- Fraction fields
#print axioms localizationAtPrimeAlgebra
#print axioms isScalarTower_localizationAtPrime
#print axioms isFractionRing_localizationAtPrime
#print axioms charZero_localizationAtPrime
#print axioms algebraMap_injective_of_tower
#print axioms fractionFieldAlgebra
#print axioms isScalarTower_fractionFieldAlgebra
#print axioms algebraMap_eq_lift

-- Rings of integers
#print axioms finite_residueField_ringOfIntegers
#print axioms perfectField_residueField_ringOfIntegers
#print axioms charZero_localization_ringOfIntegers
#print axioms isDiscreteValuationRing_localization_ringOfIntegers
#print axioms isFractionRing_localization_ringOfIntegers

-- The special-fibre valuation and its place
#print axioms isUniformizer_specialFibreValuation
#print axioms reduce_specialFibreValuation_algebraMap
#print axioms reduce_mem_specialFibrePlace
#print axioms exists_reduce_mem_specialFibrePlace
#print axioms isUniformizerAt_reduce_specialFibrePlace

-- Pole spaces
#print axioms exp_one_pow_add
#print axioms mul_mem_poleSpaceIn
#print axioms poleSpaceIn_mono
#print axioms one_mem_poleSpaceIn
#print axioms monomials_mem_poleSpaceIn
#print axioms eq_exp_one_pow_succ
#print axioms valuation_eq_of_mem_poleSpaceIn_succ
#print axioms valuation_eq_two_of_mem_poleSpaceIn
#print axioms valuation_eq_three_of_mem_poleSpaceIn

-- Transcendence degree
#print axioms trdegLeOne_of_algEquiv

end ZInQ.Contrib.CMHeight62Full.SmallGlue
