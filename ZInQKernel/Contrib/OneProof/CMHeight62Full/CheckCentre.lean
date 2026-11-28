import ZInQKernel.Contrib.OneProof.CMHeight62Full.Centre

/-!
# Axiom check for `Centre.lean`

Each `#print axioms` below should report only `propext`, `Classical.choice` and `Quot.sound`.
-/

open ZInQ.Contrib.CMHeight62Full.Centre

#print axioms centre_hartogs
#print axioms centre_val_eq_one
#print axioms centre_vertical
#print axioms centre_spec
#print axioms isDiscreteValuationRing_valuationSubring
#print axioms centre_spec_top
#print axioms ptDer_mul_pow_ne_zero
#print axioms ptDer_exists_param
#print axioms ptDer_ker_le
#print axioms isDiscreteValuationRing_of_formallySmooth
#print axioms isDiscreteValuationRing_of_standardSmooth
#print axioms hcentre_of_centres
