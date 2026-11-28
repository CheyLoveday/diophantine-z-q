import ZInQKernel.Contrib.OneProof.CMHeight62Full.Hartogs

/-! Axiom check for `Hartogs.lean`: every theorem depends only on the three standard axioms. -/

open ZInQ.Contrib.CMHeight62Full

#check @iInf_localization_height_one
#check @mem_range_of_forall_height_one

#print axioms ZInQ.Contrib.CMHeight62Full.mem_hartogsConductor
#print axioms ZInQ.Contrib.CMHeight62Full.hartogsConductor_le_smul
#print axioms ZInQ.Contrib.CMHeight62Full.exists_isPrime_hartogsConductor
#print axioms ZInQ.Contrib.CMHeight62Full.height_hartogsConductor_eq_one
#print axioms ZInQ.Contrib.CMHeight62Full.mem_range_of_forall_height_one
#print axioms ZInQ.Contrib.CMHeight62Full.mem_localizationAtPrimeSubalgebra_iff
#print axioms ZInQ.Contrib.CMHeight62Full.iInf_localization_height_one
#print axioms ZInQ.Contrib.CMHeight62Full.iInf_localization_height_one_fractionRing
#print axioms ZInQ.Contrib.CMHeight62Full.algebraMap_surjective_of_forall_height_ne_one
#print axioms ZInQ.Contrib.CMHeight62Full.algebraMap_surjective_of_ringKrullDim_nonpos
#print axioms ZInQ.Contrib.CMHeight62Full.iInf_localization_height_one_of_isField
