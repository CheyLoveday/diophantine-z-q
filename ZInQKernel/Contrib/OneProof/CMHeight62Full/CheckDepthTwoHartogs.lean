import ZInQKernel.Contrib.OneProof.CMHeight62Full.DepthTwoHartogs

/-! Axiom check for `DepthTwoHartogs.lean`: every theorem depends only on the three standard
axioms. -/

open ZInQ.Contrib.CMHeight62Full

#check @depthTwo_isDomain
#check @depthTwo_ringKrullDim
#check @depthTwo_isPrime
#check @depthTwo_height
#check @depthTwo_isDVR
#check @depthTwo_mem_range
#check @depthTwo_height_one_cases

#print axioms ZInQ.Contrib.CMHeight62Full.depthTwo_isPrime
#print axioms ZInQ.Contrib.CMHeight62Full.depthTwo_exists_pow_mul
#print axioms ZInQ.Contrib.CMHeight62Full.depthTwo_isDomain
#print axioms ZInQ.Contrib.CMHeight62Full.depthTwo_exists_mem_maximalIdeal_notMem
#print axioms ZInQ.Contrib.CMHeight62Full.depthTwo_exists_maximalIdeal_eq_span_pair
#print axioms ZInQ.Contrib.CMHeight62Full.depthTwo_ringKrullDim
#print axioms ZInQ.Contrib.CMHeight62Full.depthTwo_height
#print axioms ZInQ.Contrib.CMHeight62Full.depthTwo_isDVR
#print axioms ZInQ.Contrib.CMHeight62Full.depthTwo_height_one_cases
#print axioms ZInQ.Contrib.CMHeight62Full.depthTwo_height_maximalIdeal
#print axioms ZInQ.Contrib.CMHeight62Full.depthTwo_mem_range
#print axioms ZInQ.Contrib.CMHeight62Full.depthTwo_iInf_localization_height_one
