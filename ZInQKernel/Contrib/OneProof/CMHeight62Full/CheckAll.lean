import ZInQKernel.Contrib.OneProof.CMHeight62Full.NormAssembly
import ZInQKernel.Contrib.OneProof.CMHeight62Full.Weierstrass
import ZInQKernel.Contrib.OneProof.CMHeight62Full.Reduction
import ZInQKernel.Contrib.OneProof.CMHeight62Full.Lattice
import ZInQKernel.Contrib.OneProof.CMHeight62Full.LatticeBasis
import ZInQKernel.Contrib.OneProof.CMHeight62Full.Hartogs
import ZInQKernel.Contrib.OneProof.CMHeight62Full.GenericComparison
import ZInQKernel.Contrib.OneProof.CMHeight62Full.WeierstrassDVR
import ZInQKernel.Contrib.OneProof.CMHeight62Full.LocalStructure
import ZInQKernel.Contrib.OneProof.CMHeight62Full.GroupCurveNotP1

/-!
# Axiom check for all `CMHeight62Full` files

Imports every file of the finite-place development (base files N0–N3 and the lattice core, and
the wave-1 nodes N5, N7, N8, N9a, N10a, N11) in one environment, so that a declaration-name clash
between files would fail here, and prints the axioms of every theorem. Each should depend only on
`propext`, `Classical.choice` and `Quot.sound`.
-/

-- NormAssembly.lean
#print axioms ZInQ.Contrib.CMHeight62Full.abs_norm_le_absNorm_pow_of_pow_le
#print axioms ZInQ.Contrib.CMHeight62Full.abs_norm_le_absNorm_pow_of_valuation
#print axioms ZInQ.Contrib.CMHeight62Full.boundSubmodule_mul_le
#print axioms ZInQ.Contrib.CMHeight62Full.boundSubmodule_self_le
#print axioms ZInQ.Contrib.CMHeight62Full.mem_boundSubmodule
#print axioms ZInQ.Contrib.CMHeight62Full.one_le_boundSubmodule
#print axioms ZInQ.Contrib.CMHeight62Full.pow_le_boundSubmodule
#print axioms ZInQ.Contrib.CMHeight62Full.pow_le_spanSingleton_of_valuation

-- Weierstrass.lean
#print axioms ZInQ.Contrib.CMHeight62Full.valuation_denom_eq
#print axioms ZInQ.Contrib.CMHeight62Full.valuation_param_eq
#print axioms ZInQ.Contrib.CMHeight62Full.valuation_param_sub_le
#print axioms ZInQ.Contrib.CMHeight62Full.valuation_pow_le_of_variableChange

-- Reduction.lean
#print axioms ZInQ.Contrib.CMHeight62Full.abs_norm_algebraMap_le_of_models
#print axioms ZInQ.Contrib.CMHeight62Full.abs_norm_le_absNorm_pow_twelve_of_models

-- Lattice.lean
#print axioms ZInQ.Contrib.CMHeight62Full.div_mem_integral_of_lt_one
#print axioms ZInQ.Contrib.CMHeight62Full.exists_valuation_sum_eq
#print axioms ZInQ.Contrib.CMHeight62Full.linearIndependent_of_residuallyIndependent
#print axioms ZInQ.Contrib.CMHeight62Full.sum_integral_iff

-- LatticeBasis.lean
#print axioms ZInQ.Contrib.CMHeight62Full.IsUniformizer.le_of_lt_one
#print axioms ZInQ.Contrib.CMHeight62Full.IsUniformizer.lt_one_iff_div
#print axioms ZInQ.Contrib.CMHeight62Full.IsUniformizer.valuation_ne_zero
#print axioms ZInQ.Contrib.CMHeight62Full.exists_best_approximation
#print axioms ZInQ.Contrib.CMHeight62Full.exists_lattice_basis
#print axioms ZInQ.Contrib.CMHeight62Full.exists_linearForm_of_notMem
#print axioms ZInQ.Contrib.CMHeight62Full.exists_residuallyIndependent_basis
#print axioms ZInQ.Contrib.CMHeight62Full.exists_residuallyIndependent_cons
#print axioms ZInQ.Contrib.CMHeight62Full.exists_residuallyIndependent_fin
#print axioms ZInQ.Contrib.CMHeight62Full.exists_zpow_bound
#print axioms ZInQ.Contrib.CMHeight62Full.le_of_zpow_le_zpow_of_lt_one_aux
#print axioms ZInQ.Contrib.CMHeight62Full.residuallyIndependent_cons
#print axioms ZInQ.Contrib.CMHeight62Full.zpow_le_zpow_of_lt_one_of_le_aux

-- Hartogs.lean
#print axioms ZInQ.Contrib.CMHeight62Full.algebraMap_surjective_of_forall_height_ne_one
#print axioms ZInQ.Contrib.CMHeight62Full.algebraMap_surjective_of_ringKrullDim_nonpos
#print axioms ZInQ.Contrib.CMHeight62Full.exists_isPrime_hartogsConductor
#print axioms ZInQ.Contrib.CMHeight62Full.hartogsConductor_le_smul
#print axioms ZInQ.Contrib.CMHeight62Full.height_hartogsConductor_eq_one
#print axioms ZInQ.Contrib.CMHeight62Full.iInf_localization_height_one
#print axioms ZInQ.Contrib.CMHeight62Full.iInf_localization_height_one_fractionRing
#print axioms ZInQ.Contrib.CMHeight62Full.iInf_localization_height_one_of_isField
#print axioms ZInQ.Contrib.CMHeight62Full.mem_hartogsConductor
#print axioms ZInQ.Contrib.CMHeight62Full.mem_localizationAtPrimeSubalgebra_iff
#print axioms ZInQ.Contrib.CMHeight62Full.mem_range_of_forall_height_one

-- GenericComparison.lean
#print axioms ZInQ.Contrib.CMHeight62Full.exists_variableChange_of_mem_span
#print axioms ZInQ.Contrib.CMHeight62Full.exists_variableChange_of_poleSpaces
#print axioms ZInQ.Contrib.CMHeight62Full.genCmp_coeff_eq_zero
#print axioms ZInQ.Contrib.CMHeight62Full.genCmp_coeffs_eq_zero
#print axioms ZInQ.Contrib.CMHeight62Full.genCmp_equation_baseChange_iff
#print axioms ZInQ.Contrib.CMHeight62Full.genCmp_equation_smul
#print axioms ZInQ.Contrib.CMHeight62Full.genCmp_val_smul_le

-- WeierstrassDVR.lean
#print axioms ZInQ.Contrib.CMHeight62Full.closure_eq_closure_param
#print axioms ZInQ.Contrib.CMHeight62Full.coe_toIntegers
#print axioms ZInQ.Contrib.CMHeight62Full.equation_variableChange_map
#print axioms ZInQ.Contrib.CMHeight62Full.exists_singular_of_partials
#print axioms ZInQ.Contrib.CMHeight62Full.exists_singular_point_char_three
#print axioms ZInQ.Contrib.CMHeight62Full.exists_singular_point_char_two
#print axioms ZInQ.Contrib.CMHeight62Full.exists_singular_point_of_Δ_eq_zero
#print axioms ZInQ.Contrib.CMHeight62Full.exists_singular_point_short
#print axioms ZInQ.Contrib.CMHeight62Full.exists_weierstrassCurve_of_fin_relation
#print axioms ZInQ.Contrib.CMHeight62Full.exists_weierstrassCurve_of_relation
#print axioms ZInQ.Contrib.CMHeight62Full.isLocalHom_toIntegers
#print axioms ZInQ.Contrib.CMHeight62Full.isSingularParam_of_Δ_eq_zero
#print axioms ZInQ.Contrib.CMHeight62Full.isSingularParam_reduce
#print axioms ZInQ.Contrib.CMHeight62Full.param_of_singular
#print axioms ZInQ.Contrib.CMHeight62Full.reduce_algebraMap_mul
#print axioms ZInQ.Contrib.CMHeight62Full.reduce_equation
#print axioms ZInQ.Contrib.CMHeight62Full.singular_of_variableChange
#print axioms ZInQ.Contrib.CMHeight62Full.valuation_algebraMap_mul_le
#print axioms ZInQ.Contrib.CMHeight62Full.valuation_eq_of_sq_eq
#print axioms ZInQ.Contrib.CMHeight62Full.valuation_of_eq_sq_add
#print axioms ZInQ.Contrib.CMHeight62Full.weierstrass_equation_map
#print axioms ZInQ.Contrib.CMHeight62Full.weierstrass_normalization_dvr
#print axioms ZInQ.Contrib.CMHeight62Full.weierstrass_polyX_variableChange
#print axioms ZInQ.Contrib.CMHeight62Full.weierstrass_polyY_variableChange
#print axioms ZInQ.Contrib.CMHeight62Full.weierstrass_poly_variableChange

-- LocalStructure.lean
#print axioms ZInQ.Contrib.CMHeight62Full.bijective_toSpanSingleton_cotangent
#print axioms ZInQ.Contrib.CMHeight62Full.cotangentBasis_apply
#print axioms ZInQ.Contrib.CMHeight62Full.exists_param
#print axioms ZInQ.Contrib.CMHeight62Full.isRegularLocalRing
#print axioms ZInQ.Contrib.CMHeight62Full.ker_isPrime
#print axioms ZInQ.Contrib.CMHeight62Full.ker_le_span_sup_sq
#print axioms ZInQ.Contrib.CMHeight62Full.ker_localSection_eq_span
#print axioms ZInQ.Contrib.CMHeight62Full.ker_lt_sectionPrime
#print axioms ZInQ.Contrib.CMHeight62Full.ker_notMem_minimalPrimes
#print axioms ZInQ.Contrib.CMHeight62Full.localSection_algebraMap
#print axioms ZInQ.Contrib.CMHeight62Full.localStructure
#print axioms ZInQ.Contrib.CMHeight62Full.localStructure_of_standardSmooth
#print axioms ZInQ.Contrib.CMHeight62Full.map_ker_eq_span
#print axioms ZInQ.Contrib.CMHeight62Full.maximalIdeal_eq_span
#print axioms ZInQ.Contrib.CMHeight62Full.mem_sq_of_secDer_eq_zero
#print axioms ZInQ.Contrib.CMHeight62Full.mul_pow_ne_zero_of_secDer
#print axioms ZInQ.Contrib.CMHeight62Full.ringKrullDim_eq_two
#print axioms ZInQ.Contrib.CMHeight62Full.secDer_add
#print axioms ZInQ.Contrib.CMHeight62Full.secDer_algebraMap
#print axioms ZInQ.Contrib.CMHeight62Full.secDer_eq_zero_of_mem_sq
#print axioms ZInQ.Contrib.CMHeight62Full.secDer_mul
#print axioms ZInQ.Contrib.CMHeight62Full.secDer_one
#print axioms ZInQ.Contrib.CMHeight62Full.secDer_sub
#print axioms ZInQ.Contrib.CMHeight62Full.secDer_zero
#print axioms ZInQ.Contrib.CMHeight62Full.sectionPrime_eq_ker_sup
#print axioms ZInQ.Contrib.CMHeight62Full.spanFinrank_maximalIdeal_le_two
#print axioms ZInQ.Contrib.CMHeight62Full.sub_mem_sq
#print axioms ZInQ.Contrib.CMHeight62Full.two_le_height_sectionPrime
#print axioms ZInQ.Contrib.CMHeight62Full.two_le_ringKrullDim

-- GroupCurveNotP1.lean
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.adjoin_le_place
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.aeval_mem_place
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.comap_comap_symm
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.comap_ratPlace_eq
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.comap_symm_comap
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.eq_algebraMap_of_forall_mem
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.eq_mul_of_mem_nonunits
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.eq_of_le_of_nonunits
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.eq_zero_of_algebraMap_mem_nonunits
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.exists_constPlace_not_mem
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.exists_mobius
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.exists_poly_of_mem_pow
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.exists_sub_eq_mul
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.hasSimplePoleOnlyAt_comap
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.inv_not_mem_of_mem_nonunits
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.inv_sub_not_mem_ratPlace
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.isConstPlace_comap
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.isConstPlace_ratPlace
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.isDegreeOnePlace_comap
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.isDegreeOnePlace_ratPlace
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.isIntegral_of_forall_mem
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.mem_comap_algEquiv
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.mem_nonunits_comap
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.mem_nonunits_of_inv_not_mem
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.mem_of_isIntegral
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.mem_of_mem_nonunits
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.mem_ratPlace
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.mul_mem_nonunits
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.ne_zero_of_hasSimplePoleOnlyAt
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.ratPlace_aux
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.ratPlace_eq
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.sub_mem_nonunits_ratPlace
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.sub_mem_ratPlace
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.sub_ne_zero_of_hasSimplePoleOnlyAt
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.transcendental_of_hasSimplePoleOnlyAt
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.valuation_aeval_eq_one
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.valuation_aeval_le
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.valuation_algebraMap_eq_one
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.valuation_le_of_isIntegral
#print axioms ZInQ.Contrib.CMHeight62Full.GroupCurveNotP1.valuation_le_of_monic_root
#print axioms ZInQ.Contrib.CMHeight62Full.adjoin_eq_top_of_hasSimplePoleOnlyAt
#print axioms ZInQ.Contrib.CMHeight62Full.eq_algebraMap_of_mul_uniformizer_mem
#print axioms ZInQ.Contrib.CMHeight62Full.eq_algebraMap_of_mul_uniformizer_mem_of_baseChange
#print axioms ZInQ.Contrib.CMHeight62Full.false_of_hasSimplePoleOnlyAt
#print axioms ZInQ.Contrib.CMHeight62Full.not_hasSimplePoleOnlyAt
#print axioms ZInQ.Contrib.CMHeight62Full.not_hasSimplePoleOnlyAt_of_baseChange
