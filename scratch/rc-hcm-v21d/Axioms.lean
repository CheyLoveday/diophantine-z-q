import ZInQKernel.Contrib.OneProof.RC.HCMV21.LevelIntersection
import ZInQKernel.Contrib.OneProof.RC.HCMV21.DeuringHomRank
import ZInQKernel.Contrib.OneProof.RC.HCMV21.QuotientHomLattice
import ZInQKernel.Contrib.OneProof.RC.HCMV21.TateHomLattice
import ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricTateChain
import ZInQKernel.Contrib.OneProof.RC.HCMV21.CyclicTateChain
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ChainIdeal
import ZInQKernel.Contrib.OneProof.RC.HCMV21.DetectorIdeal
import ZInQKernel.Contrib.OneProof.RC.HCMV21.CompletedMaximalOrder
import ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricRightIdeal
import ZInQKernel.Contrib.OneProof.RC.HCMV21.TateIdealRead
import ZInQKernel.Contrib.OneProof.RC.HCMV21.RationalTateCoordinates
import ZInQKernel.Contrib.OneProof.RC.HCMV21.QuaternionTateRead
import ZInQKernel.Contrib.OneProof.RC.HCMV21.CompletionComparison

open Lean in
macro "#printPrivateAxioms " m:ident n:ident : command => do
  let id := mkIdent (mkPrivateNameCore m.getId n.getId)
  `(#print axioms $id:ident)

#print axioms ZInQ.Manuscript.RC.HCMV21.mem_levelHom_iff_exists_levelQuotientMap
#print axioms ZInQ.Manuscript.RC.HCMV21.levelEnd_eq_intersection_of_levelQuotient
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.DeuringHomRank ZInQ.Manuscript.RC.HCMV21.precomposeHom
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.DeuringHomRank ZInQ.Manuscript.RC.HCMV21.precomposeHom_injective
#print axioms ZInQ.Manuscript.RC.HCMV21.hom_basis_of_epi_both_ways
#print axioms ZInQ.Manuscript.RC.HCMV21.end_basis_of_deuring
#print axioms ZInQ.Manuscript.RC.HCMV21.exists_reverse_of_etale_quotient
#print axioms ZInQ.Manuscript.RC.HCMV21.postcomposeToEnd
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.QuotientHomLattice ZInQ.Manuscript.RC.HCMV21.postcomposeToEnd_mem_level
#print axioms ZInQ.Manuscript.RC.HCMV21.span_quotient_levelHom_eq_source_order
#print axioms ZInQ.Manuscript.RC.HCMV21.mem_postcomposeToEnd_levelHom_image_iff
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.TateHomLattice ZInQ.Manuscript.RC.HCMV21.padic_exists_nat_add_pow_mul
#print axioms ZInQ.Manuscript.RC.HCMV21.exists_add_pow_smul_of_mem_span
#print axioms ZInQ.Manuscript.RC.HCMV21.span_homT_eq_top_of_basis
#print axioms ZInQ.Manuscript.RC.HCMV21.tateLevelSubmodule
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.TateHomLattice ZInQ.Manuscript.RC.HCMV21.tateLevelSubmodule_mem_pow_smul
#print axioms ZInQ.Manuscript.RC.HCMV21.span_levelHom_eq_tateLevelMaps
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricTateChain ZInQ.Manuscript.RC.HCMV21.nonempty_tate_basis_two
#print axioms ZInQ.Manuscript.RC.HCMV21.span_homT_eq_top_of_deuring
#print axioms ZInQ.Manuscript.RC.HCMV21.span_levelHom_eq_tate_quotient_chain
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricTateChain ZInQ.Manuscript.RC.HCMV21.homT_reverse_comp_eq
#print axioms ZInQ.Manuscript.RC.HCMV21.mem_tateRange_reverse_iff
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricTateChain ZInQ.Manuscript.RC.HCMV21.span_levelHom_eq_span_primary
#print axioms ZInQ.Manuscript.RC.HCMV21.span_levelHom_eq_tate_composite_quotient_chain
#print axioms ZInQ.Manuscript.RC.HCMV21.tateLevelPreimage_of_cyclic_generator
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.CyclicTateChain ZInQ.Manuscript.RC.HCMV21.exists_linearEquiv_of_primitive
#print axioms ZInQ.Manuscript.RC.HCMV21.exists_tateLevelPreimage_standard
#print axioms ZInQ.Manuscript.RC.HCMV21.latticeChainMaps
#print axioms ZInQ.Manuscript.RC.HCMV21.latticeChainMaps_translate
#print axioms ZInQ.Manuscript.RC.HCMV21.latticeChainMaps_eq_principal
#print axioms ZInQ.Manuscript.RC.HCMV21.mapsTo_latticeChainMaps_iff
#print axioms ZInQ.Manuscript.RC.HCMV21.completeScalarCharacter
#print axioms ZInQ.Manuscript.RC.HCMV21.completeScalarCharacter_one_tmul
#print axioms ZInQ.Manuscript.RC.HCMV21.completeScalarCharacter_factors
#print axioms ZInQ.Manuscript.RC.HCMV21.detector_order_eq_of_maximal
#print axioms ZInQ.Manuscript.RC.HCMV21.detector_leftOrder_eq
#print axioms ZInQ.Manuscript.RC.HCMV21.detector_rightLattice_principal
#print axioms ZInQ.Manuscript.RC.HCMV21.completion_maximal_of_order_maximal
#print axioms ZInQ.Manuscript.RC.HCMV21.levelOrderOfEndOrder
#print axioms ZInQ.Manuscript.RC.HCMV21.levelOrderOfEndOrder_completion_eq
#print axioms ZInQ.Manuscript.RC.HCMV21.quotientRightIdeal
#print axioms ZInQ.Manuscript.RC.HCMV21.localLattice_quotientRightIdeal_eq_span
#print axioms ZInQ.Manuscript.RC.HCMV21.localLattice_quotientRightIdeal_eq_completion
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.TateIdealRead ZInQ.Manuscript.RC.HCMV21.span_levelHom_eq_span_hom_away_level
#print axioms ZInQ.Manuscript.RC.HCMV21.mem_span_postcompose_levelHom_iff_range
#print axioms ZInQ.Manuscript.RC.HCMV21.tateRange_reverse_eq_range_of_torsion_kernel
#print axioms ZInQ.Manuscript.RC.HCMV21.mem_span_postcompose_levelHom_iff_local_factor
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.RationalTateCoordinates ZInQ.Manuscript.RC.HCMV21.algHom_liftEquiv_surjective
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.RationalTateCoordinates ZInQ.Manuscript.RC.HCMV21.baseChangeEnd_span
#print axioms ZInQ.Manuscript.RC.HCMV21.exists_rationalTate_coordinates_of_endOrder
#print axioms ZInQ.Manuscript.RC.HCMV21.exists_rationalTate_coordinates_of_deuring
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.QuaternionTateRead ZInQ.Manuscript.RC.HCMV21.image_span
#print axioms ZInQ.Manuscript.RC.HCMV21.localLattice_quotientRightIdeal_eq_localRight
#print axioms ZInQ.Manuscript.RC.HCMV21.exists_adelic_quotientRightIdeal_of_localFactors
#print axioms ZInQ.Manuscript.RC.HCMV21.rightIdeal_eq_fromAdelic_of_completions
#print axioms ZInQ.Manuscript.RC.HCMV21.torusOrbitMap_eq_of_scaledLocalRight
#print axioms ZInQ.Manuscript.RC.HCMV21.orientedCorrespondence_of_completedReferenceReads
