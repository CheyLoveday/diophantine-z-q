import ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricOrders
import ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricKernel
import ZInQKernel.Contrib.OneProof.RC.HCMV21.PrimeToGeometry
import ZInQKernel.Contrib.OneProof.RC.HCMV21.RamifiedCoset
import ZInQKernel.Contrib.OneProof.RC.HCMV21.SplitCoset
import ZInQKernel.Contrib.OneProof.RC.HCMV21.RightIdealCoordinates
import ZInQKernel.Contrib.OneProof.RC.HCMV21.RestrictedCosets
import ZInQKernel.Contrib.OneProof.RC.HCMV21.InverseLattice
import ZInQKernel.Contrib.OneProof.RC.HCMV21.InverseOrbit

-- Private names contain a numeric component that cannot be entered as an ident.
-- Build the ident from the module and declaration, then use the same audit command.
open Lean in
macro "#printPrivateAxioms " m:ident n:ident : command => do
  let id := mkIdent (mkPrivateNameCore m.getId n.getId)
  `(#print axioms $id:ident)

#print axioms ZInQ.Manuscript.RC.HCMV21.nsmul_mem_levelEnd
#print axioms ZInQ.Manuscript.RC.HCMV21.span_levelEnd_eq_span_end
#print axioms ZInQ.Manuscript.RC.HCMV21.range_precomposeCurveMap_le_annihilator
#print axioms ZInQ.Manuscript.RC.HCMV21.levelEnd_map_of_intertwines
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricKernel ZInQ.Manuscript.RC.HCMV21.overHom_ext_geometricPoints
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricKernel ZInQ.Manuscript.RC.HCMV21.homT_comp_eq_nsmul_id
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricKernel ZInQ.Manuscript.RC.HCMV21.mem_range_homT_iff_coord_in_kernel
#print axioms ZInQ.Manuscript.RC.HCMV21.existsUnique_factor_of_etale_kernel
#print axioms ZInQ.Manuscript.RC.HCMV21.range_precomposeCurveMap_eq_annihilator
#print axioms ZInQ.Manuscript.RC.HCMV21.factor_maps_level
#print axioms ZInQ.Manuscript.RC.HCMV21.factor_mem_levelHom
#print axioms ZInQ.Manuscript.RC.HCMV21.factor_intertwines_label
#print axioms ZInQ.Manuscript.RC.HCMV21.exists_homT_range_of_etale_kernel
#print axioms ZInQ.Manuscript.RC.HCMV21.exists_eq_nsmul_of_etale_homT_dvd
#print axioms ZInQ.Manuscript.RC.HCMV21.mem_levelHom_iff_tateLevelPreimage_mapsTo
#print axioms ZInQ.Manuscript.RC.HCMV21.finiteEtale_mul_of_ne_zero
#print axioms ZInQ.Manuscript.RC.HCMV21.surjective_nsmul_of_ne_zero
#print axioms ZInQ.Manuscript.RC.HCMV21.exists_eq_nsmul_of_primeTo_homT_dvd
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.RamifiedCoset ZInQ.Manuscript.RC.HCMV21.integralJ_sq
#print axioms ZInQ.Manuscript.RC.HCMV21.division_scalar_factors
#print axioms ZInQ.Manuscript.RC.HCMV21.division_existsUnique_quadraticPair
#print axioms ZInQ.Manuscript.RC.HCMV21.divisionVal_eq_one_iff
#print axioms ZInQ.Manuscript.RC.HCMV21.divisionVal_uniformizer
#print axioms ZInQ.Manuscript.RC.HCMV21.division_uniformizer_decomposition
#print axioms ZInQ.Manuscript.RC.HCMV21.divisionVal_torus_even
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.RamifiedCoset ZInQ.Manuscript.RC.HCMV21.uniformizer_sq_value
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.RamifiedCoset ZInQ.Manuscript.RC.HCMV21.uniformizer_sq_torus
#print axioms ZInQ.Manuscript.RC.HCMV21.division_doubleCoset_iff
#print axioms ZInQ.Manuscript.RC.HCMV21.division_red_unit_conj
#print axioms ZInQ.Manuscript.RC.HCMV21.division_uniformizer_switches
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.RamifiedCoset ZInQ.Manuscript.RC.HCMV21.central_uniformizer_even
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.RamifiedCoset ZInQ.Manuscript.RC.HCMV21.inverseConj_mul
#print axioms ZInQ.Manuscript.RC.HCMV21.division_same_orientation_iff_even
#print axioms ZInQ.Manuscript.RC.HCMV21.projector_first_normalForm
#print axioms ZInQ.Manuscript.RC.HCMV21.projector_forms_distinct
#print axioms ZInQ.Manuscript.RC.HCMV21.level_projector_eq_zero_or_one
#print axioms ZInQ.Manuscript.RC.HCMV21.projector_two_normalForms
#print axioms ZInQ.Manuscript.RC.HCMV21.levelRoot_projector_normalForm
#print axioms ZInQ.Manuscript.RC.HCMV21.card_residue_embeddings
#print axioms ZInQ.Manuscript.RC.HCMV21.splitLevelLattice_coordinate
#print axioms ZInQ.Manuscript.RC.HCMV21.mapsTo_splitLevelLattice_iff
#print axioms ZInQ.Manuscript.RC.HCMV21.splitSwap_mem_levelLattice
#print axioms ZInQ.Manuscript.RC.HCMV21.commute_firstMatrix_iff
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.SplitCoset ZInQ.Manuscript.RC.HCMV21.firstMatrix_swap
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.SplitCoset ZInQ.Manuscript.RC.HCMV21.split_coset_factor
#print axioms ZInQ.Manuscript.RC.HCMV21.split_level_doubleCoset
#print axioms ZInQ.Manuscript.RC.HCMV21.preserves_principalRightIdeal_iff
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.RightIdealCoordinates ZInQ.Manuscript.RC.HCMV21.end_mul_apply
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.RightIdealCoordinates ZInQ.Manuscript.RC.HCMV21.end_unit_cancel
#print axioms ZInQ.Manuscript.RC.HCMV21.all_leftMultiples_map_iff
#print axioms ZInQ.Manuscript.RC.HCMV21.latticeOfMaps_inverseTranslate
#print axioms ZInQ.Manuscript.RC.HCMV21.latticeOfMaps_inverseTranslate_principal
#print axioms ZInQ.Manuscript.RC.HCMV21.restricted_coset_factor
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.InverseLattice ZInQ.Manuscript.RC.HCMV21.inv_mul_le_one
#print axioms ZInQ.Manuscript.RC.HCMV21.mem_completedIdeal_algebraMap_iff
#print axioms ZInQ.Manuscript.RC.HCMV21.closure_fractionalIdeal_eq_completedIdeal
#print axioms ZInQ.Manuscript.RC.HCMV21.mem_completedIdeal_mul_iff
#print axioms ZInQ.Manuscript.RC.HCMV21.sInvLat_eq_div_fractionalIdeal
#print axioms ZInQ.Manuscript.RC.HCMV21.exists_complexArtinCond
#print axioms ZInQ.Manuscript.RC.HCMV21.arithmetic_j_of_shimura
#print axioms ZInQ.Manuscript.RC.HCMV21.inverseAdelicOrbitAction_bijective
#print axioms ZInQ.Manuscript.RC.HCMV21.orientedCorrespondence_of_inverseReferenceReads
#print axioms ZInQ.Manuscript.RC.HCMV21.sum_mul_inv_eq_of_invariant
