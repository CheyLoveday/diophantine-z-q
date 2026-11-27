import ZInQKernel.Contrib.OneProof.RC.HCMV21.CotangentProduct
import ZInQKernel.Contrib.OneProof.RC.HCMV21.DetectorReference
import ZInQKernel.Contrib.OneProof.RC.HCMV21.FramedReferenceReads
import ZInQKernel.Contrib.OneProof.RC.HCMV21.MatrixFrames
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ParametrizationSquare
import ZInQKernel.Contrib.OneProof.RC.HCMV21.PointedCotangent
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceAdelic
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceCMEmbedding
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceGeometricPoints
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceOrder
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceQuotientRead
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceSemilocal
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceSpecialization
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceTateLevel
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceTateProfile
import ZInQKernel.Contrib.OneProof.RC.HCMV21.TangentCharacter

open Lean in
macro "#printPrivateAxioms " m:ident n:ident : command => do
  let id := mkIdent (mkPrivateNameCore m.getId n.getId)
  `(#print axioms $id:ident)

-- CotangentProduct
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.CotangentProduct ZInQ.Manuscript.RC.HCMV21.PointedScheme.evaluation_eq_zero_iff
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.CotangentProduct ZInQ.Manuscript.RC.HCMV21.PointedScheme.deviation
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.CotangentProduct ZInQ.Manuscript.RC.HCMV21.PointedScheme.jetAlgebra
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.CotangentProduct ZInQ.Manuscript.RC.HCMV21.PointedScheme.jetAlgebra_natural
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.CotangentProduct ZInQ.Manuscript.RC.HCMV21.PointedScheme.jetAlgebra_injective
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.CotangentProduct ZInQ.Manuscript.RC.HCMV21.PointedScheme.infinitesimalBase
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.CotangentProduct ZInQ.Manuscript.RC.HCMV21.PointedScheme.infinitesimalPoint
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.CotangentProduct ZInQ.Manuscript.RC.HCMV21.PointedScheme.infinitesimalPoint_natural
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.CotangentProduct ZInQ.Manuscript.RC.HCMV21.PointedScheme.infinitesimalPoint_injective
#print axioms ZInQ.Manuscript.RC.HCMV21.PointedScheme.cotangent_ranges_sup_eq_top

-- DetectorReference
#print axioms ZInQ.Manuscript.RC.HCMV21.detector_referenceCoordinates

-- FramedReferenceReads
#print axioms ZInQ.Manuscript.RC.HCMV21.orientedCorrespondence_of_framedReferenceReads

-- MatrixFrames
#print axioms ZInQ.Manuscript.RC.HCMV21.matrixFrame_inner
#print axioms ZInQ.Manuscript.RC.HCMV21.splitReference_conjugate

-- ParametrizationSquare
#print axioms ZInQ.Manuscript.RC.HCMV21.restrictSection
#print axioms ZInQ.Manuscript.RC.HCMV21.ParametrizationFibresAt
#print axioms ZInQ.Manuscript.RC.HCMV21.parametrization_commutes_of_fibres
#print axioms ZInQ.Manuscript.RC.HCMV21.point_reduction_of_integral_parametrization

-- PointedCotangent
#print axioms ZInQ.Manuscript.RC.HCMV21.PointedScheme
#print axioms ZInQ.Manuscript.RC.HCMV21.PointedScheme.point
#print axioms ZInQ.Manuscript.RC.HCMV21.PointedScheme.localRing
#print axioms ZInQ.Manuscript.RC.HCMV21.PointedScheme.cotangent
#print axioms ZInQ.Manuscript.RC.HCMV21.PointedScheme.evaluation
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.PointedCotangent ZInQ.Manuscript.RC.HCMV21.PointedScheme.over_of_section
#print axioms ZInQ.Manuscript.RC.HCMV21.PointedScheme.evaluation_constant
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.PointedCotangent ZInQ.Manuscript.RC.HCMV21.PointedScheme.stalkMapAt
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.PointedCotangent ZInQ.Manuscript.RC.HCMV21.PointedScheme.stalkMapAt_canonical
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.PointedCotangent ZInQ.Manuscript.RC.HCMV21.PointedScheme.stalkMapAt_eq
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.PointedCotangent ZInQ.Manuscript.RC.HCMV21.PointedScheme.stalkMapAt_comp
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.PointedCotangent ZInQ.Manuscript.RC.HCMV21.PointedScheme.stalkMapAt_id
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.PointedCotangent ZInQ.Manuscript.RC.HCMV21.PointedScheme.stalkMapAt_germ_top
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.PointedCotangent ZInQ.Manuscript.RC.HCMV21.PointedScheme.map_point
#print axioms ZInQ.Manuscript.RC.HCMV21.PointedScheme.pullStalk
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.PointedCotangent ZInQ.Manuscript.RC.HCMV21.PointedScheme.pullStalk_id
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.PointedCotangent ZInQ.Manuscript.RC.HCMV21.PointedScheme.pullStalk_comp
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.PointedCotangent ZInQ.Manuscript.RC.HCMV21.PointedScheme.mem_maximalIdeal_pullStalk
#print axioms ZInQ.Manuscript.RC.HCMV21.PointedScheme.evaluation_pullStalk
#print axioms ZInQ.Manuscript.RC.HCMV21.PointedScheme.specMap_pullStalk
#print axioms ZInQ.Manuscript.RC.HCMV21.PointedScheme.pullCotangent
#print axioms ZInQ.Manuscript.RC.HCMV21.PointedScheme.pullCotangent_congr
#print axioms ZInQ.Manuscript.RC.HCMV21.PointedScheme.pullCotangent_mk
#print axioms ZInQ.Manuscript.RC.HCMV21.PointedScheme.pullCotangent_id
#print axioms ZInQ.Manuscript.RC.HCMV21.PointedScheme.pullCotangent_comp
#print axioms ZInQ.Manuscript.RC.HCMV21.PointedScheme.ofAbVar
#print axioms ZInQ.Manuscript.RC.HCMV21.PointedScheme.pullCotangent_eq_geometric

-- ReferenceAdelic
#print axioms ZInQ.Manuscript.RC.HCMV21.referenceAnalyticClass
#print axioms ZInQ.Manuscript.RC.HCMV21.ReferenceOrderCoordinates
#print axioms ZInQ.Manuscript.RC.HCMV21.exists_referenceCoordinates
#print axioms ZInQ.Manuscript.RC.HCMV21.reference_leftRing_eq
#print axioms ZInQ.Manuscript.RC.HCMV21.mem_localRight_mul_reference
#print axioms ZInQ.Manuscript.RC.HCMV21.relativeReferenceRead
#print axioms ZInQ.Manuscript.RC.HCMV21.relativeReferenceRead_base
#print axioms ZInQ.Manuscript.RC.HCMV21.relativeReferenceRead_spec
#print axioms ZInQ.Manuscript.RC.HCMV21.multiplyReference
#print axioms ZInQ.Manuscript.RC.HCMV21.multiplyReference_one
#print axioms ZInQ.Manuscript.RC.HCMV21.localRight_mul_reference_eq_iff
#print axioms ZInQ.Manuscript.RC.HCMV21.geometricReferenceRead
#print axioms ZInQ.Manuscript.RC.HCMV21.geometricReferenceRead_base
#print axioms ZInQ.Manuscript.RC.HCMV21.geometricReferenceRead_local
#print axioms ZInQ.Manuscript.RC.HCMV21.reference_hunit

-- ReferenceCMEmbedding
#print axioms ZInQ.Manuscript.RC.HCMV21.ringOfIntegersRationalization
#print axioms ZInQ.Manuscript.RC.HCMV21.ringOfIntegersRationalization_one_tmul
#print axioms ZInQ.Manuscript.RC.HCMV21.referenceCMEmbedding
#print axioms ZInQ.Manuscript.RC.HCMV21.referenceCMEmbedding_on_order
#print axioms ZInQ.Manuscript.RC.HCMV21.localCMEmbedding
#print axioms ZInQ.Manuscript.RC.HCMV21.localCMEmbedding_injective
#print axioms ZInQ.Manuscript.RC.HCMV21.localCMEmbedding_tmul
#print axioms ZInQ.Manuscript.RC.HCMV21.localCMEmbedding_integral_tensors

-- ReferenceGeometricPoints
#print axioms ZInQ.Manuscript.RC.HCMV21.geometricPointSourceIso
#print axioms ZInQ.Manuscript.RC.HCMV21.levelPointsToClosure
#print axioms ZInQ.Manuscript.RC.HCMV21.levelPointsToClosure_injective
#print axioms ZInQ.Manuscript.RC.HCMV21.levelEnd_iff_levelHom_closure

-- ReferenceOrder
#print axioms ZInQ.Manuscript.RC.HCMV21.QuaternionRamificationUniqueness
#print axioms ZInQ.Manuscript.RC.HCMV21.transportOrder
#print axioms ZInQ.Manuscript.RC.HCMV21.exists_referenceEndOrder
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceOrder ZInQ.Manuscript.RC.HCMV21.localBasis_apply
#print axioms ZInQ.Manuscript.RC.HCMV21.quaternionBaseChange
#print axioms ZInQ.Manuscript.RC.HCMV21.quaternionBaseChange_tmul
#print axioms ZInQ.Manuscript.RC.HCMV21.localQuaternionEquiv
#print axioms ZInQ.Manuscript.RC.HCMV21.localQuaternionEquiv_toLocal
#print axioms ZInQ.Manuscript.RC.HCMV21.referenceDivisionChart
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceOrder ZInQ.Manuscript.RC.HCMV21.orderToCompletion
#print axioms ZInQ.Manuscript.RC.HCMV21.completedReferenceEnd
#print axioms ZInQ.Manuscript.RC.HCMV21.completedReferenceEnd_one_tmul
#print axioms ZInQ.Manuscript.RC.HCMV21.referenceCompletion_map_eq
#print axioms ZInQ.Manuscript.RC.HCMV21.reference_levelCompletion_eq
#print axioms ZInQ.Manuscript.RC.HCMV21.completedReferenceDivision
#print axioms ZInQ.Manuscript.RC.HCMV21.completedReferenceDivision_one_tmul

-- ReferenceQuotientRead
#print axioms ZInQ.Manuscript.RC.HCMV21.quotientReferenceRead_away
#print axioms ZInQ.Manuscript.RC.HCMV21.identity_quotientRightIdeal_eq

-- ReferenceSemilocal
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceSemilocal ZInQ.Manuscript.RC.HCMV21.basePlace
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceSemilocal ZInQ.Manuscript.RC.HCMV21.padicSemilocal
#print axioms ZInQ.Manuscript.RC.HCMV21.referenceCMComponents
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceSemilocal ZInQ.Manuscript.RC.HCMV21.padicSemilocal_tmul
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceSemilocal ZInQ.Manuscript.RC.HCMV21.integral_of_adic_coordinates
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceSemilocal ZInQ.Manuscript.RC.HCMV21.localOrder_contains_CM_coordinates
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceSemilocal ZInQ.Manuscript.RC.HCMV21.adic_coordinates_of_localOrder
#print axioms ZInQ.Manuscript.RC.HCMV21.reference_localCM_mem_iff
#print axioms ZInQ.Manuscript.RC.HCMV21.referenceCMAdeles
#print axioms ZInQ.Manuscript.RC.HCMV21.referenceCMAdeles_diagonal
#print axioms ZInQ.Manuscript.RC.HCMV21.reference_geometry_hunit

-- ReferenceSpecialization
#print axioms ZInQ.Manuscript.RC.HCMV21.specialized_cotangentCharacter
#print axioms ZInQ.Manuscript.RC.HCMV21.detector_reference_supersingular
#print axioms ZInQ.Manuscript.RC.HCMV21.exists_detectorEndOrder
#print axioms ZInQ.Manuscript.RC.HCMV21.detector_reference_cotangent
#print axioms ZInQ.Manuscript.RC.HCMV21.reference_divisionCharacter

-- ReferenceTateLevel
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceTateLevel ZInQ.Manuscript.RC.HCMV21.span_reference_primary
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceTateLevel ZInQ.Manuscript.RC.HCMV21.cyclic_primary
#print axioms ZInQ.Manuscript.RC.HCMV21.splitProfile_of_cyclicReference
#print axioms ZInQ.Manuscript.RC.HCMV21.detector_referenceCoordinates_of_cyclic

-- ReferenceTateProfile
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceTateProfile ZInQ.Manuscript.RC.HCMV21.tateMatrix_baseChange
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceTateProfile ZInQ.Manuscript.RC.HCMV21.tateMatrix_mulVec
#print axioms ZInQ.Manuscript.RC.HCMV21.splitProfile_of_referenceTateChain

-- TangentCharacter
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.TangentCharacter ZInQ.Manuscript.RC.HCMV21.PointedScheme.basePoint
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.TangentCharacter ZInQ.Manuscript.RC.HCMV21.PointedScheme.baseCotangent_subsingleton
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.TangentCharacter ZInQ.Manuscript.RC.HCMV21.PointedScheme.pullCotangent_const
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.TangentCharacter ZInQ.Manuscript.RC.HCMV21.PointedScheme.squarePoint
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.TangentCharacter ZInQ.Manuscript.RC.HCMV21.PointedScheme.square_fst
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.TangentCharacter ZInQ.Manuscript.RC.HCMV21.PointedScheme.square_snd
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.TangentCharacter ZInQ.Manuscript.RC.HCMV21.PointedScheme.square_cotangent_span
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.TangentCharacter ZInQ.Manuscript.RC.HCMV21.pullCotangent_add
#print axioms ZInQ.Manuscript.RC.HCMV21.cotangentEndMap
#print axioms ZInQ.Manuscript.RC.HCMV21.cotangentEndMap_one
#print axioms ZInQ.Manuscript.RC.HCMV21.cotangentEndMap_mul
#printPrivateAxioms ZInQKernel.Contrib.OneProof.RC.HCMV21.TangentCharacter ZInQ.Manuscript.RC.HCMV21.onLine_eq_smul
#print axioms ZInQ.Manuscript.RC.HCMV21.cotangentCharacter
#print axioms ZInQ.Manuscript.RC.HCMV21.cotangentMap_eq_character_smul
#print axioms ZInQ.Manuscript.RC.HCMV21.tangentMap_eq_character_smul
#print axioms ZInQ.Manuscript.RC.HCMV21.residueAtSection
#print axioms ZInQ.Manuscript.RC.HCMV21.cotangent_finrank_one
#print axioms ZInQ.Manuscript.RC.HCMV21.cotangentLine
