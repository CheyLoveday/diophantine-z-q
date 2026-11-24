import ZInQKernel.Contrib.OneProof.RC.HCMV21.AdelicCorrespondence
import ZInQKernel.Contrib.OneProof.RC.HCMV21.AdelicTorsor
import ZInQKernel.Contrib.OneProof.RC.HCMV21.AnalyticTorsor
import ZInQKernel.Contrib.OneProof.RC.HCMV21.CMFieldArithmetic
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ClassFieldGeneration
import ZInQKernel.Contrib.OneProof.RC.HCMV21.Consumer
import ZInQKernel.Contrib.OneProof.RC.HCMV21.DetectorOrientation
import ZInQKernel.Contrib.OneProof.RC.HCMV21.HeegnerLevel
import ZInQKernel.Contrib.OneProof.RC.HCMV21.HeegnerModels
import ZInQKernel.Contrib.OneProof.RC.HCMV21.OrderStabilizer
import ZInQKernel.Contrib.OneProof.RC.HCMV21.QuotientComparison
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ShimuraJ
import ZInQKernel.Contrib.OneProof.RC.HCMV21.SpecialOrientation

#print axioms ZInQ.Manuscript.RC.HCMV21.adelicOrbitAction
#print axioms ZInQ.Manuscript.RC.HCMV21.adelicOrbitAction_smul_idele
#print axioms ZInQ.Manuscript.RC.HCMV21.adelicOrbitAction_bijective
#print axioms ZInQ.Manuscript.RC.HCMV21.orientedCorrespondence_to_adelicOrbit
#print axioms ZInQ.Manuscript.RC.HCMV21.rationalTorusUnits
#print axioms ZInQ.Manuscript.RC.HCMV21.torusOrbitMap
#print axioms ZInQ.Manuscript.RC.HCMV21.torusOrbitMap_eq_iff
#print axioms ZInQ.Manuscript.RC.HCMV21.adelicOrbitEquivClassGroup
#print axioms ZInQ.Manuscript.RC.HCMV21.adelicOrbitEquivClassGroup_apply
#print axioms ZInQ.Manuscript.RC.HCMV21.IdealLatticeClass
#print axioms ZInQ.Manuscript.RC.HCMV21.analytic_orbit_bijective
#print axioms ZInQ.Manuscript.RC.HCMV21.idealClass_eq_iff_complexHomothety
#print axioms ZInQ.Manuscript.RC.HCMV21.idealClass_eq_of_jLattice_eq
#print axioms ZInQ.Manuscript.RC.HCMV21.hilbertField_eq_adjoin_of_artinActsOnJ
#print axioms ZInQ.Manuscript.RC.HCMV21.eq_of_kronecker_root_of_fixed
#print axioms ZInQ.Manuscript.RC.HCMV21.hilbertField_eq_adjoin_of_freeArtinOrbit
#print axioms ZInQ.Manuscript.RC.HCMV21.inputsAtDatum_of_orientedCorrespondence
#print axioms ZInQ.Manuscript.RC.HCMV21.point_reduction_of_orientedCorrespondence
#print axioms ZInQ.Manuscript.RC.HCMV21.detectorResidueCharacter
#print axioms ZInQ.Manuscript.RC.HCMV21.detectorResidueCharacter_mk
#print axioms ZInQ.Manuscript.RC.HCMV21.detectorOrderScalars
#print axioms ZInQ.Manuscript.RC.HCMV21.detectorResidueCharacter_eq_scalar_reduction
#print axioms ZInQ.Manuscript.RC.HCMV21.detector_inert_prime
#print axioms ZInQ.Manuscript.RC.HCMV21.detector_frobenius_switches
#print axioms ZInQ.Manuscript.RC.HCMV21.mem_levelLattice_iff
#print axioms ZInQ.Manuscript.RC.HCMV21.heegnerDatum_ideal_pair
#print axioms ZInQ.Manuscript.RC.HCMV21.simultaneous_good_models_of_descended_j
#print axioms ZInQ.Manuscript.RC.HCMV21.formPeriod
#print axioms ZInQ.Manuscript.RC.HCMV21.formPeriod_lattice
#print axioms ZInQ.Manuscript.RC.HCMV21.heegnerForm_ideal_pair
#print axioms ZInQ.Manuscript.RC.HCMV21.heegnerBranchPoint
#print axioms ZInQ.Manuscript.RC.HCMV21.hilbert_j_integral_values
#print axioms ZInQ.Manuscript.RC.HCMV21.exists_variableChange_ofJ_of_lattice
#print axioms ZInQ.Manuscript.RC.HCMV21.eq_scalar_add_smul_of_commute
#print axioms ZInQ.Manuscript.RC.HCMV21.commute_units_iff_mem_fieldUnits
#print axioms ZInQ.Manuscript.RC.HCMV21.comap_order_eq_integralClosure
#print axioms ZInQ.Manuscript.RC.HCMV21.isOrderUnit_iff_isIntegral_and_inv
#print axioms ZInQ.Manuscript.RC.HCMV21.existsUnique_quotientCompare
#print axioms ZInQ.Manuscript.RC.HCMV21.orientedCorrespondence_of_primeTo_representatives
#print axioms ZInQ.Manuscript.RC.HCMV21.hilbertArtin_of_idele
#print axioms ZInQ.Manuscript.RC.HCMV21.idelic_j_reciprocity_of_shimura
#print axioms ZInQ.Manuscript.RC.HCMV21.ideal_j_reciprocity_of_shimura
#print axioms ZInQ.Manuscript.RC.HCMV21.geometricResidueCharacter
#print axioms ZInQ.Manuscript.RC.HCMV21.geometricResidueCharacter_eq_of_intertwines
#print axioms ZInQ.Manuscript.RC.HCMV21.frobenius_comp_ne_of_card_sq
