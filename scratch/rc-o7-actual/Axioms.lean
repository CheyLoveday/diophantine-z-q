import ZInQKernel.Contrib.OneProof.RC.O7Actual.Arithmetic
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Assembly
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Conjugacy
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Embeddings
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Family
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Genus
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Orbits
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Orientation
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Reduction
import ZInQKernel.Contrib.OneProof.RC.O7Actual.SplitLocal
import ZInQKernel.Contrib.OneProof.RC.O7Actual.StageRead

open ZInQ.Manuscript.RC.O7Actual

/- Arithmetic.lean -/
#print axioms quadratic_parameter_le
#print axioms quadratic_norm_one
#print axioms classOrder
#print axioms HalfIntegral
#print axioms exists_basisHom
#print axioms halfIntegral_of_basisHom
#print axioms order_isIntegral
#print axioms optimal_of_maps_integers
#print axioms twoPower_mul
#print axioms unit_of_twoPower
#print axioms ring_two

/- Assembly.lean -/
#print axioms actualVisibility
#print axioms stageStabilizer
#print axioms actual_stabilizer
#print axioms TorusWeights.phase
#print axioms TorusWeights.weight
#print axioms TorusWeights.phase_unit
#print axioms orbitWeight
#print axioms Normalizers.orientation
#print axioms comparisonInputs
#print axioms actual_representative

/- Conjugacy.lean -/
#print axioms rational_conjugacy

/- Embeddings.lean -/
#print axioms OptimalAt
#print axioms halfIntegral_iff_optimal
#print axioms supp_iff_optimal_on_sphere
#print axioms Voight1467VToIII
#print axioms classG_norm_one
#print axioms centralizer_span
#print axioms basis_norm
#print axioms optimal_commuting_unit_sign

/- Family.lean -/
#print axioms StageAt.visibility
#print axioms classOrder_mem_adelic
#print axioms IntegralSupport.classGroup
#print axioms IntegralSupport.stabilizer
#print axioms DatumAt.representative
#print axioms DatumAt.inputs
#print axioms thetaComparison_actual

/- Genus.lean -/
#print axioms NormCharacterDescent
#print axioms norm_character_self_prime
#print axioms norm_character_self_ideal
#print axioms normCharacterDescent_self

/- Orbits.lean -/
#print axioms OrbitSet
#print axioms OrbitFibers.param
#print axioms doubleCoset_restrict
#print axioms doubleCoset_orbitEquiv
#print axioms torsor_weight

/- Orientation.lean -/
#print axioms Orientations
#print axioms card_orientations
#print axioms ZInQ.Manuscript.RC.O7Actual.flip
#print axioms bit_induction
#print axioms cancel_edge_sign
#print axioms orientation_sum
#print axioms atkin_edge
#print axioms uniformizer_edge

/- Reduction.lean -/
#print axioms cj_reference_class
#print axioms cj_lamOf_reduction

/- SplitLocal.lean -/
#print axioms firstProjector
#print axioms projector_first_normalForm
#print axioms projector_forms_distinct
#print axioms projector_two_normalForms
#print axioms levelRoot_projector_normalForm
#print axioms card_residue_embeddings

/- StageRead.lean -/
#print axioms actual_reference_read
