import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedRamifiedNewvector

open Lean in
macro "#print_private_axioms" mod:ident decl:ident : command =>
  `(#print axioms $(mkCIdent (mkPrivateNameCore mod.getId decl.getId)))

#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerEvaluation ZInQ.Manuscript.RC.EvenJoin.whittakerSlash
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerEvaluation ZInQ.Manuscript.RC.EvenJoin.whittakerSlash_hasSum
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerEvaluation ZInQ.Manuscript.RC.EvenJoin.whittakerSlash_periodic
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerEvaluation ZInQ.Manuscript.RC.EvenJoin.whittakerSlash_holo
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerEvaluation ZInQ.Manuscript.RC.EvenJoin.whittakerSlash_bounded
#print axioms ZInQ.Manuscript.RC.EvenJoin.whittakerIntegral
#print axioms ZInQ.Manuscript.RC.EvenJoin.whittakerIntegral_eq
#print axioms ZInQ.Manuscript.RC.EvenJoin.whittakerOffset
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerEvaluation ZInQ.Manuscript.RC.EvenJoin.whittakerOffset_zero
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerEvaluation ZInQ.Manuscript.RC.EvenJoin.whittakerOffset_add
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerEvaluation ZInQ.Manuscript.RC.EvenJoin.upper_level_of_norm
#print axioms ZInQ.Manuscript.RC.EvenJoin.whittakerLocalReduction
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerEvaluation ZInQ.Manuscript.RC.EvenJoin.rationalDiagonal
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerEvaluation ZInQ.Manuscript.RC.EvenJoin.translatedDiagonal
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerEvaluation ZInQ.Manuscript.RC.EvenJoin.isWhittakerTest
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerEvaluation ZInQ.Manuscript.RC.EvenJoin.isWhittakerTest_index
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerEvaluation ZInQ.Manuscript.RC.EvenJoin.isWhittakerTest_away
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerEvaluation ZInQ.Manuscript.RC.EvenJoin.whittakerIntegral_lifts
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerEvaluation ZInQ.Manuscript.RC.EvenJoin.finiteWhittaker
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerEvaluation ZInQ.Manuscript.RC.EvenJoin.finiteWhittaker_eq
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerEvaluation ZInQ.Manuscript.RC.EvenJoin.finiteWhittaker_away
#print axioms ZInQ.Manuscript.RC.EvenJoin.whittakerColumnsOfForms

#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.whittakerColumnValues
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.dilationWhittakerAt_of_forms
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.placedGaloisInput_of_carayol_of_ramified

#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.exists_with_local_square_roots
#print axioms ZInQ.Manuscript.RC.EvenJoin.halfModulusOfRoot
#print axioms ZInQ.Manuscript.RC.EvenJoin.halfModulusOfRoot_units
#print axioms ZInQ.Manuscript.RC.EvenJoin.halfModulusOfRoot_uniformizer
#print axioms ZInQ.Manuscript.RC.EvenJoin.ramified_scalar_complex_eq_sum
#print axioms ZInQ.Manuscript.RC.EvenJoin.NormalizedCuspSource.LocalWhittakerTest
#print axioms ZInQ.Manuscript.RC.EvenJoin.whittaker_translate_sum_eq_classical
#print axioms ZInQ.Manuscript.RC.EvenJoin.ramified_scalar_complex_eq
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.RamifiedLocalModelAt
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.ramifiedNewvectorAt_of_whittakerTests
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.old_degree_endpoint_coefficients
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.placedGaloisInput_of_carayol_of_localModels
