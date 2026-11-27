import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedRamifiedFactor

open Lean in
macro "#print_private_axioms" mod:ident decl:ident : command =>
  `(#print axioms $(mkCIdent (mkPrivateNameCore mod.getId decl.getId)))

#print axioms ZInQ.Manuscript.RC.EvenJoin.localUnitResidue
#print axioms ZInQ.Manuscript.RC.EvenJoin.localUnitResidue_eq_one
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedLocalCharacter ZInQ.Manuscript.RC.EvenJoin.localUnitResidue_natCast
#print axioms ZInQ.Manuscript.RC.EvenJoin.charConductor_of_localUnitResidue
#print axioms ZInQ.Manuscript.RC.EvenJoin.tested_sourceLevel_exponent_one
#print axioms ZInQ.Manuscript.RC.EvenJoin.tested_sourceChar_at_tested_unit
#print axioms ZInQ.Manuscript.RC.EvenJoin.SourceCentralCharacterAt
#print axioms ZInQ.Manuscript.RC.EvenJoin.sourceCentralCharacter_of_tested

#print axioms ZInQ.Manuscript.RC.EvenJoin.quadraticChar_of_cyclotomic_action
#print axioms ZInQ.Manuscript.RC.EvenJoin.ReciprocityAt.ResidueCyclotomic
#print axioms ZInQ.Manuscript.RC.EvenJoin.reciprocity_quadratic_of_residue

#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.LocalWeilReciprocity ZInQ.Manuscript.RC.EvenJoin.residueAction
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.LocalWeilReciprocity ZInQ.Manuscript.RC.EvenJoin.localFrob
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.LocalWeilReciprocity ZInQ.Manuscript.RC.EvenJoin.residueFrob_infinite
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.LocalWeilReciprocity ZInQ.Manuscript.RC.EvenJoin.residueActionWeil
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.LocalWeilReciprocity ZInQ.Manuscript.RC.EvenJoin.residueAction_inertia
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.LocalWeilReciprocity ZInQ.Manuscript.RC.EvenJoin.residueExponentData
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.LocalWeilReciprocity ZInQ.Manuscript.RC.EvenJoin.residueExponentMap
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.LocalWeilReciprocity ZInQ.Manuscript.RC.EvenJoin.residueExponent_spec
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.LocalWeilReciprocity ZInQ.Manuscript.RC.EvenJoin.residueExponent_inertia
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.LocalWeilReciprocity ZInQ.Manuscript.RC.EvenJoin.residueExponent_frob
#print axioms ZInQ.Manuscript.RC.EvenJoin.localWeilReciprocity
#print axioms ZInQ.Manuscript.RC.EvenJoin.localWeilReciprocity_residue

#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedRamifiedFactor ZInQ.Manuscript.RC.EvenJoin.unramified_eq_of_uniformizer
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedRamifiedFactor ZInQ.Manuscript.RC.EvenJoin.induced_central_eq
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedRamifiedFactor ZInQ.Manuscript.RC.EvenJoin.fixed_eq_zero_of_induced_eval
#print axioms ZInQ.Manuscript.RC.EvenJoin.induced_finrank_level_one
#print axioms ZInQ.Manuscript.RC.EvenJoin.orderedInducingCharacters_unique
#print axioms ZInQ.Manuscript.RC.EvenJoin.ramifiedFactorOfPrincipal
#print axioms ZInQ.Manuscript.RC.EvenJoin.halfModulusOfRoot_complex
#print axioms ZInQ.Manuscript.RC.EvenJoin.NormalizedCuspSource.LocalWhittakerDiagonal
#print axioms ZInQ.Manuscript.RC.EvenJoin.NormalizedCuspSource.localWhittakerTest_of_diagonal
#print axioms ZInQ.Manuscript.RC.EvenJoin.LocalPrincipalAction
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.RamifiedPrincipalInputsAt
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.exists_placed_local_root
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.ramifiedLocalModelAt_of_principalInputs
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.ramifiedLocalModelAt_of_localWeil
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.placedGaloisInput_of_carayol_of_principalInputs
