import ZInQKernel.Contrib.OneProof.RC.EvenJoin.OldNewConsumers

open Lean in
macro "#print_private_axioms" mod:ident decl:ident : command =>
  `(#print axioms $(mkCIdent (mkPrivateNameCore mod.getId decl.getId)))

#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.OldNewProof ZInQ.Manuscript.RC.EvenJoin.GoodPrime
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.OldNewProof ZInQ.Manuscript.RC.EvenJoin.columnOperator
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.OldNewProof ZInQ.Manuscript.RC.EvenJoin.columnEigenvalues
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.OldNewProof ZInQ.Manuscript.RC.EvenJoin.columnOperator_apply
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.OldNewProof ZInQ.Manuscript.RC.EvenJoin.source_eq_of_eigenvalues_eq
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.OldNewProof ZInQ.Manuscript.RC.EvenJoin.column_degree_pos
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.OldNewProof ZInQ.Manuscript.RC.EvenJoin.column_coeff_degree
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.OldNewProof ZInQ.Manuscript.RC.EvenJoin.independent_eigenvalue_fiber
#print axioms ZInQ.Manuscript.RC.EvenJoin.oldNewIndependenceWeightTwo_proved
#print axioms ZInQ.Manuscript.RC.EvenJoin.cuspDilation_form_injective
#print axioms ZInQ.Manuscript.RC.EvenJoin.cuspDilation_coeff_independent_proved

#print axioms ZInQ.Manuscript.RC.EvenJoin.cuspInventory_proved
#print axioms ZInQ.Manuscript.RC.EvenJoin.cuspInventory_coeff_proved
#print axioms ZInQ.Manuscript.RC.EvenJoin.cuspInventory_char_proved
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.inventory_proved
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.block_span_proved
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.evenBasis_proved
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.seed_proved
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.seed_complex_proved
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.seed_integral_proved
#print axioms ZInQ.Manuscript.RC.EvenJoin.placed_diamond_eval_proved
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.integral_diamonds_proved
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.fresh_coeff_mem_proved
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.determinantData_proved
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.model_proved
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.model_coordinates_proved
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedGaloisInput_proved
#print axioms ZInQ.Manuscript.RC.EvenJoin.budgetRealization_of_placed_proved
#print axioms ZInQ.Manuscript.RC.EvenJoin.rules_and_seed_of_placed_joint_proved
