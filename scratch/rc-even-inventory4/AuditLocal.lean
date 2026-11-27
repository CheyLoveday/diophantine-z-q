import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedLocal

open Lean in
macro "#print_private_axioms" mod:ident decl:ident : command =>
  `(#print axioms $(mkCIdent (mkPrivateNameCore mod.getId decl.getId)))

#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedLocalLevels ZInQ.Manuscript.RC.EvenJoin.tested_coprime_complement
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedLocalLevels ZInQ.Manuscript.RC.EvenJoin.movingLevel_split
#print axioms ZInQ.Manuscript.RC.EvenJoin.tested_square_not_dvd_movingLevel
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedLocalLevels ZInQ.Manuscript.RC.EvenJoin.exists_tested_unit
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedLocalLevels ZInQ.Manuscript.RC.EvenJoin.jacobi_eq_one_of_congr
#print axioms ZInQ.Manuscript.RC.EvenJoin.evenBlockPrimes
#print axioms ZInQ.Manuscript.RC.EvenJoin.even_blockChar_at_tested_unit
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedLocalLevels ZInQ.Manuscript.RC.EvenJoin.mem_evenBlockPrimes_of_dvd
#print axioms ZInQ.Manuscript.RC.EvenJoin.tested_dvd_source_iff
#print axioms ZInQ.Manuscript.RC.EvenJoin.tested_not_dvd_degree

#print axioms ZInQ.Manuscript.RC.EvenJoin.WhittakerColumnValues
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerColumns ZInQ.Manuscript.RC.EvenJoin.sumWhittaker
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.WhittakerColumns ZInQ.Manuscript.RC.EvenJoin.sumWhittaker_fourier
#print axioms ZInQ.Manuscript.RC.EvenJoin.WhittakerColumnValues.comparison

#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.RamifiedNewvectorAt
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.DilationWhittakerAt
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedLocal ZInQ.Manuscript.RC.EvenJoin.blockKind
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedLocal ZInQ.Manuscript.RC.EvenJoin.source_occurs
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedLocal ZInQ.Manuscript.RC.EvenJoin.sourceKind
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedLocal ZInQ.Manuscript.RC.EvenJoin.sourceKind_ramified_iff
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.model_coefficient_sum
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.placedCuspidalData
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.placedCuspidal_active
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.placedCuspidal_up
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.old_dilation_recurrence
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.classical_up_at_one
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedLocal ZInQ.Manuscript.RC.EvenJoin.placed_source_normalized
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.placedCuspidal_at_one
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.placedWhittaker
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.cuspidalLocalAt_of_comparisons
#print axioms ZInQ.Manuscript.RC.EvenJoin.PlacedCuspLists.placedGaloisInput_of_carayol
