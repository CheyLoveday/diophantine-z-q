import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedSourceAttachment

open ZInQ.Manuscript.RC.EvenJoin

open Lean in
macro "#print_private_axioms" mod:ident decl:ident : command =>
  `(#print axioms $(mkCIdent (mkPrivateNameCore mod.getId decl.getId)))

#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PrimeComparison ZInQ.Manuscript.RC.EvenJoin.PrimeComparison.mem_or_inv_mem
#print axioms PrimeComparison.atPrime
#print axioms PrimeComparison.integerAlgebra
#print axioms PrimeComparison.isLocalizationAtPrime
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PrimeComparison ZInQ.Manuscript.RC.EvenJoin.PrimeComparison.nonunits_int
#print axioms PrimeComparison.liesOver
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PrimeComparison ZInQ.Manuscript.RC.EvenJoin.PrimeComparison.stabilizes
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PrimeComparison ZInQ.Manuscript.RC.EvenJoin.PrimeComparison.residue_action
#print axioms PrimeComparison.arithFrob
#print axioms PrimeComparison.inertia
#print axioms PrimeComparison.exists_comparison
#print_private_axioms ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedSourceAttachment ZInQ.Manuscript.RC.EvenJoin.NormalizedCuspSource.printField
#print axioms NormalizedCuspSource.attachmentOfCarayol
#print axioms PlacedCuspLists.two_mem_receiving
#print axioms PlacedCuspLists.attachmentsOfCarayol
