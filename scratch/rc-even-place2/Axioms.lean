import ZInQKernel.Contrib.OneProof.RC.EvenPlace.KSplitBinding

open ZInQ.Manuscript.RC.EvenPlace

#print axioms phaseData_forget_order
#print axioms phaseData_with_order_of_prints
#print axioms evenSource_with_order_of_prints
#print axioms sourceFamily_with_order_of_prints
#print axioms genuineEvenSource_with_order_of_prints
#print axioms phaseScalarsAt_of_order
#print axioms common_phase_scalars
#print axioms budget_shift_mem
#print axioms sourceAtPlace
#print axioms sourceAtPlace_eta_phase
#print axioms sourceAtPlace_exists
#print axioms singletonCoefficientsAt_of_shell
#print axioms common_place_for_sources
#print axioms kSplitSeed_of_trace_at_place

-- The private declaration has a numeric component in its internal name.
open Lean Elab Command in
run_cmd do
  let internalPrefix := Name.num (Name.append `_private `ZInQKernel.Contrib.OneProof.RC.EvenPlace.Sources) 0
  let name := Name.append internalPrefix `ZInQ.Manuscript.RC.EvenPlace.evenSource_with_origin
  elabCommand (← `(command| #print axioms $(mkIdent name):ident))
