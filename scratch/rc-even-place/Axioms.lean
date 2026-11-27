import ZInQKernel.Contrib.OneProof.RC.EvenPlace.Singleton

open ZInQ.Manuscript.RC.EvenPlace

#print axioms phaseField_mem
#print axioms place_exists
#print axioms Place.mem_complexIntegers_iff
#print axioms Place.root_mem_complexIntegers
#print axioms Place.odd_inv_mem
#print axioms Place.half_not_mem
#print axioms Place.padic_agree
#print axioms character_value_pow
#print axioms Place.character_mem
#print axioms Place.fieldLift_complex
#print axioms Place.localLift_eq
#print axioms Place.localLift_pow
#print axioms Place.rat_mem
#print axioms Place.scaled_phase_factor
#print axioms common_place_for_characters
#print axioms all_mem_of_recurrence
#print axioms recur_scale
#print axioms Place.unshiftedLift_complex
#print axioms Place.unshiftedLift_local
#print axioms Place.source_shift_mem
#print axioms sourceHyp_of_complex
#print axioms singleton_divisions
#print axioms singleton_of_shell

-- Use the numeric component of the internal names, which are not surface identifiers.
open Lean Elab Command in
run_cmd do
  let internalPrefix := Name.num (Name.append `_private `ZInQKernel.Contrib.OneProof.RC.EvenPlace.Place) 0
  for name in #[`ZInQ.Manuscript.RC.EvenPlace.Place.liesOver_two,
      `ZInQ.Manuscript.RC.EvenPlace.Place.continuous_padic,
      `ZInQ.Manuscript.RC.EvenPlace.Place.padic_mem] do
    elabCommand (← `(command| #print axioms $(mkIdent (Name.append internalPrefix name)):ident))
  let internalPrefix := Name.num (Name.append `_private `ZInQKernel.Contrib.OneProof.RC.EvenPlace.Singleton) 0
  for name in #[`ZInQ.Manuscript.RC.EvenPlace.shell_indices_unique,
      `ZInQ.Manuscript.RC.EvenPlace.unary_on_shell,
      `ZInQ.Manuscript.RC.EvenPlace.mem_of_dvd] do
    elabCommand (← `(command| #print axioms $(mkIdent (Name.append internalPrefix name)):ident))
