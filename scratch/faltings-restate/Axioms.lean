import ZInQKernel.Contrib.OneProof.FaltingsRestate

#print axioms ZInQ.FaltingsRestate.faltingsHeightBaseChange
#print axioms ZInQ.FaltingsRestate.semistableNeronIdentification_of_ss2
#print axioms ZInQ.FaltingsRestate.semistableNeronIdentification_of_cor33
#print axioms ZInQ.FaltingsRestate.faltingsSemistableHeightBC_of_identification
#print axioms ZInQ.FaltingsRestate.faltingsSemistableHeightBC_of_leaves
#print axioms ZInQ.FaltingsRestate.identityComponent_of_faltingsLemma1
#print axioms ZInQ.FaltingsRestate.identityComponentBaseChangeDVRRange_of_faltingsLemma1
#print axioms ZInQ.FaltingsRestate.semistableNeronIdentification_of_faltingsLemma1
#print axioms ZInQ.FaltingsRestate.faltingsSemistableHeightBC_of_faltingsLemma1

open Lean Elab Command in
run_cmd do
  for (mod, decls) in [
    (`ZInQKernel.Contrib.OneProof.FaltingsRestate,
      [`ZInQ.FaltingsRestate.height_eq_of_two_semistable]),
    (`ZInQKernel.Contrib.OneProof.FaltingsRestateDVR,
      [`ZInQ.FaltingsRestate.range_pullback,
       `ZInQ.FaltingsRestate.generic_iso_of_range,
       `ZInQ.FaltingsRestate.closed_fibre_of_range,
       `ZInQ.FaltingsRestate.exists_semiabelian_component])] do
    for decl in decls do
      let id := mkIdent (mkPrivateNameCore mod decl)
      elabCommand (← `(#print axioms $id))
