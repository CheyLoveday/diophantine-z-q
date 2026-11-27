import ZInQKernel.Contrib.OneProof.FaltingsDict2Models

open ZInQ.FaltingsRestate

#print axioms FaltingsLemma1DVRPrint
#print axioms isMonHom_of_generic
#print axioms faltingsLemma1DVR_iff_print
#print axioms faltingsLemma1DVRPrint_of_printed_points
#print axioms splitTorus.grpObj
#print axioms splitTorusPoints
#print axioms splitTorusPoints_natural
#print axioms torusKernel_isPullback
#print axioms torusKernel_isClosedImmersion
#print axioms torusKernel_points
#print axioms hasTorusExtensionScheme_of_hasTorusExtension
#print axioms isSemiabelianModelO_imp_faltingsDefScheme
#print axioms faltingsLemma1DVRPrint_of_printed
#print axioms faltingsSemistableHeightBC_of_faltingsLemma1Print

open Lean Elab Command in
run_cmd do
  for (mod, decl) in [
    (`ZInQKernel.Contrib.OneProof.FaltingsDict2SplitTorus, `ZInQ.FaltingsRestate.torusEval_natural),
    (`ZInQKernel.Contrib.OneProof.FaltingsDict2Torus, `ZInQ.FaltingsRestate.hom_ext_of_algPt),
    (`ZInQKernel.Contrib.OneProof.FaltingsDict2Torus, `ZInQ.FaltingsRestate.torusIso_of_points)] do
    let id := mkIdent (mkPrivateNameCore mod decl)
    elabCommand (← `(#print axioms $id))
