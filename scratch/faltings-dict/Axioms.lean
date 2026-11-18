import ZInQKernel.Contrib.OneProof.FaltingsDict

#print axioms ZInQ.FaltingsRestate.hasTorusExtension_of_connected
#print axioms ZInQ.FaltingsRestate.isLocalizationAway_uniformizer
#print axioms ZInQ.FaltingsRestate.jO_range_eq_basicOpen
#print axioms ZInQ.FaltingsRestate.jO_genericOpen
#print axioms ZInQ.FaltingsRestate.specDVR_points
#print axioms ZInQ.FaltingsRestate.closedFibre_hasTorusExtension
#print axioms ZInQ.FaltingsRestate.genericFibre_dim_eq
#print axioms ZInQ.FaltingsRestate.fibre_dims
#print axioms ZInQ.FaltingsRestate.closedFibre_dim_eq
#print axioms ZInQ.FaltingsRestate.isCommMonObj_groupModelO
#print axioms ZInQ.FaltingsRestate.genericFibre_hasTorusExtension
#print axioms ZInQ.FaltingsRestate.isSemiabelianModelO_imp_faltingsDef
#print axioms ZInQ.FaltingsRestate.faltingsLemma1DVR_models
#print axioms ZInQ.FaltingsRestate.faltingsLemma1DVR_of_printed

open Lean Elab Command in
run_cmd do
  for decl in [
    `ZInQ.FaltingsRestate.isIso_openSubgroup_of_connected,
    `ZInQ.FaltingsRestate.smoothRank_chart,
    `ZInQ.FaltingsRestate.smoothRank_mono,
    `ZInQ.FaltingsRestate.smoothRank_of_connected,
    `ZInQ.FaltingsRestate.dim_baseChange_eq_chart,
    `ZInQ.FaltingsRestate.genericFibre_connected] do
    let id := mkIdent (mkPrivateNameCore `ZInQKernel.Contrib.OneProof.FaltingsDict decl)
    elabCommand (← `(#print axioms $id))
