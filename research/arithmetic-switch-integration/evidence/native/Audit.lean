import Research.DerivativeSwitch.ActualBoundaryCup
import Research.DerivativeSwitch.OrthogonalComparison
import Lean.Util.CollectAxioms
set_option pp.universes true
set_option pp.explicit true
#print Research.DerivativeSwitch.ActualBoundaryCup.LocalCupData
#print Research.DerivativeSwitch.OrthogonalComparison.fibreD
#print Research.DerivativeSwitch.OrthogonalComparison.fibreComparison
open Lean Elab Command in
run_cmd do
  let names : Array Name := #[`Research.DerivativeSwitch.ActualBoundaryCup.closed_cup_differential, `Research.DerivativeSwitch.ActualBoundaryCup.pure_boundary_correction, `Research.DerivativeSwitch.ActualBoundaryCup.traced_pure_boundary, `Research.DerivativeSwitch.ActualBoundaryCup.traced_left_boundary, `Research.DerivativeSwitch.ActualBoundaryCup.traced_right_boundary, `Research.DerivativeSwitch.ActualBoundaryCup.traced_change_left, `Research.DerivativeSwitch.ActualBoundaryCup.traced_change_right, `Research.DerivativeSwitch.OrthogonalComparison.fibreComparison_commutes, `Research.DerivativeSwitch.OrthogonalComparison.fibreComparison_global, `Research.DerivativeSwitch.OrthogonalComparison.fibreComparison_sign_change, `Research.DerivativeSwitch.OrthogonalComparison.inverse_preserves_global_homotopy, `Research.DerivativeSwitch.OrthogonalComparison.inverse_preserves_global_homology, `Research.DerivativeSwitch.OrthogonalComparison.inverse_preserves_local_homotopy, `Research.DerivativeSwitch.OrthogonalComparison.inverse_preserves_local_homology]
  for name in names do
    let declaration ← getConstInfo name
    logInfo m!"STATEMENT {name}: {declaration.type}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
        throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"AXIOM_CHECK {name}: {axioms.toList}"
  logInfo "AXIOM_AUDIT_PASS proof_roots=14"
