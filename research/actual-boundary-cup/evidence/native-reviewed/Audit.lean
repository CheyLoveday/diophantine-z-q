import Research.DerivativeSwitch.ActualBoundaryCup
import Lean.Util.CollectAxioms
set_option pp.explicit true
#print Research.DerivativeSwitch.ActualBoundaryCup.LocalCupData
#print Research.DerivativeSwitch.ActualBoundaryCup.closed_cup_differential
#print Research.DerivativeSwitch.ActualBoundaryCup.pure_boundary_correction
#print Research.DerivativeSwitch.ActualBoundaryCup.traced_pure_boundary
#print Research.DerivativeSwitch.ActualBoundaryCup.traced_left_boundary
#print Research.DerivativeSwitch.ActualBoundaryCup.traced_right_boundary
#print Research.DerivativeSwitch.ActualBoundaryCup.traced_change_left
#print Research.DerivativeSwitch.ActualBoundaryCup.traced_change_right
open Lean Elab Command in
run_cmd do
  let names : Array Name := #[`Research.DerivativeSwitch.ActualBoundaryCup.closed_cup_differential, `Research.DerivativeSwitch.ActualBoundaryCup.pure_boundary_correction, `Research.DerivativeSwitch.ActualBoundaryCup.traced_pure_boundary, `Research.DerivativeSwitch.ActualBoundaryCup.traced_left_boundary, `Research.DerivativeSwitch.ActualBoundaryCup.traced_right_boundary, `Research.DerivativeSwitch.ActualBoundaryCup.traced_change_left, `Research.DerivativeSwitch.ActualBoundaryCup.traced_change_right]
  for name in names do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
        throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"AXIOM_CHECK {name}: {axioms.toList}"
  logInfo "AXIOM_AUDIT_PASS declarations=7"
