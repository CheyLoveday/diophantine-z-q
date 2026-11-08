import Research.DerivativeSwitch.ArithmeticBridge
import Lean.Util.CollectAxioms
set_option pp.universes true
set_option pp.explicit true
#print Research.DerivativeSwitch.ArithmeticBridge.LocalPair
#print Research.DerivativeSwitch.ArithmeticBridge.rawCup
#print Research.DerivativeSwitch.ArithmeticBridge.localTransport
#print Research.DerivativeSwitch.ArithmeticBridge.coneProductThird
#print Research.DerivativeSwitch.ArithmeticBridge.PairedBoundaryData
#print Research.DerivativeSwitch.ArithmeticBridge.PairedBoundaryData.partner
#print Research.DerivativeSwitch.ArithmeticBridge.PairedBoundaryData.functional
open Lean Elab Command in
run_cmd do
  let names : Array Name := #[`Research.DerivativeSwitch.ArithmeticBridge.cocycle_conjugation, `Research.DerivativeSwitch.ArithmeticBridge.cocycle_transport_shared_unit, `Research.DerivativeSwitch.ArithmeticBridge.area_smul_left, `Research.DerivativeSwitch.ArithmeticBridge.area_smul_right, `Research.DerivativeSwitch.ArithmeticBridge.coefficient_pairing_symmetric, `Research.DerivativeSwitch.ArithmeticBridge.cone_pure_boundary, `Research.DerivativeSwitch.ArithmeticBridge.PairedBoundaryData.partner_local, `Research.DerivativeSwitch.ArithmeticBridge.transported_boundary_cup, `Research.DerivativeSwitch.ArithmeticBridge.arithmetic_unit_comparison]
  for name in names do
    let declaration ← getConstInfo name
    logInfo m!"STATEMENT {name}: {declaration.type}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
        throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"AXIOM_CHECK {name}: {axioms.toList}"
  logInfo "AXIOM_AUDIT_PASS declarations=9"
