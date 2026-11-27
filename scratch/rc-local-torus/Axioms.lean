import ZInQKernel.Contrib.OneProof.RC.LocalTorus.Assembly

/-! Print and check the dependencies of the new declarations, including private lemmas. -/
open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let selectedPrefix := `ZInQKernel.Contrib.OneProof.RC.LocalTorus
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut nTheorems : Nat := 0
  let mut nDefinitions : Nat := 0
  for i in [:env.header.moduleNames.size] do
    unless selectedPrefix.isPrefixOf env.header.moduleNames[i]! do continue
    for ci in env.header.moduleData[i]!.constants do
      match ci with
      | .thmInfo _ => nTheorems := nTheorems + 1
      | .defnInfo _ => nDefinitions := nDefinitions + 1
      | .axiomInfo _ => throwError "Unexpected new axiom {ci.name}"
      | _ => continue
      let n := ci.name
      for ax in ← Lean.collectAxioms n do
        unless allowed.contains ax do throwError "{n} depends on unexpected axiom {ax}"
      elabCommand (← `(command| #print axioms $(mkIdent n)))
  if nTheorems == 0 || nDefinitions == 0 then
    throwError "Audit did not find the local torus declarations"
  logInfo m!"Audited {nTheorems} theorems and {nDefinitions} definitions."
