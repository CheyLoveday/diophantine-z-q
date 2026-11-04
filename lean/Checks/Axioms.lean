module

import all ZInQ
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut modules : Array Name := #[]
  for idx in [:env.header.modules.size] do
    let modName := env.header.modules[idx]!.module
    if Name.isPrefixOf `ZInQ modName && modName != `ZInQ then
      modules := modules.push modName
      for name in env.header.moduleData[idx]!.constNames do
        let axioms ← collectAxioms name
        for ax in axioms do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unexpected axiom {ax} in {name} from {modName}"
        checked := checked + 1
        logInfo m!"AXIOM_CHECK {name}: {axioms.toList}"
  unless modules.size == 48 do
    throwError "Expected declarations from 48 project modules, found {modules.size}"
  unless checked ≥ 463 do
    throwError "Expected at least 463 project declarations, checked {checked}"
  logInfo m!"AXIOM_AUDIT_PASS declarations={checked} modules={modules.size}"
