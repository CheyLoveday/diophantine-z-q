import ZInQKernel.OneProof.Main
import Lean
/-! degpoly-proof: closure constants of `frozenTarget` whose type mentions T7 (`CharPolyIndepOfEll`) or the
field (`CharPolyIndepOfEllAlgClosed`), and their callers in the closure (adapted from homfree-proof). -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

def isTgt (n : Name) : Bool :=
  match n with
  | .str _ s => s == "CharPolyIndepOfEll" || s == "CharPolyIndepOfEllAlgClosed"
  | _ => false

run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[`ZInQ.OneProof.frozenTarget]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ccValue? ci then todo := todo ++ v.getUsedConstants
  IO.println s!"closure size {seen.size}"
  for c in seen.toList do
    if isTgt c then
      IO.println s!"TARGET {c}"
  let mut tyHits : NameSet := {}
  for c in seen.toList do
    if let some ci := env.find? c then
      if ci.type.getUsedConstants.any isTgt then
        tyHits := tyHits.insert c
        IO.println s!"TYPE {c} proj={(env.getProjectionFnInfo? c).isSome}"
  for c in seen.toList do
    if let some ci := env.find? c then
      if let some v := ccValue? ci then
        let used := v.getUsedConstants
        let hits := used.filter (fun n => tyHits.contains n)
        if !hits.isEmpty then
          IO.println s!"CALLER {c} USES {hits.toList}"
