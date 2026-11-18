import ZInQKernel.OneProof.Main
import Lean

open Lean

def censusValue? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

def censusModule (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => toString (env.header.modules[i.toNat]!.module)
  | none => "?"

def censusKey (n : Name) : Bool :=
  let k := n.toString
  ["DeligneCanonicalModelY3EveryPrint", "deligneCanonicalModelY3EveryPrint",
    "deligneH_of_print", "bodyH_of_PM", "unitsH_of_PM", "DeligneBodyAtPM", "ModuliAtUnitsHP",
    "shimuraMainThmIDeligneY3AbU", "ShimuraMainThmIDeligneY3AbU",
    "shimuraMainThmIDeligneY3AbU_of_print", "shimuraMainThmIDeligneY3AbU_of_printPM",
    "field_of_printP", "deligneP_of_H", "body_of_H", "units_of_H",
    "mainThmI_of_U", "isShimuraHolFamily_of_body", "shimuraFamilyAb_of_mainThmI",
    "shimuraFamilyAb_of_U", "rayClassCMAb_of_leaves", "rayClassCMAb_of", "embed_core",
    "obj_at", "y3ConnectedAb_of_U", "y3ConnectedAb_of_mainThmI", "connected_of_body"].any
      (fun s => k.endsWith ("." ++ s))

run_cmd do
  let env ← getEnv
  -- Every declaration censused is in a module importing RayClassShimura, or
  -- in that module itself. Modules outside this cone cannot refer to any of
  -- the declarations under audit.
  let seed := `ZInQKernel.Contrib.OneProof.RayClassShimura
  let mut eligible : NameHashSet := {}
  let mut size := 1
  while size != eligible.size do
    size := eligible.size
    for i in [:env.header.modules.size] do
      let m := env.header.modules[i]!.module
      if m == seed || env.header.moduleData[i]!.imports.any (fun p => eligible.contains p.module) then
        eligible := eligible.insert m
  let mut seen : NameHashSet := {}
  let mut todo : Array Name := #[`ZInQ.OneProof.frozenTarget]
  let mut out : Array String := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    unless (env.getModuleIdxFor? n).any
        (fun i => eligible.contains env.header.modules[i.toNat]!.module) do continue
    seen := seen.insert n
    if let some c := env.find? n then
      let ts := c.type.getUsedConstants
      let vs := ((censusValue? c).map Expr.getUsedConstants).getD #[]
      todo := todo ++ ts ++ vs
      let t := ts.filter censusKey
      let v := vs.filter censusKey
      if censusKey n || !t.isEmpty || !v.isEmpty then
        out := out.push s!"{censusModule env n} {n} TYPE {t.toList} VALUE {v.toList}"
  IO.println s!"relevant closure size {seen.size}; census {out.size}"
  for s in out.qsort (· < ·) do IO.println s

  for n in #[`Y3Hodge.deligneH_of_print, `Y3Fix.shimuraMainThmIDeligneY3AbU_of_print,
      `RayClassCFT.shimuraFamilyAb_of_U, `RayClassCFT.rayClassCMAb_of_leaves, `DCY3Used.y3ConnectedAb_of_U] do
    unless seen.contains n do
      throwError "Expected live declaration missing: {n}"
  for n in #[`Y3Hodge.shimuraMainThmIDeligneY3AbU_of_printPM, `Y3ABUPrint.shimuraMainThmIDeligneY3AbU_of_print,
      `Y3Hodge.print_of_deligneH, `Y3Hodge.print_iff_deligneH] do
    unless (env.find? n).isSome && !seen.contains n do
      throwError "Control declaration absent from environment or unexpectedly live: {n}"
  IO.println "Census controls passed."
