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
  | some i => toString (env.header.moduleNames[i.toNat]!)
  | none => "?"

def censusKey (n : Name) : Bool :=
  let k := n.toString
  ["DeligneCanonicalModelY3EveryPrint", "deligneCanonicalModelY3EveryPrint",
    "deligneH_of_print", "bodyH_of_PM", "unitsH_of_PM", "DeligneBodyAtPM", "ModuliAtUnitsHP",
    "shimuraMainThmIDeligneY3AbU", "ShimuraMainThmIDeligneY3AbU"].any
      (fun s => k.endsWith ("." ++ s))

run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[`ZInQ.OneProof.frozenTarget]
  let mut out : Array String := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some c := env.find? n then
      let ts := c.type.getUsedConstants
      let vs := ((censusValue? c).map Expr.getUsedConstants).getD #[]
      todo := todo ++ ts ++ vs
      let t := ts.filter censusKey
      let v := vs.filter censusKey
      if censusKey n || !t.isEmpty || !v.isEmpty then
        out := out.push s!"{censusModule env n} {n} TYPE {t.toList} VALUE {v.toList}"
  IO.println s!"closure size {seen.size}; census {out.size}"
  for s in out.qsort (· < ·) do IO.println s
