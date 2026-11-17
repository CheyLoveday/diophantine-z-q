import ZInQKernel.OneProof.Main
/-! fold-b112: closure check of the folded frozen target (copied from fold-b105). The removed Props must not occur in
the closure (types and values) of `ZInQ.OneProof.frozenTarget`, nor `sorryAx`; the hypotheses of frozenTarget are
printed by `#check`. -/

#print axioms ZInQ.OneProof.frozenTarget
#check @ZInQ.OneProof.frozenTarget

open Lean in
def fcValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

open Lean in
run_cmd do
  let env ← getEnv
  let closure : Name → NameSet := fun root => Id.run do
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[root]
    while !todo.isEmpty do
      let c := todo.back!
      todo := todo.pop
      if seen.contains c then continue
      seen := seen.insert c
      if let some ci := env.find? c then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := fcValue? ci then todo := todo ++ v.getUsedConstants
    return seen
  let checked : List Name := [`sorryAx,
    -- removed (must be false)
    `ZInQ.SemistabAssembly.BostLowerBoundAnSS, `ZInQ.R3Residual.BostLowerBoundAn, `ZInQ.HeightFix.BostLowerBoundPrinted,
    `ZInQ.HeightSplit.BostLowerBound, `ZInQ.SemistabAssembly.bostLowerBoundAn_of_ss,
    `ZInQ.ChevFree.bostLowerBound_of_printed_free, `HDec.HSyn.OpenResearchLeaves53, `HDec.HSyn.sixContactMin_of_open72,
    -- the replacement route (must be true)
    `ZInQ.BostGR9.GaudronRemondSec9LowerAnSS, `ZInQ.BostGR9.gaudronRemondSec9LowerAn_of_ss,
    `ZInQ.BostGR9.sec9Printed_of_an, `ZInQ.BostGR9.grBostBound_of_sec9Printed, `ZInQ.BostGR9.r21_of_grBost',
    `ZInQ.HeightSplit.GRBostBound, `HDec.HSyn.OpenResearchLeaves54, `HDec.HSyn.sixContactMin_of_open73]
  for root in [`ZInQ.OneProof.frozenTarget] do
    let s := closure root
    IO.println s!"{root}: closure {s.size}"
    for b in checked do
      IO.println s!"  contains {b}: {s.contains b}"

/-! Field check: `OpenResearchLeaves54` has `OpenResearchLeaves53`'s fields with `bostLowerBoundAnSS` replaced by
`gaudronRemondSec9LowerAnSS`, every other field with the same type. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let o := `HDec.HSyn.OpenResearchLeaves53
  let n := `HDec.HSyn.OpenResearchLeaves54
  let fo := getStructureFields env o
  let fn := getStructureFields env n
  logInfo m!"field check: {o} {fo.size} fields, {n} {fn.size} fields; only in old: {fo.filter (!fn.contains ·)}; only in new: {fn.filter (!fo.contains ·)}"
  for f in fo do
    if fn.contains f then
      let tyO := (env.find? (o ++ f)).get!.type.bindingBody!
      let tn := (env.find? (n ++ f)).get!.type.bindingBody!
      unless tyO == tn do logInfo m!"type differs: {f}"
