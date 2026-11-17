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
    -- fold 2 (sz-raynaud): the replacement route (must be true); the old field's Prop stays as the proof's type
    `SZRaynaud.SilverbergZarhinThm35, `SZRaynaud.raynaudSemistableSHOr_of_sz35, `DictModels.RaynaudOr.RaynaudSemistableSHOr,
    `HDec.HSyn.OpenResearchLeaves55, `HDec.HSyn.sixContactMin_of_open74,
    -- fold 1 still in force: must be false / true
    `ZInQ.SemistabAssembly.BostLowerBoundAnSS, `ZInQ.HeightSplit.BostLowerBound, `ZInQ.BostGR9.GaudronRemondSec9LowerAnSS]
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
  let o := `HDec.HSyn.OpenResearchLeaves54
  let n := `HDec.HSyn.OpenResearchLeaves55
  let fo := getStructureFields env o
  let fn := getStructureFields env n
  logInfo m!"field check: {o} {fo.size} fields, {n} {fn.size} fields; only in old: {fo.filter (!fn.contains ·)}; only in new: {fn.filter (!fo.contains ·)}"
  for f in fo do
    if fn.contains f then
      let tyO := (env.find? (o ++ f)).get!.type.bindingBody!
      let tn := (env.find? (n ++ f)).get!.type.bindingBody!
      unless tyO == tn do logInfo m!"type differs: {f}"
