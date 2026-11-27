import ZInQKernel.Contrib.OneProof.CMCurveOrder.Fold

/-! Audit the project-constant closure of the actual new height theorem.
The walker is copied from the open77 audit. -/

open Lean Meta

def closureZ (env : Environment) (root : Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[root]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let inZ := match env.getModuleIdxFor? n with
      | some i => (env.header.moduleNames[i.toNat]!.toString.startsWith "ZInQKernel")
      | none => false
    if !inZ then continue
    match env.find? n with
    | some ci =>
      let v := match ci with | .thmInfo t => t.value | .defnInfo d => d.value | _ => default
      for c in v.getUsedConstants ++ ci.type.getUsedConstants do
        if !seen.contains c then stack := stack.push c
    | none => pure ()
  return seen

#eval show MetaM Unit from do
  let env ← getEnv
  let root := `HDec.HSyn.sixContactMin_of_open78_cm
  let s := closureZ env root
  for n in [`HDec.CMBranch.FibreSplit.cmCurveOrder324_of,
      `HDec.CMBranch.FibreSplit.cmFibreSplit_of_curveOrder324,
      `ZInQ.BostGR9.GaudronRemondSec9LowerAnSS] do
    unless s.contains n do throwError "missing dependency {n}"
    IO.println s!"present: {n}"
  for n in [`HDec.HSyn.OpenResearchLeaves58CM.cmFibreSplit,
      `HDec.CMBranch.FibreSplit.cmCurveOrder_of, `GR512Bridge.GonzalezRotgerThm512X6RCF,
      `LeafQM.AV.R5ptProps] do
    if s.contains n then throwError "unexpected dependency {n}"
    IO.println s!"absent: {n}"
  let bundle := `HDec.HSyn.OpenResearchLeaves59CMFS
  let fields := getStructureFields env bundle
  unless fields.size == 30 do throwError "expected 30 fields, found {fields.size}"
  for f in fields do
    unless s.contains (bundle ++ f) do throwError "unread field {f}"
  IO.println s!"all {fields.size} research fields are read"
