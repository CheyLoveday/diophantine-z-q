import ZInQKernel.OneProof.Main

open Lean Elab Command

/-- BFS over the constants used (types and values) from `root`, skipping Mathlib/core modules;
list direct type readers, the A6 alias readers, and test the old converse paths. -/
elab "#nos_uses " root:ident : command => do
  let env ← getEnv
  let skip (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      let s := m.toString
      s.startsWith "Mathlib" || s.startsWith "Init" || s.startsWith "Lean" || s.startsWith "Std" ||
        s.startsWith "Batteries" || s.startsWith "Aesop" || s.startsWith "Qq" || s.startsWith "Plausible"
    | none => false
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[root.getId]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    if skip n then continue
    match env.find? n with
    | none => pure ()
    | some ci =>
      let mut cs := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
      if let .inductInfo ii := ci then cs := cs ++ ii.ctors.toArray
      for c in cs do
        unless seen.contains c do stack := stack.push c
  logInfo m!"closure size {seen.size}"
  let keys := #[`PkgI2.NeronOggShafarevich, `HDec.PkgI2.NeronOggShafarevich,
    `NOSSepDict.NeronOggShafarevichSep]
  -- A6 exposes the antecedent through this Prop, so the theorem isn't a direct type hit.
  let a6 := `HDec.D2A6.GoodRedTorsionT
  let mut lines := #[]
  for n in seen.toList do
    if skip n then continue
    if let some ci := env.find? n then
      let deps := ci.type.getUsedConstants
      let ks := keys.filter (deps.contains ·)
      if !ks.isEmpty || deps.contains a6 then
        let isProj := (env.getProjectionFnInfo? n).isSome
        let mod := (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)
        let mode := if ks.isEmpty then "TYPEUSES VIA A6" else "TYPEUSES"
        lines := lines.push s!"{mode} :: {n} proj={isProj} mod={mod} {ks}"
  for l in lines.qsort (· < ·) do IO.println l
  let converse (n : Name) : Bool :=
    let s := n.toString
    s.endsWith ".goodReduction_of_QM_rational3_of_alg" ||
      s.endsWith ".goodReduction_of_QM_rational3_C" ||
      s.endsWith ".QML3.goodReduction" || s.endsWith ".QML3.goodReductionC"
  let targets := ((env.constants.toList.map Prod.fst).filter converse).toArray
  for n in targets.qsort (fun n₁ n₂ => n₁.toString < n₂.toString) do
    IO.println s!"CONVERSE :: {n} present={seen.contains n}"

#nos_uses ZInQ.OneProof.frozenTarget
