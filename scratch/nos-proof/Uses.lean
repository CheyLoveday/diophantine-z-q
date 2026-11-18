import ZInQKernel.OneProof.Main

open Lean Elab Command

/-- BFS over the constants used (types and values) from `root`, skipping Mathlib/core modules;
list closure constants whose type mentions `PkgI2.NeronOggShafarevich`. -/
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
  let k := ``PkgI2.NeronOggShafarevich
  for n in seen.toList do
    if skip n then continue
    if let some ci := env.find? n then
      if ci.type.getUsedConstants.contains k then
        let isProj := (env.getProjectionFnInfo? n).isSome
        logInfo m!"TYPEUSES :: {n} proj={isProj} mod={(env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)}"

#nos_uses ZInQ.OneProof.frozenTarget
