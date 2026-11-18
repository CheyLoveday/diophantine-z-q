import ZInQKernel.OneProof.Main


open Lean Elab Command in
/-- Check the transitive closure of types, values and inductive constructors. -/
elab "#nos_closure " root:ident old:ident : command => do
  let env ← getEnv
  let some _ := env.find? root.getId | throwError "Missing root {root.getId}"
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[root.getId]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      stack := stack ++ ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then
        stack := stack ++ v.getUsedConstants
      if let .inductInfo i := ci then stack := stack ++ i.ctors.toArray
  let expectsOld := old.getId == `present
  IO.println s!"{root.getId}: closure size {seen.size}"
  if !expectsOld && seen.contains `HDec.PkgI2.NeronOggShafarevich then
    throwError "HDec copy of NOS survives the bypass"
  for n in [`NOSSepDict.NeronOggShafarevichSep, `PkgI2.NeronOggShafarevich,
      `NOSSepDict.neronOggShafarevich_of_sep, `NOSNarrow.NeronOggShafarevichSepPerfect,
      `NOSNarrow.nosForward_proof, `sorryAx] do
    let found := seen.contains n
    let expected := if n == `NOSNarrow.nosForward_proof then !expectsOld else
      expectsOld && n != `sorryAx && n != `NOSNarrow.NeronOggShafarevichSepPerfect
    IO.println s!"  {n}: {if found then "PRESENT" else "absent"}"
    unless found == expected do throwError "{n}: present={found}, expected={expected}"

#nos_closure HDec.HSyn.sixContactMin_of_open83 present
#nos_closure HDec.HSyn.sixContactMin_of_open84 absent
#nos_closure ZInQ.OneProof.frozenTarget absent
