import ZInQKernel.OneProof.Main

/-! Every reference from a constant defined outside the 79 kept Route K / TYZ / CR3 modules
(`scratch/lane74b/kept-mods.txt`: lane74's 78 H-reach files and `RouteK.Selmer.CharSum`) to a constant defined in one
of them, over the environment of `ZInQKernel.OneProof.Main` (type and value of every constant). -/

open Lean Elab Command

elab "#kept_refs" : command => do
  let env ← getEnv
  let kept ← IO.FS.lines "scratch/lane74b/kept-mods.txt"
  let keptSet : NameHashSet := kept.foldl (fun s m => s.insert m.toName) {}
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let mut out : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some m := modOf n | continue
    if !(`ZInQKernel).isPrefixOf m || keptSet.contains m then continue
    let mut cs := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
    for c in cs do
      if let some mc := modOf c then
        if keptSet.contains mc then out := out.push s!"{m} {n} -> {mc} {c}"
  out := out.qsort (· < ·)
  logInfo m!"references into kept modules: {out.size}\n{String.intercalate "\n" (out.toList.eraseDups)}"

#kept_refs
