import ZInQKernel.OneProof.Main
import Lean
/-! Reverse value dependencies from the old NOS projections; include every research carrier in the
closure, even if its seed projection isn't used. Repeat the traversal over type dependencies to find
non-seed projections and terms that need a copy because their type changes. -/
open Lean

def ccValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

def isSeed (env : Environment) (n : Name) : Bool :=
  match n with
  | .str _ s => (s == "r7a" || s == "neronOggShafarevichSep") && (env.getProjectionFnInfo? n).isSome
  | _ => false

run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut tyUses : Std.HashMap Name (Array Name) := {}
  let mut valUses : Std.HashMap Name (Array Name) := {}
  let mut todo : Array Name := #[`ZInQ.OneProof.frozenTarget]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some ci := env.find? c then
      let ty := ci.type.getUsedConstants
      tyUses := tyUses.insert c ty
      todo := todo ++ ty
      if let some v := ccValue? ci then
        let us := v.getUsedConstants
        valUses := valUses.insert c us
        todo := todo ++ us
  IO.println s!"closure size {seen.size}"
  (← IO.getStdout).flush
  -- reverse edges
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (c, us) in valUses.toList do
    for u in us do
      rev := rev.alter u (fun o => some ((o.getD #[]).push c))
  let mut tainted : NameSet := {}
  let mut q : Array Name := #[]
  for c in seen.toList do
    if isSeed env c then
      tainted := tainted.insert c
      q := q.push c
  while !q.isEmpty do
    let c := q.back!
    q := q.pop
    for d in rev.getD c #[] do
      if !tainted.contains d then
        tainted := tainted.insert d
        q := q.push d
  -- structures carrying the field
  let mut carriers : NameSet := {}
  for c in tainted.toList do
    if isSeed env c then
      if let some info := env.getProjectionFnInfo? c then
        if let some ci := env.find? info.ctorName then
          if let .ctorInfo cv := ci then carriers := carriers.insert cv.induct
  -- Also include structures whose seed projection is unused.
  for c in seen.toList do
    if let some (.inductInfo _) := env.find? c then
      for f in ["r7a", "neronOggShafarevichSep"] do
        if (env.getProjectionFnInfo? (c ++ Name.mkSimple f)).isSome then carriers := carriers.insert c
  IO.println s!"carriers {carriers.toList}"
  IO.println s!"value-tainted {tainted.size}"
  for c in carriers.toList do
    let mod := (env.getModuleIdxFor? c).map (fun i => env.header.moduleNames[i.toNat]!)
    IO.println s!"C {mod.getD Name.anonymous} {c}"
  for (c, us) in tyUses.toList do
    for u in us do
      rev := rev.alter u (fun o => some ((o.getD #[]).push c))
  let mut types := tainted
  q := tainted.toList.toArray ++ carriers.toList.toArray
  for c in carriers.toList do types := types.insert c
  while !q.isEmpty do
    let c := q.back!
    q := q.pop
    for d in rev.getD c #[] do
      if !types.contains d then
        types := types.insert d
        q := q.push d
  let mut out : Array String := #[]
  for c in tainted.toList do
    let mod := match env.getModuleIdxFor? c with
      | some i => toString (env.header.moduleNames[i.toNat]!)
      | none => "?"
    let uses := ((valUses.getD c #[]).filter (types.contains ·)).toList
    out := out.push s!"T {mod} {c} USES {uses}"
  for c in types.toList do
    if tainted.contains c || carriers.contains c then continue
    let mod := match env.getModuleIdxFor? c with
      | some i => toString (env.header.moduleNames[i.toNat]!)
      | none => "?"
    out := out.push s!"S {mod} {c}"
  IO.println s!"tainted {tainted.size}"
  IO.println s!"value-or-type tainted {types.size}"
  for s in out.qsort (· < ·) do IO.println s
