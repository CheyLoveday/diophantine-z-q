# semistab-assembly results log

## 11-17 04:30 setup
- Base 8914890c1. Statements read (VERIFIED, read in tree):
  - `ZInQ.HeightFix.IsSemistableRes` PrintedStableHeight.lean:578; `isSemistable_of_res` :590.
  - `ZInQ.R3Residual.IsAnStableHeight` AnalyticStableHeight.lean:710 (clause `IsSemistableRes 𝒩`),
    `BostLowerBoundAn` :856, `GaudronRemondThm14An` :864.
  - `ZInQ.SemiAbDescend.isClosed_range_openSubgroup` SemiAbelianDescendsPerfect.lean:411 (IsAlgClosed).
- Finding (VERIFIED by reading): `HasSemiAbelianIdentityComponent` / `HasSemiAbelianIdCompTorus` assert an
  open *connected* subgroup U, not that U is G⁰; the print says G⁰. The gap is "U clopen".
- Plan: new file ZInQKernel/Contrib/OneProof/SemistablePrintedReadings.lean (namespace ZInQ.SemistabAssembly).
  Closedness over any field: base change to k̄; projection integral (Mathlib IsIntegralHom.SpecMap_iff,
  IsIntegralHom ⇒ UniversallyClosed) and surjective, so U = p(p⁻¹U) closed. (Uses closedness of p rather
  than openness: simpler, same conclusion.)
- Build of AnalyticStableHeight + SemiAbelianDescendsPerfect started (not built in worktree).
