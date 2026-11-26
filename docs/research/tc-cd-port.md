# tc-cd-port: vendoring Tau Ceti's cd_ℓ(G_K) = 2 and local duality for finite modules

- Both roots build: NumberTheory.ClassFieldTheory.Local.CohomologicalDimension.AbsoluteGaloisGroup
  and NumberTheory.ClassFieldTheory.Local.Duality.FiniteModule (under ZInQKernel.Contrib.TauCeti.),
  with `lake build`, no errors.
- The target theorem builds. Its exact type (`#check`, scratch/tc-cd-port/Axioms.lean):

  ```
  @TauCeti.ClassFieldTheory.cohomologicalDimensionAt_absoluteGaloisGroup_eq_two : ∀ {K : Type} [inst : Field K]
    [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K] (ℓ : ℕ)
    [Fact (Nat.Prime ℓ)], TauCeti.cohomologicalDimensionAt ℓ (Field.absoluteGaloisGroup K) = 2
  ```

  `#print axioms` output:

  ```
  'TauCeti.ClassFieldTheory.cohomologicalDimensionAt_absoluteGaloisGroup_eq_two' depends on axioms: [propext, Classical.choice, Quot.sound]
  'TauCeti.ClassFieldTheory.dualityMap_bijective_of_smul_kummerCoeff_eq_self' depends on axioms: [propext, Classical.choice, Quot.sound]
  'TauCeti.cohomologicalDimensionAt_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
  'TauCeti.ContCohomology.subsingleton_continuousCohomology_ofDiscreteModule_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
- New modules: 103. Locally changed files: 0 (all 103 copied unmodified apart from the
  mechanical provenance line and import rewriting). MathlibBackport additions: none.
- No count change: this bump retires no frozen field by itself.

## Source

- Repository: https://github.com/TauCetiProject/TauCeti
- Commit: 5a01f5fe3621126cccf9ba22e700493cbc7b7156 (the pin of the earlier vendorings)
- License: Apache-2.0 (ThirdParty/TauCeti/LICENSE)
- Authors: The Tau Ceti contributors
- Location: ZInQKernel/Contrib/TauCeti/<path>; each file keeps the Tau Ceti copyright header
  and carries the provenance line
  `-- Vendored from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 5a01f5fe3621, module TauCeti.<module>), Apache-2.0.`
  Imports `TauCeti.X` are rewritten to `ZInQKernel.Contrib.TauCeti.X`.
- A Source-list entry for this bump is appended to ThirdParty/TauCeti/NOTICE.

## Module list

The union of the import closures of the two roots at the pin has 521 modules (target root 474,
FiniteModule root 397). 418 are already vendored on the base (at the same path under
ZInQKernel/Contrib/TauCeti/, or, for LinearAlgebra.Exact only, under Backport/). The 103 new
modules are listed in scratch/tc-cd-port/modules.txt, also reproduced below. The two bridge
lemmas are in the closure: `TauCeti.cohomologicalDimensionAt_le_iff` is in
RepresentationTheory/Homological/ContCohomology/CohomologicalDimension/Basic.lean (new), and
`TauCeti.ContCohomology.subsingleton_continuousCohomology_ofDiscreteModule_iff` is in
RepresentationTheory/Homological/ContCohomology/RestrictScalars.lean (already vendored).

The host's closure and copy tools were not available, so the closure and the copy were done by
the scripts scratch/tc-cd-port/closure.py and scratch/tc-cd-port/port.py. port.py never
overwrites an existing file, and it rewrites imports to the Backport/ path for a module that is
vendored only there. The only such import is TauCeti.LinearAlgebra.Exact, imported by
Topology/Algebra/Group/Profinite/ProP/Devissage.lean, which now imports
ZInQKernel.Contrib.TauCeti.Backport.LinearAlgebra.Exact. No second copy of Exact exists.

## Already vendored modules of the closure that differ from the pin

These copies were kept unchanged. All eight already carry a "Modified for the Z-in-Q kernel"
line from earlier tasks (scratch/tc-cd-port/vdiff.py compares them modulo the mechanical changes):

- Backport/LinearAlgebra/Exact.lean: the commit-4d91513e version (task t40-tate), not the
  commit-5a01f5fe one; it is a superset (extra declarations and the Mathlib.Algebra.Module.Projective import).
- NumberTheory/LocalField/UnitFiltration/Pow.lean: shim, declarations removed, the module
  UnitFiltration/Pow/Basic imported instead (task stab-clash). The new modules build against it.
- RepresentationTheory/FDRep.lean: shim, declarations removed, FDRep/Basic imported instead
  (task stab-clash). The new modules build against it.
- RepresentationTheory/Homological/ContCohomology/Coinduced/Discrete.lean: explicit `G A`
  arguments in the IsZeroApply/IsAddApply/IsSMulApply instances.
- RepresentationTheory/Homological/TateCohomology/TrivialityCriterion.lean: `isPGroup'`.
- Topology/Algebra/Group/Profinite/Generation.lean: `rfl` after `simp`.
- Topology/Algebra/Group/Profinite/Sylow/Basic.lean: `isPGroup'`.
- Topology/Algebra/Group/Profinite/Sylow/Existence.lean: `isPGroup'`.

## Local changes

None. None of the known fixes (`isPGroup'`, explicit `G A`, closing `rfl`) was needed in a new
file, and no file-level set_option was needed. A textual scan of the 103 new files finds no
`sorry`, `native_decide` or `axiom`.

## Comparison with the contributor draft

The contributor draft commit (fork PR #8, 1f3ef0e3b81bf223d11c619172392597c43c792b) is not in the
local repository, so the cross-check was skipped. The draft is reported to have 105 files,
and this list has 103 modules. The brief's static estimate of "about 104" probably counted
LinearAlgebra.Exact, which this list leaves out because it is vendored under Backport/.
The draft's other file may be its NOTICE. Neither point could be checked.

## Clash and hash guard

- scratch/tc-cd-port/ClashTC.lean imports both roots together with the 53 existing top modules of
  ZInQKernel/Contrib/TauCeti (modules not imported by another vendored module;
  scratch/tc-cd-port/tc-top-modules.txt). `lake env lean` succeeds with no output, so there is no
  name clash with the existing vendored Tau Ceti code.
- scratch/tc-cd-port/Clash.lean adds ZInQKernel.OneProof.Main to these imports. It was not run:
  building OneProof.Main's import closure in this worktree was stopped at the 2-hour limit of a
  background job (4104 modules built, no errors; all 53 TauCeti top modules done, OneProof.Main
  not reached). A static check was done in its place:
  scratch/tc-cd-port/NewDecls.lean lists the 1259 non-internal declarations of the 103 new
  modules (scratch/tc-cd-port/new-decls.txt), 86 of them outside namespace TauCeti.
  - None of the 86 is defined in the same namespace anywhere in ZInQKernel outside
    Contrib/TauCeti. The only same-named theorem, `restrict_surjective_of_discrete`, lives in
    namespace `P2MW.….C3Aux`, not in `ContinuousMap`.
  - The only two non-TauCeti files that open namespace TauCeti
    (ZInQKernel/Contrib/OneProof/PointedGenusZeroFunctionField.lean and
    ZInQKernel/Contrib/RC53Assist/PullbackScalar/ResidueComparisonProof.lean) declare none of
    the 1259 names.
  - Remaining for the integrator: run Clash.lean once OneProof.Main is built.
- `git diff --name-status 162d4636b..` shows only A lines and one M line
  (ThirdParty/TauCeti/NOTICE).

## Build measurements

LEAN_NUM_THREADS=4, CPUQuota=1600%, MemoryMax=48G, nice. Mathlib prebuilt, and no ZInQKernel
module of the closure built in the worktree beforehand. Host load average 3 to 14.

- Full build of both roots: 523 ZInQKernel modules compiled (the 103 new ones plus 420 already
  vendored modules of the closure and its Backport/ imports). Wall-clock 8 min 26 s, user 39 min 4 s.
  The new modules alone are a subset of this.
- Warm rebuild (no change): 2.6 s.

## New modules (103)

- TauCeti.Algebra.Category.ModuleCat.Topology.FilteredColimits
- TauCeti.Algebra.Group.TypeTags.Hom
- TauCeti.Algebra.GroupAction.Trivial
- TauCeti.Algebra.Module.ZMod.Dual
- TauCeti.Algebra.Module.ZMod.Injective
- TauCeti.Algebra.Module.ZMod.SMulCommClass
- TauCeti.Data.ENat.LeastBound
- TauCeti.Data.ZMod.MulCastHom
- TauCeti.Data.ZMod.TrivialAction
- TauCeti.FieldTheory.GaloisCohomology.BrauerTorsion
- TauCeti.FieldTheory.GaloisCohomology.KummerCoeffProP
- TauCeti.FieldTheory.GaloisCohomology.Steinberg
- TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
- TauCeti.FieldTheory.Kummer.Cyclic
- TauCeti.GroupTheory.PGroup.Additive
- TauCeti.GroupTheory.PLowerCentralSeries
- TauCeti.LinearAlgebra.BilinearMap.IntLinear
- TauCeti.NumberTheory.ClassFieldTheory.Brauer.Kummer.Basic
- TauCeti.NumberTheory.ClassFieldTheory.Brauer.Kummer.Corestriction
- TauCeti.NumberTheory.ClassFieldTheory.Brauer.RootsOfUnity
- TauCeti.NumberTheory.ClassFieldTheory.Brauer.Torsion
- TauCeti.NumberTheory.ClassFieldTheory.FiniteCohomology.Basic
- TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.DegreeThree
- TauCeti.NumberTheory.ClassFieldTheory.Local.CohomologicalDimension
- TauCeti.NumberTheory.ClassFieldTheory.Local.CohomologicalDimension.AbsoluteGaloisGroup
- TauCeti.NumberTheory.ClassFieldTheory.Local.CohomologicalDimension.RootsOfUnity
- TauCeti.NumberTheory.ClassFieldTheory.Local.CyclicClass
- TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.FiniteModule
- TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.TrivialZMod
- TauCeti.NumberTheory.ClassFieldTheory.Local.HilbertPairing
- TauCeti.NumberTheory.ClassFieldTheory.Local.Symbol
- TauCeti.NumberTheory.ClassFieldTheory.MuNRep
- TauCeti.NumberTheory.LocalField.Cohomology
- TauCeti.NumberTheory.LocalField.Kummer
- TauCeti.NumberTheory.Padics.DyadicUnits
- TauCeti.NumberTheory.Padics.GeneratedClosedSubgroups
- TauCeti.NumberTheory.Padics.TwistedUnits
- TauCeti.RepresentationTheory.Homological.ContCohomology.Annihilation
- TauCeti.RepresentationTheory.Homological.ContCohomology.ClosedSubgroup
- TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
- TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClosedSubgroup
- TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ContinuousMulEquiv
- TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.IndexNotDvd
- TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Restriction
- TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.RightExact
- TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.SingleDegree
- TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.TrivialFp
- TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.FiniteIndex
- TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.InternalHom
- TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Pairing
- TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Torsion
- TauCeti.RepresentationTheory.Homological.ContCohomology.ConnectingMapComparison
- TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Cohomology
- TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Comparison
- TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.ConnectingMap.Basic
- TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.Basic
- TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.DimensionShifting
- TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.FourLemma
- TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.OpenSubgroup
- TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.RightExact
- TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.TrivialAction
- TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Functoriality
- TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Graded.Basic
- TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Graded.Comm
- TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality
- TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product
- TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.RestrictScalars
- TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Restriction
- TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Shapiro
- TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialFp.Basic
- TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeCast
- TauCeti.RepresentationTheory.Homological.ContCohomology.Devissage
- TauCeti.RepresentationTheory.Homological.ContCohomology.DiscreteGroup
- TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteCoefficients
- TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.AllDegreeColimit
- TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Canonical
- TauCeti.RepresentationTheory.Homological.ContCohomology.Finiteness
- TauCeti.RepresentationTheory.Homological.ContCohomology.H2ZMod
- TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Comparison
- TauCeti.RepresentationTheory.Homological.ContCohomology.ProjectionFormula
- TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp
- TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Cup
- TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Explicit
- TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialGroup
- TauCeti.Topology.Algebra.ContinuousZModDual
- TauCeti.Topology.Algebra.Group.FrattiniSeries
- TauCeti.Topology.Algebra.Group.Hom
- TauCeti.Topology.Algebra.Group.LowerCentralSeries
- TauCeti.Topology.Algebra.Group.Profinite.ProP.Burnside
- TauCeti.Topology.Algebra.Group.Profinite.ProP.CohomologicalDimension
- TauCeti.Topology.Algebra.Group.Profinite.ProP.Devissage
- TauCeti.Topology.Algebra.Group.Profinite.ProP.FixedPoints
- TauCeti.Topology.Algebra.Group.Profinite.ProP.Frattini.Basic
- TauCeti.Topology.Algebra.Group.Profinite.ProP.Frattini.Step
- TauCeti.Topology.Algebra.Group.Profinite.ProP.MaximalSubgroup
- TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicUnits
- TauCeti.Topology.Algebra.Group.Profinite.ProP.Procyclic
- TauCeti.Topology.Algebra.Group.Profinite.ProP.ZModTwist
- TauCeti.Topology.Algebra.Group.Profinite.Sylow.CohomologicalDimension
- TauCeti.Topology.Algebra.Group.Torsion
- TauCeti.Topology.Algebra.GroupAction.InternalHom.DoubleDual
- TauCeti.Topology.Instances.ZMod
- TauCeti.Topology.Separation.Profinite
