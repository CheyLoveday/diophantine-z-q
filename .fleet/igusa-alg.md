# igusa-alg: report

**Verdict: done.** theta-glue's five closed identities `IgusaAlg 5`, `6`, `7`, `8` and `9` are proved in Lean.
Their statements are copied verbatim. `IgusaAlg 3` and `IgusaAlg 4` are reproved by the same method, which
replaces theta-glue's 21 GB `ring` proofs. With them, the use form of the field `thetaRatiosAlgebraic`
follows from the single composite LEAF `LinYangThetaCurve`:
- `thetaRatiosAtQM_of_linYang : LinYangThetaCurve → ThetaRatiosAtQM`;
- `thetaPointOfFibre_of_linYang : FibreQMPeriod → LinYangThetaCurve → ThetaPointOfFibre`. This is a drop-in
  replacement for `thetaPointOfFibre_of_qm_ratios`.

Both come from theta-glue's `qmThetaSymmetricCurve_of_alg59` and `thetaEightSquare` together with
theta-split's Route 1. The universal `ThetaRatiosAlgebraic` (for all `K` and `A`) is not derived: Route 1
gives only the use form, which is what the consumer needs.

**Method.**
- Rewriting each identity in `s_i = U_i²` halves the degree to `4k`. The pairs of characteristics make the
  odd terms cancel, which was checked exactly with sympy.
- The general theorem `IgusaAlgEval.Data.gen_eq_zero` proves a homogeneous integer identity over every
  commutative ring from one kernel evaluation at `(1, N, N^D, N^{D²})` plus a coefficient bound. It uses
  `decide +kernel` with GMP arithmetic and no `native_decide`. The soundness proof has three parts:
  homogeneity with Kronecker injectivity, a coefficient majorant, and base-`N` uniqueness.
- The seven identities take 8 s and 7 GB. A grid-interpolation alternative timed out at 38 GB.

**What compiles** (VERIFIED, `lake env lean`, no `sorry`, every `#print axioms` = `[propext, Classical.choice, Quot.sound]`):
- `scratch/igusa-alg/IgusaAlg.lean` (imports TailA): 3 min 19 s, 12.1 GB. It contains theta-split's
  ThetaUse body verbatim and theta-glue's ThetaGlue body verbatim except the §7 `ring` proofs.
- `Core.lean`, `Inst.lean` and `Bridge.lean`: Mathlib-only development versions. `Bridge.lean` proves
  `IgusaAlg 3..9` in 1 min 55 s, 11 GB.

**What remains.** The LEAF `LinYangThetaCurve` (theta-glue §5) is the only input left on Route 1. For
integration, drop the GLUE field `∀ k, 5 ≤ k → k ≤ 9 → IgusaAlg k` and use `thetaPointOfFibre_of_linYang`.
`IgusaAlgEval` can become its own module ahead of the ThetaGlue code.

Report: docs/research/igusa-alg.md. Log: scratch/igusa-alg/log.md.
