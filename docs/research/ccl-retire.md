# Cai–Chen–Liu retirement

The retirement applies cleanly to pinned main
`2ba691fde6bfb9e514a429414ba92a6c6893a63f`. The consumer audit found
no new Lean dependency on a deleted declaration. All 25 Lake targets
passed, and the 21-declaration axiom check passed. The count lowered
is **none**. The staged chain supplies the full-anchor witness after
proving the unit factor is one. [Retirement plan](ccl-unit-index2.md#retirement-at-fold) ·
[Consumer audit](../../scratch/ccl-retire2/log.md)

## Deleted declarations and files

Paths below are relative to `ZInQKernel/Contrib/`. Structure-generated
declarations are covered by the removal of their parent structures.

- `OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean` contained
  `e2ProviderOn`, `e2ProviderOn_succ`, `CommonCoordinateInputsGenuineE2`
  (fields `elliptic`, `milne`, `iwasawa`, `chains`),
  `commonCoordinateInputsGenuineK_of_E2`,
  `commonCoordinateInputsNF_of_genuineE2`, and
  `commonCoordinateTarget_of_genuineE2`.
- `OneProof/RC/Wiring/CommonCoordinate18E2.lean` contained
  `classSupport`, `ActualPresentation.ps_getD_pos`,
  `ActualPresentation.ps_getD_prime`, `E2ChainInputs`, and `e2Provider`.
  The fields of `E2ChainInputs` were `cp`, `emb`, `κ`, `print`,
  `hψ`, `d`, `hd`, `hd2`, `hdS0`, `htwo`, `hgood`, `hsep`,
  `hq`, `hsplit`, `f`, `hf`, `hθ`, and `hfd`. Its namespace
  contained `chainCond_pos`, `chainCond_coprime`, `cond_not_mem`,
  `mem_S_of_cond`, `classSupport_subset`, `hSd`, `hm`, `hgood'`,
  `hpl`, `hfd_cond`, `datum`, `anchor`, `hcop`, `hadmD`, `hsplitD`,
  `g`, `hanti`, `hwd`, `stepFactor_eq`, `hG`, and `hloc`.
  The staged import now takes `chainCond` and `dvd_chainCond` from
  `OneProof/RC/Wiring/ChainCond.lean` and imports its other
  dependencies directly. [Conductor definitions](../../ZInQKernel/Contrib/OneProof/RC/Wiring/ChainCond.lean)
- `CloudB3E2Norm/H20HeegnerNorm.lean` contained `HeegnerTransportAt`,
  `hnorm_of_normRelations`, `hnorm_of_print`, and `nonVacuity_transport`.
- `CloudB3E2Norm/H20Transport.lean` lost `hnorm_of_print_on` and now
  imports `PrintsArith.Heegner` directly for its subgroup transport.
  [Subgroup transport](../../ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean)
- `CloudB3E2Norm/H20Anchor.lean` lost `CCLGenuine` and
  `hnorm_of_genuine_print`. The full-anchor dictionary uses
  `GenuineHeegnerAnchor` and its coordinate lemmas.
  [Anchor](../../ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean)
- `OneProof/RC/PrintsArith/Heegner.lean` lost
  `CCLThm2_15Applied`. The staged application starts with
  `CCLThm2_15AppliedWithUnits`, then derives the anchored
  `HeegnerPointData.NormRelations` that the additive transport takes.
  [Arithmetic interface](../../ZInQKernel/Contrib/OneProof/RC/PrintsArith/Heegner.lean)

## Respelled premises

Each premise unfolds the retired abbreviation at the same full anchor.

| Declaration | Explicit premise |
| --- | --- |
| `H20DictFields.hnorm_of_full_anchor` | `∃ D : HeegnerPointData E, D.NormRelations ∧ FullAnchor E K p ι κ D` |
| `H20PresClass.gx_step_anchored` | `∃ D : HeegnerPointData E, D.NormRelations ∧ FullAnchor E K cp emb κ D` |
| `H20PresClassOf.gx_step_heegner` | `∃ D : HeegnerPointData E, D.NormRelations ∧ FullAnchor E K cp emb κ D` |
| `H20PresClassMatch.gx_step_heegner_at` | `∃ D : HeegnerPointData E, D.NormRelations ∧ FullAnchor E K cp emb κ D` |

## Builds and axioms

Each module ran in a separate Lake invocation under the 60 GiB memory
cap. The targets cover the proof and discharge roots, the default kernel
root, the direct importers from the consumer audit, and the imports of
the axiom check. The three retired module paths have no surviving
imports.

```text
PASS ZInQKernel.OneProof.Main
PASS ZInQKernel.OneProof.Discharges
PASS ZInQKernel.Contrib.OneProof.RC.Wiring.ChainCond
PASS ZInQKernel.Contrib.CloudB3E2Norm.CentralSpec
PASS ZInQKernel.Contrib.CloudB3E2Norm.E2ChainActual
PASS ZInQKernel.Contrib.CloudB3E2Norm.H20AmbientS
PASS ZInQKernel.Contrib.CloudB3E2Norm.H20DictFields
PASS ZInQKernel.Contrib.CloudB3E2Norm.H20PairedLift
PASS ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassMatch
PASS ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassOf
PASS ZInQKernel.Contrib.CloudB3E2Norm.H20ThetaMono
PASS ZInQKernel.Contrib.CloudB3E2Norm.H20Transport
PASS ZInQKernel.Contrib.CloudB3E2Norm.H20Untwisted
PASS ZInQKernel.Contrib.CloudB3E2Norm.HeegnerRCBridge
PASS ZInQKernel.Contrib.CloudB3E2Norm.RingClassMono
PASS ZInQKernel.Contrib.OneProof.RC.CCLUnitIndex.Units
PASS ZInQKernel.Contrib.OneProof.RC.HeegnerAnchor.Comparison
PASS ZInQKernel.Contrib.OneProof.RC.O7Actual.Reduction
PASS ZInQKernel.Contrib.OneProof.RC.PrintsArith.Bundle
PASS ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19E2
PASS ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19Leaf
PASS ZInQKernel
PASS ZInQKernel.Contrib.CloudB3E2Norm.H20Anchor
PASS ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner
PASS ZInQKernel.Contrib.CloudB3E1RingClass.SupportReq
```

`scratch/ccl-retire/Check.lean` already included
`#print axioms ZInQ.OneProof.frozenTarget`. All 21 declarations
in the rerun use only `propext`, `Classical.choice`, and `Quot.sound`.
[Build log](../../scratch/ccl-retire2/builds.txt) ·
[Axiom output](../../scratch/ccl-retire2/axioms.txt)

## Count

**None.** The import closure on pinned main contains 10,580 project
modules for `frozenTarget` and 380 for the type of `hRC`. Each excludes
every module that owned a deleted declaration. The merge gives the
same result. `hRC` remains an explicit hypothesis in
`ZInQKernel/OneProof/Main.lean:265`. Its type is
`ZInQKernel/Contrib/OneProof/SelmerTwoPower.lean:217` and its GLUE
entry is at `docs/one-proof/kinds.tsv:23` and
`docs/one-proof/OPEN.md:149`. The retirement removes zero
`frozenTarget` fields and zero GLUE or LEAF rows. The H part
has 21 hypotheses, 4 published and 17 GLUE under the strict reading
at `docs/one-proof/OPEN.md:16` and `docs/one-proof/OPEN.md:18`.
[Closure evidence](../../scratch/ccl-retire2/log.md#import-closure-and-count)

## Known issues

- The retired unweighted application allowed `d = 1` under generic
  premises that can hold at `D_K = -4`. The staged path uses the
  manuscript's companion field exclusion and proves the unit factor
  equals one before applying the unweighted norms.
  [Prior counterexample checks](../../scratch/ccl-unit-index/Check.lean) ·
  [Manuscript point relations](../../diophantine_zq.tex#L2914)
- The earlier level shortcut fails modulo 8 because `2² ≡ −4 mod 8`.
  The modulo-16 proof excludes the two exceptional discriminants
  under its level hypothesis. The staged path uses the companion
  data. [Unit-index proofs](../../ZInQKernel/Contrib/OneProof/RC/CCLUnitIndex/Units.lean)
- The report uses the recorded reading of Cai–Chen–Liu, Theorem 2.15,
  Trans. Amer. Math. Soc. 370 (2018), p. 3730. The manuscript's use at
  `diophantine_zq.tex:2914` through `diophantine_zq.tex:2936` agrees
  with that reading. The journal page still awaits an independent
  reread. Global compatibility of the point family and the
  analytic-to-algebraic parametrization comparison remain inputs.
  [Prior source and manuscript audit](ccl-unit-index2.md#manuscript-check)
- A few Lean comments still name the retired witness or wiring. The
  exact references are in the audit. [Comment references](../../scratch/ccl-retire2/log.md#exact-name-matches-on-the-merged-base)
