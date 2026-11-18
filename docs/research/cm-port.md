# cm-port: merged; fold blocked by the old Raynaud premise

**VERIFIED (source).** Merge `fe56e1880` brings `151c02161` and its `fe5ad6a96` ancestor onto fork main `41892618b`. The merge adds the original CM order proof and the pre-fold CM fibre split provider unchanged. The requested port stops at the provider’s fifth argument: `PkgI2.RaynaudCriterionNF.{0}` is missing from Main’s current bundles and has no supplier in their existing conversion chain. `OpenResearchLeaves63.cmFibreSplit` is still open.

- Before: **H strict LEAF/GLUE 5/28 on 33**.
- After this merge: **H strict LEAF/GLUE 5/28 on 33**.
- If `cmFibreSplit` is discharged without adding a field: **H strict LEAF/GLUE 5/27 on 32** (computed projection only).

**Manuscript check:** Nothing new; `cm-curve-order` checked `diophantine_zq.tex`, proof of `thm:height`, L582–587.

## Inputs at the live top

**VERIFIED (source).** [Main](../../ZInQKernel/OneProof/Main.lean) uses `sixContactMin_of_open82` from [TailZ89](../../ZInQKernel/OneProof/H/TailZ89.lean) on `OpenResearchLeaves63`, `OpenTextbookLeaves18` (empty) and `OpenAddedLeaves28`. The existing [provider](../../ZInQKernel/Contrib/OneProof/CMCurveOrder.lean#L245) has conclusion exactly `HDec.CMBranch.CMFibreSplit`. Its arguments trace as follows:

| Input | Supplier on the live route |
| --- | --- |
| T27, `QMLattice.YuB6Alg` | `QMLattice.yuB6Alg_of'` from the existing uniformization, GAGA and geometric torsion proofs. |
| T6, `HomFreeC.HomFreeFiniteC` | `HomFreeC.homFreeFiniteC` from `uniformizationLeafAll_proof` and `mumfordTorsionAlgClosed_proof`. |
| G2, `G0ModField.FibreCoverExists` | `fibreCoverExists_of_propTSAll'` with `propTSAll_of_pieces3_y3c` and `unramifiedConjugates_proved`, already called in [Y3Copy5](../../ZInQKernel/OneProof/H/Y3Copy5.lean#L1669). The live moduli and vertical witness inputs use `r.y3ToP1j` and `r.heckeSqrtBranchAny` through the existing `Y₃` conversions. |
| `PkgI2.NeronOggShafarevich` | `NOSSepDict.neronOggShafarevich_of_sep r.neronOggShafarevichSep`. |
| `PkgI2.RaynaudCriterionNF` | **Missing.** The former supplier used `ReductSplit.SemistableUnipotent`, previously obtained from `sga7_IX_3_5_ForwardGeom_Def34`. |
| `PkgI2.TorsionStructure` | T5 from `mumfordTorsionAlgClosed_proof` via the existing `AvSplit` conversions. |

## Known issues

**VERIFIED (source).** [The old Raynaud premise](../../ZInQKernel/OneProof/H/LPrefix.lean#L794) requires `(σ − 1)² = 0` on prime power torsion for **every** inertia element. [The old supplier](../../ZInQKernel/OneProof/H/TailZ80.lean#L2431) calls `GapNeron.raynaudCriterion_leavesNF` with `r.semistableUnipotent`. The live [Y3Open conversion](../../ZInQKernel/OneProof/H/Y3Open.lean#L385) instead constructs `HDec.D2A6.R6U` from `silverbergZarhinThm35`, `elliotWildInertiaTrivial`, `neronSchemeExtensionDedekind` and `y3FullThreeRepZ30`. The first component only controls wild inertia; the second supplies the integral `Y₃` model. In particular the similarly named `GR9.raynaudCriterionNF_of14_hf_gm_eb_sf_u_y3c` returns `R6U`. This is the replacement documented in [d2a6b](d2a6b.md), following `thm:height` L529–530 for good reduction and L814–818 for wild inertia. The old `cmHomFieldModel_of` still calls `good_of_QML3` with the stronger premise.

**SPECULATIVE (integration direction, not tried).** A later port could reuse `good_of_QML3U`, which the live path already calls at the kernel field step, in an `R6U` version of `cmHomFieldModel_of`. The existing curve order and matrix unit proofs would still apply, and the proposed consumer would remain `CMFibreSplit`. The assigned port calls for stopping when the original provider’s input is missing, so this reroute was left untouched.

The merged proof’s inherited on-the-spot arguments and the difference between the manuscript’s Hodge centralizer and the chain’s Yu supplier are documented in [cm-curve-order](cm-curve-order.md). This port adds no mathematical argument, leaf, or GLUE and changes no consumer statement. There are no new leaves to rate.

## Verification and handoff

**VERIFIED (computed).** [The scratch copy](../../scratch/cm-port/Statement.lean) and the merged `CMCurveOrder324` have the same Prop body byte for byte as `CMCurveOrder` at `324f0655a`. The merged files retain [the original verification transcript](../../scratch/cm-curve-order/MainDryRun.txt), which shows the three standard axioms for the order proof, its fibre split provider and the earlier open78 fold. That transcript is for the earlier bundles.

**VERIFIED (compiled).** The scratch statement check exited 0 with the previous task’s compiled imports. It checks `Iff.rfl` and applies `cmCurveOrder324_of` to T6. The [new transcript](../../scratch/cm-port/Statement.txt) shows `propext`, `Classical.choice` and `Quot.sound` for both `cmCurveOrder324_of` and `cmFibreSplit_of_curveOrder324`. This check does not import Main.

`Main.lean` and `kinds.tsv` are unchanged, including the four headline binders `hRC`, `h54`, `hB`, `hK`. With the input missing, there is no executable autofold spec, generated live fold, or new `FrozenTarget` or `#discharges` dry run for Main.
