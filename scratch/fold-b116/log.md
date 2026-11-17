# fold-b116 log

Base wip/leaf-fold33b d804d07d (= fork main + fold-b115). H top `HDec.HSyn.sixContactMin_of_open77` (TailZ84,
`OpenResearchLeaves58`). Build tree `.lake/build`, `lean/.lake/build` copied (reflink) from the fold-b115 worktree
(8bef0560; no Lean file differs from d804d07d).

## 0. Base checks (VERIFIED, 11-17 15:17)
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges`: ok (15991 jobs, replayed); frozenTarget
  [propext, Classical.choice, Quot.sound].
- Base hash dump (DumpCompact): 19972 constants (/tmp/fb116/hashes_fold0.txt, not committed).
- **render_open count at base: 30 open (H 29, strictest 5/24, 1 other).**

## Item 1: inbox 83 amendment to ss-faltings (faltingsSemistableHeightBC)
1. Generator `scratch/fold-b116/item1_ssf_amend.py` (text edits only):
   - kinds row `faltingsSemistableHeightBC`: kind published -> consequence; strict/strictest GLUE/GLUE (unchanged);
     flag = the reading desk's text (inbox 83, verbatim); flag_class pending-reading -> note; source locator
     "section 1 (locator UNVERIFIED ...)" -> "§3, p. 354"; rated_by "ss-faltings; the reading desk 11-17 (page read)".
   - leaf docstring `ZInQ.SSFaltings.FaltingsSemistableHeightBC` (Contrib/OneProof/SSFaltings.lean) and its module doc:
     locator §3 p. 354; the claim "the reason he gives is SGA 7 IX 3.3" removed; the Néron-model step
     N'^0 = (N^0)_{R'} (SGA 7 IX Cor. 3.3 / BLR 7.4/3, cited neither by Faltings there nor by the manuscript) named as
     part of the leaf.
   - field docstring in TailZ84 and Main's fold paragraph: "section 1" -> "§3, p. 354", Cor. 3.3 content named inside
     the leaf.
   - Not edited (other declarations' docstrings that say "Faltings 1983 §1" for the stable height in general:
     G0StableBC, HeightDictionary, JavanpeykarDirect, JavanpeykarAnRetype, PrintedStableHeight, LPrefix, TailA, TailY).
2. Build (VERIFIED): `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges
   ZInQKernel.Contrib.OneProof.SSFaltings ZInQKernel.Contrib.OneProof.SSFaltingsGR9 ZInQKernel.OneProof.H.SSFChain
   ZInQKernel.OneProof.H.TailZ84` ok (15991 jobs); frozenTarget standard.
3. Checks (`run_checks.sh 1 hashes_fold0.txt`, VERIFIED): hash guard 19972 -> 19972, no constant changed, none new
   (docstring-only edits; `cmp_fold1.txt`). Closure (`FoldCheck-fold1.txt`): sorryAx absent; state as after fold-b115
   (`SGA7_IX_Cor3_3_Def34` absent, `SGA7_IX_3_5_ForwardGeom_Def34` present). OpenStatements: 30. render_open and
   `--check` ok. DischargesTest: 17 DISCHARGES lines, output file unchanged. frontier_crosswalk 232 IDs, 4 matched,
   `--check` ok. autoform check exit 0 (776 articles, 647 fully proved). gate.sh: GATE=ok.
   kinds rows: none added or dropped (one row edited); claims.tsv unchanged.
   **render_open count after item 1: 30 open (H 29, strictest 5/24, 1 other); 5/24 on 29 (unchanged: the row was
   already GLUE/GLUE).**
4. Wording for the report and landing note: "SGA 7 IX Cor. 3.3 no longer a separate row; its content is named inside
   faltingsSemistableHeightBC".
5. Manuscript check (VERIFIED by reading diophantine_zq.tex): L596-598 ("This extension does not change its stable
   Faltings height", uncited): gap filled by the leaf faltingsSemistableHeightBC, now located at Faltings 1983 §3
   p. 354 (the reading desk's page read; not re-read here: UNVERIFIED by this task) with the Néron-model step
   (SGA 7 IX Cor. 3.3 / BLR 7.4/3) inside the leaf; bibitem faltings1983 L11084-11086 OK.

## Item 2: d2a6b (inbox 76; sga7_IX_3_5_ForwardGeom_Def34 -> elliotWildInertiaTrivial; bypass regenerated on this top)
1. Merged origin/wip/d2a6b 6570dbca (clean; commit 44fd0ac0). Hygiene: scratch/d2a6b BypassFold.lean, ClosureCheck.lean,
   PruneScanBypass.lean (redeclare `HDec.HSyn.OpenResearchLeaves58`) and Discharges.lean (imports the superseded
   Contrib chain) renamed `.lean.txt`; no host paths; no vendored code.
2. Generators copied to `scratch/fold-b116/gen-d2a6b/` and retargeted (d2a6b's own scratch files unchanged):
   TaintD.lean/TaintD2.lean import `OneProof.H.SSFChain`, root `HDec.HSyn.sixContactMin_of_open73_sf` (ss-faltings'
   copy of TailZ80's top; TailZ81-84 are field conversions); gen_chain.py TOP `sixContactMin_of_open73_sf`, module
   order from SSFChain, the r14 edit also matches `raynaudCriterionNF_of14_hf_gm_eb_sf`; gen_bypass.py CHAIN_R
   `OpenResearchLeaves54SF`, CHAIN_TOP `sixContactMin_of_open73_sf`, chain import `ZInQKernel.OneProof.H.D2A6Chain`.
3. Taint (VERIFIED): `lake build D2A6Wrap A6Z30` ok (14424 jobs); TaintD: closure 274018, IX 3.5: 28 carriers (base
   d2a6b on TailZ83: 31, incl. OpenResearchLeaves55-57 above its chain top), 829 T/S lines; TaintD2 28 carriers.
4. `python3 scratch/fold-b116/fold_d2a6b.py`: gen_chain 131 blocks (102 declarations, 29 structures; edits r14 1,
   qml3 1): 90 from SSFChain, 25 EichlerBoundCopy, 9 TailH, 7 HomFree Consumers (d2a6b on TailZ80: 91 from TailZ80,
   same others). Chain written to `ZInQKernel/OneProof/H/D2A6Chain.lean` (top `sixContactMin_of_open73_sf_u` on
   `OpenResearchLeaves54SFU`); d2a6b's superseded `Contrib/OneProof/D2A6Chain.lean` (generated on TailZ80, same
   declaration names) removed with `git rm`. gen_bypass --mode post: `OpenResearchLeaves58` (27 fields) ->
   `OpenResearchLeaves59` (27), top `sixContactMin_of_open78` (numeric names), module `TailZ85`; removed
   `sga7_IX_3_5_ForwardGeom_Def34`, added `elliotWildInertiaTrivial`, mapped `silverbergZarhinThm35`,
   `y3FullThreeRepZ30`; strict 5/24 on 29 -> 5/24 on 29, strictest 5/24 -> 5/24; new row elliotWildInertiaTrivial
   consequence GLUE/GLUE (note), replaces the sga7_IX_3_5_ForwardGeom_Def34 row in kinds.tsv. claims.tsv: no row for
   either field on this base (nothing to drop).
5. Build (VERIFIED): `lake build ZInQKernel.OneProof.H.D2A6Chain ZInQKernel.OneProof.H.TailZ85
   ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.A6Z30` ok (15997 jobs);
   frozenTarget [propext, Classical.choice, Quot.sound]. D2A6Chain has the source's linter warnings (ambiguous
   `open` namespaces), no errors.
6. Checks (`run_checks.sh 2 hashes_fold1.txt`, VERIFIED): hash guard 19972 -> 21006, only before 0, only after 1034
   (D2A6Chain 999, TailZ85 35), changed only `ZInQ.OneProof.frozenTarget` (`cmp_fold2.txt`). Closure
   (`FoldCheck-fold2.txt`, 292618 constants): absent sorryAx, `SGA7_IX_3_5_ForwardGeom_Def34`,
   `SGA7_IX_3_5_ForwardGeom`, the three `RaynaudCriterionNF`, `raynaudPlace_of_R6`, `torsFix_of_descent`,
   `modelG3G6_of_leaves3`, `good_of_QML3`, `SGRSplit.ShimuraIntegralModelRep`, every Cor. 3.3 form,
   `SemistableNeronBaseChange`, `SemistablePersists`, `OpenResearchLeaves58`, `sixContactMin_of_open77`; present
   `RaynaudWildNF`, `ElliotWildInertiaTrivial`, `SilverbergZarhinThm35`, `Y3FullThreeRepZ30`,
   `FaltingsSemistableHeightBC`, `D2A6.R6U`, `sixContactMin_of_open73_sf_u`, `OpenResearchLeaves59`,
   `sixContactMin_of_open78`. **Constants whose name contains `SGA7` or `sga7` in the closure: 0** (no SGA 7 IX 3.3 /
   3.5 row or statement left). Field check: 27 vs 27, only `sga7_IX_3_5_ForwardGeom_Def34` <->
   `elliotWildInertiaTrivial`, no other type differs. OpenStatements: 30. render_open and `--check` ok. DischargesTest:
   18 DISCHARGES lines (was 17; new: `elliotWildInertiaTrivial` by `SZRaynaud.elliot_of_semistableUnipotent`,
   conditional on SemistableUnipotent = IX 3.5: the new field is not stronger than the old). frontier_crosswalk 232
   IDs, 4 matched, `--check` ok. autoform exit 0. gate.sh: GATE=ok (numeric names parse).
   **render_open count after item 2: 30 open (H 29, strictest 5/24, 1 other); strict 5/24 on 29 (count-neutral).**
7. Manuscript check (VERIFIED by reading diophantine_zq.tex): L383-384 (S contains every prime <= 324) OK;
   L529-530 ("The proper model and its universal abelian scheme give good reduction outside the places over S",
   no argument) gap filled (A6Z30: classifying point, valuative criterion, base change, rigidity; on-the-spot bridge
   ofKer, proved); L557-558, L752-753, L781 OK (uses of L529-530); L814-816 (A[3], A[5] if p = 3; Raynaud's
   criterion [silverbergzarhin, Thm 3.5]) OK; L817-818 ("Its wild inertia acts trivially on each V_l(A)", uncited)
   gap filled (citation: the ELLIOT field elliotWildInertiaTrivial); L443-453, L464-472, L472-477 unverified
   (inside the leaf y3FullThreeRepZ30; not re-read); L453-462 OK per d2a6b (not re-checked here: unverified by this
   task). No errors.
