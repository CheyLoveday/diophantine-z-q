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
