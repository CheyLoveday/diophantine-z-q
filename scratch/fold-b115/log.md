# fold-b115 log

Base wip/leaf-fold33b 1496913c (= fork main 67950e82 + inbox 71: Tau Ceti Homogeneous.lean restored, CloudW07 lemma
renamed `eval2_const_mul_chart`). H top `HDec.HSyn.sixContactMin_of_open76` (TailZ83, `OpenResearchLeaves57`).
Build tree `.lake/build` and `lean/.lake/build` copied (reflink) from a sibling worktree at the same commit.

## 0. Base checks (VERIFIED, 11-17 14:10)
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges`: ok (15987 jobs, replayed); frozenTarget
  [propext, Classical.choice, Quot.sound].
- Base hash dump (DumpCompact): 18987 constants (/tmp/fb115/hashes_fold0.txt, not committed).
- `render_open.py`: 29 H hypotheses, strictest 5/24, 1 other; `--check` ok, 30 open hypotheses.
- **render_open count at base: 30 open (H 29, strictest 5/24, 1 other).**

## Fold 1: ss-faltings (inbox 74; sga7_IX_Cor3_3_Def34 -> faltingsSemistableHeightBC; bypass, count-neutral)

1. Merged origin/wip/ss-faltings d230fa8e (main f3402e89 merged into it; no conflicts: its Tau Ceti Homogeneous edits
   are already undone by the base's inbox-71 fix, the merge left Homogeneous.lean, HomogeneousCharts.lean and
   ThirdParty/TauCeti/NOTICE as on the base; commit 86231f4c). Hygiene: `scratch/ss-faltings/BypassFold.lean` and
   `BypassCheck.lean` (redeclare `HDec.HSyn.OpenResearchLeaves58SF`) renamed `.lean.txt`; no host paths, no session
   names; build logs on the branch are 8-line truncations (kept); no vendored code.
2. Generator `scratch/fold-b115/fold_ssf.py` (runs ss-faltings' `gen/gen_bypass.py`, then moves the module to the next
   TailZ, edits Main and the kinds row). Finding: with the branch's default names (`OpenResearchLeaves58SF`,
   `sixContactMin_of_open77sf`) `scratch/lane74/gate.sh` FAILS: `autofold: cannot parse Main.lean` (autofold's
   regex `sixContactMin_of_open(\d+) ` does not match `open77sf`). The fold therefore uses the generator's own
   arguments `OpenResearchLeaves58` / `sixContactMin_of_open77` (the names the integrator's note gives). Same text
   otherwise (gen_bypass.py with explicit arguments).
3. Finding: with `SSFChain.lean` in `ZInQKernel/Contrib/OneProof/`, `#discharges` (DischargesTest) lists every
   projection of its copied bundles as a self-match: 246 DISCHARGES lines instead of 16, and render_open copies them
   into CONTRIBUTING.md's worked example (+725 lines). The generated chain copy is therefore moved to
   `ZInQKernel/OneProof/H/SSFChain.lean` (with the earlier copy reroutes NoSGA3Copy, GoodModelIsoCopy,
   EichlerBoundCopy; `git mv`, content unchanged); the proof files `SSFaltings.lean`, `SSFaltingsGR9.lean` stay in
   Contrib. TailZ84's import and docstring path follow.
4. Fold: `ZInQKernel/OneProof/H/TailZ84.lean` (OpenResearchLeaves58, 27 fields = OpenResearchLeaves57 with
   `sga7_IX_Cor3_3_Def34` replaced by `faltingsSemistableHeightBC`; conversion
   `openResearchLeaves57SF_of_OpenResearchLeaves58`; `sixContactMin_of_open77`); Main -> TailZ84,
   `sixContactMin_of_open77`, docstring paragraph; kinds row `sga7_IX_Cor3_3_Def34` replaced by
   `faltingsSemistableHeightBC` (published; flag "pending reading: Faltings 1983 section 1 not read ... locator
   UNVERIFIED ..."; GLUE/GLUE; flag_class pending-reading; label, area_issue of the old row). claims.tsv: no row.
   gen_bypass count line: strict 5/24 on 29 -> 5/24 on 29; strictest 5/24 -> 5/24.
5. Build (VERIFIED): `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.OneProof.H.TailZ84
   ZInQKernel.OneProof.H.SSFChain ZInQKernel.Contrib.OneProof.SSFaltings ZInQKernel.Contrib.OneProof.SSFaltingsGR9` ok
   (15991 jobs); `sixContactMin_of_open76_sf` and `frozenTarget`: [propext, Classical.choice, Quot.sound].
6. Checks (`run_checks.sh 1 hashes_fold0.txt`, VERIFIED): hash guard 18987 -> 19972, only before 0, only after 985
   (SSFChain 950, TailZ84 35), changed only `ZInQ.OneProof.frozenTarget` (`cmp_fold1.txt`). Closure
   (`FoldCheck-fold1.txt`, 292905 constants): sorryAx, `SGA7_IX_Cor3_3_Def34`, `SGA7_IX_Cor3_3` (both),
   `CToPrinted.SGA7_IX_3_3`, `SemistablePersistsSHcp`, `SemistableNeronBaseChange`, `SemistablePersists`,
   `OpenResearchLeaves57`, `sixContactMin_of_open76` absent; `FaltingsSemistableHeightBC`, `SemistableReductionThmIF`,
   `semistableReductionThmIF_of_raynaud`, `OpenResearchLeaves58`, `sixContactMin_of_open77`, `sixContactMin_of_open76_sf`
   present; `SGA7_IX_3_5_ForwardGeom_Def34` present (d2a6b's row, not in this task). Field check: 27 vs 27, only
   `sga7_IX_Cor3_3_Def34` <-> `faltingsSemistableHeightBC`, no other type differs. OpenStatements: 30. render_open and
   `--check` ok. DischargesTest: 16 DISCHARGES lines (base 15; new: `faltingsSemistableHeightBC` by
   `SSFaltings.faltingsSemistableHeightBC_of_ss2`, still assumes `SemistableNeronBaseChange` = the never-stronger
   witness). frontier_crosswalk 232 IDs, 4 matched, `--check` ok. autoform check exit 0 (776 articles, 645 fully
   proved). gate.sh: GATE=ok. `#discharges` cannot show the field (bypass; the old field does not follow from the new
   leaf); the closure check shows it gone. No autofold spec (nothing discharged outright); the fold is reproduced by
   `fold_ssf.py`.
   **render_open count after fold 1: 30 open (H 29, strictest 5/24, 1 other); strict 5/24 on 29 (count-neutral).**
7. Manuscript check (VERIFIED against diophantine_zq.tex): L596-597 OK; L597-598 gap filled (uncited invariance
   sentence, now the leaf faltingsSemistableHeightBC, Faltings 1983 section 1); L598 and L875-876 gap filled ("stable
   Faltings height" occurs only there and is never defined; supplied in Lean); L620-621 gap filled (isogeny step
   needs a common semistable field, supplied at K(A[15])K(B[15])); L814-817 OK; no errors.
