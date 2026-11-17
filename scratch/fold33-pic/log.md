# fold33-pic log

Base wip/leaf-fold33b 943f1775 (top `sixContactMin_of_open43`, TailZ50; render_open: H 31 fields, strictest 11/20,
37 open). origin/main c1e4ed1b is an ancestor (VERIFIED `git merge-base --is-ancestor`), not merged.
Build: reflink copy of the leaf-fold33b worktree's `.lake/build` (same commit, same lake-manifest, same Mathlib olean;
the worktree had no project build).

## Step 1a: merge origin/wip/phisurj (5507316e, contains 03d7e0f3 and wip/weil-proof)
- merged cleanly (commit fd8cb72e); adds Contrib/OneProof/{PhiAmpleIsogenyWeil, PhiSurjDescent, PhiAmpleIsogenyOpen,
  MumfordSquareMulN, WeilPairingMumfordOpen, WeilFormula, WeilFormulaTheta}.lean, docs, scratch.
- hygiene: scratch files redeclaring HDec.HSyn bundles renamed .lean.txt: scratch/phisurj/{FoldDryRunWeil,
  FoldTailZ49, FrozenTargetDryRun}.lean, scratch/weil-proof/{FoldDryRun, FoldDryRunLF32, FoldDryRunUnread}.lean.
- host paths: none in the merged files (grep /home/, jackmccarthy).

## Step 1b: fold (commit after this entry)
- autofold `scratch/fold33-pic/autofold-weil.json` (phisurj's autofold-weil.json, name changed): dry run
  `strict count: 11/20 on 31 -> 11/19 on 30; strictest 11/20 -> 11/19` (autofold-weil-dryrun.txt); wrote
  `OneProof/H/TailZ51.lean` (`OpenAddedLeaves21` = OpenAddedLeaves20 without `weilPairingMumford`,
  `openAddedLeaves20_of_OpenAddedLeaves21` with `PhiSurj.weilPairingMumford_of_open n.L1 n.L2 t.mumfordTorsionAlgClosed`,
  `sixContactMin_of_open44`). kinds.tsv: autofold's rewrite re-sorted one row and re-quoted the hCM row; replaced by
  HEAD's file minus the `weilPairingMumford` row (minimal diff, same csv content). claims.tsv: row weilPairingMumford
  dropped by autofold.
- `mumfordPhiSurjectiveAC` removal: no copy needed. Readers (VERIFIED grep): TailZ45:123
  (`openAddedLeaves18_of_OpenAddedLeaves19`) and the poincare conversion (homfree reroute :2082), both through
  `PicFix.phiAmpleIsogeny_of_printed l.mumfordKLFiniteSectionAC l.mumfordPhiSurjectiveAC : PhiAmpleIsogeny`. The GM copy
  chain already has `sixContactMin_of_open37_hf_gm (r : OpenResearchLeaves27GM) (t : OpenTextbookLeaves13HF)
  (l : OpenAddedLeaves18)` (GoodModelIsoCopy:2075) and `OpenAddedLeaves18` has `phiAmpleIsogeny` as a field. New module
  `OneProof/H/TailZ52.lean` (bypass to an older generation, as phisurj's FoldTailZ49 on the older top):
  `OpenAddedLeaves22 = {picRepresentableAbVar, picZeroAbVar}`; `openAddedLeaves18_of_OpenAddedLeaves22 (t : OpenTextbookLeaves16)`
  (phiAmpleIsogeny := phiAmpleIsogeny_of_open L1 L2 torsion, weilPairingMumford := weilPairingMumford_of_open ...,
  egaIV as TailZ45); `openTextbookLeaves13HF_of_open16_22` (as openTextbookLeaves13_of_OpenTextbookLeaves14_hf with
  phiAmpleIsogeny_of_open, neronSchemeExtensionExists_of_dedekind from the research leaf as TailZ50);
  `sixContactMin_of_open45 r t l := sixContactMin_of_open37_hf_gm (r27GM of r28GM of r29GM of r) (tb13HF) (added18)`.
  Main: import TailZ52, `l : OpenAddedLeaves22`, `sixContactMin_of_open45`, one docstring paragraph.
- kinds.tsv: row `mumfordPhiSurjectiveAC` (LEAF/LEAF) dropped. No row added.

## Step 1 checks (all VERIFIED; outputs in scratch/fold33-pic/)
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges ZInQKernel.OneProof.H.TailZ51
  ZInQKernel.OneProof.H.TailZ52`: Build completed successfully (14218 jobs) (build_1_phisurj.txt).
- `#print axioms`: sixContactMin_of_open44, sixContactMin_of_open45, ZInQ.OneProof.frozenTarget:
  [propext, Classical.choice, Quot.sound].
- closure (closure_1_phisurj.txt, 271467 constants): PicDict.MumfordPhiSurjectiveAC false,
  PicFix.phiAmpleIsogeny_of_printed false, sorryAx false, OpenAddedLeaves19/20 false, sixContactMin_of_open43 false;
  T09Pic.WeilPairingMumford true but no bundle field has it as type (only `picZeroAbVar : T09Pic.PicZeroAbVar` is
  flagged, expected in step 1); PhiSurj.phiAmpleIsogeny_of_open / weilPairingMumford_of_open true. Bundles:
  OpenResearchLeaves31 24, OpenTextbookLeaves16 3, OpenAddedLeaves22 2 fields.
- hash guard (hashdiff_1_phisurj.txt): before 15313, after 15335, only before 0, only after 22 (11 TailZ51 + 11
  TailZ52), changed 1: ZInQ.OneProof.frozenTarget.
- OpenStatements.lean: open-statements.json 35 open hypotheses.
- render_open.py, --check: **29 H hypotheses, strictest 10/19, 6 others**; "ok: 35 open hypotheses, all classified;
  4 generated files up to date" (base: 31, 11/20, 37 open).
- frontier_crosswalk.py, --check: 232 IDs, 27 matched; up to date.
- DischargesTest rerun: `#discharges: 35 open hypotheses, 9695 theorems checked, 34 discharge one` (was 37, 9464, 38);
  the four `OpenAddedLeaves20.weilPairingMumford` lines (pic-dict reductions) are gone with the field.
- autoform check blueprint: OK: 781 articles, 2343 dependencies, 705 fully proved, 2531 declaration name(s) resolved.

## Step 2a: char-0 reader analysis on the folded tree, merge origin/wip/piczero-char0 (2cc19764)
- FieldTaint (copy of piczero-char0's, seed `picZeroAbVar`, fieldtaint_1.txt, VERIFIED, closure 271467): tainted fields
  t8, t09SymmIsogenyExists, t9, phiAmpleIsogeny, picZeroAbVar, poincareComplement, weilPairingMumford. Edges:
  `openAddedLeaves18_of_OpenAddedLeaves22` computes phiAmpleIsogeny and weilPairingMumford from L2 (phisurj);
  `openTextbookLeaves13HF_of_open16_22` computes poincareComplement; `addedLeaves12_of_open13` computes
  t09SymmIsogenyExists from picZeroAbVar, phiAmpleIsogeny, weilPairingMumford; t9 and t8 as before. Terminal readers
  exactly piczero-char0's three: `gluePieces_of_open4_hf` (t09SymmIsogenyExists, at `[NumberField K]`),
  `g8_g12_of_leaves3_hf` (t9, dead), `glueOutputs_of_leaves3_hf` (t8 from poincareComplement, a `CharZero` statement);
  the rest are the chain theorems passing bundles. So after phisurj every reader of picZeroAbVar is still in
  characteristic 0 (the new fields phiAmpleIsogeny/weilPairingMumford feed only t09SymmIsogenyExists).
- merge origin/wip/piczero-char0: clean. Hygiene (as fold33-piczero): scratch/piczero-char0/{FoldCheck, Iso2,
  RerouteCheck}.lean -> .lean.txt; the first-generation reroute Contrib/OneProof/PicZeroAbVarCharZeroReroute.lean (built
  on 0e3c3125, imported by nothing) moved to scratch/piczero-char0/PicZeroAbVarCharZeroReroute.lean.txt (copies in
  Contrib flood #discharges; the regenerated copy goes to OneProof/H/); the docstring line of PicZeroAbVarCharZero.lean
  naming it updated. Host paths: none.
