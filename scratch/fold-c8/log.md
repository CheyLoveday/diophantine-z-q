# fold-c8 log

Base wip/leaf-fold33b b9b85486 (main + fold-b115 + fold-b116). H top `HDec.HSyn.sixContactMin_of_open79` (TailZ86,
`OpenResearchLeaves60`, `OpenTextbookLeaves18`, `OpenAddedLeaves27`). Build tree `.lake/build`, `lean/.lake/build`
reflink-copied from the fold-b116 worktree (627782cf; no Lean file differs from b9b85486).

## 1. Merges (VERIFIED, 11-17 16:10)
- `git merge origin/wip/conrad-b3` (e579047cc): clean, commit d7482351.
- `git merge 8050603b` (PR #86 head, input only): clean, commit f0294b40 (317 added files, all new; no existing file changed).
- Hygiene (commit 90e65c77): 12 scratch dry-run files that declare `HDec.HSyn` bundle generations renamed `.lean.txt`
  (c8-conrad2: C8DryRun, C8DryRunGen, C8DryRunTaint, C8FoldDryRun, gen/fold.lean; c8-conrad3: C8DryRunTaint,
  C8FoldDryRun; conrad-b3: CBDryRun; ht-abvar: HTDryRun, HTDryRunTaint, gen/top_b.lean; ht-merge: HTMergeDryRun).
  Host paths: none in the merged files. Vendored LICENSE/NOTICE files kept (CloudR2Poincare L1, L3, L4; CloudR2Hom C4SourcePort).

## 2. Base build and checks (VERIFIED, 11-17 16:38)
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.C8Printed
  ZInQKernel.Contrib.OneProof.C8CFT ZInQKernel.Contrib.OneProof.ScholzeH1AbVar
  ZInQKernel.Contrib.CloudR2Poincare.FinalUnconditional`: Build completed successfully (16329 jobs; build1.txt).
  PR #86's `CloudR2Poincare/L1/Source20261116/ResidueFieldModels.lean` alone took 2123 s (35 min).
- Base hash dump (DumpCompact): 21041 constants (/tmp/fc8/hashes_fold0.txt, not committed); frozenTarget standard.
- **render_open count at base (kinds.tsv H rows): strict 5/24 on 29, strictest 5/24.**

## 3. Taint and generated fold (VERIFIED, 11-17 16:41)
- `lake env lean scratch/fold-c8/gen/Taint.lean` (c8-conrad2's taint, seeds `t09SymmIsogenyExists`, `phiAmpleIsogeny`,
  `weilPairingMumford`, `detTate`) on the base: closure 292708, 13 carriers (OpenAddedLeaves4PZ..18PZ, GaloisPieces), 71
  tainted; T/S lines: D2A6Chain 41 T + 7 S, PicZeroCharZeroCopy 26 T + 127 S, TailA 1 T + 6 S, TailZ85 1, TailZ86 1,
  Main 1 (`gen/taint_out.txt`, 2 min 17 s). No two tainted declarations share a short name.
- `python3 scratch/fold-c8/fold_c8.py --dry-run`: gen.py 69 blocks, 13 structures, readers replaced [1, 1]
  (`detTate_of_leaves4_pz l.t09SymmIsogenyExists ...` in `gluePieces_of_open4_hf_pz_eb_u`; `g12Det_of_pz m.r14det
  m.detTate ...` in `g8_g12_of_leaves3_hf_pz_eb_u` -> `C8Conrad.g12DetPZ_of_inputs r.r14 r.r13 m.c8 h9 r.r10`); excluded
  (replaced by the top section) `sixContactMin_of_open45_pz_eb_sf_u`, `_open48_eb_k954_sf_u`, `_open72_sf_u`,
  `_open73_sf_u`, `_open78`, `_open79`. Top section edited copies: `GR9.openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf_sf_u_hm`
  (consumer (iii): `hodgeTateDecompAbVar := hHT`), `openAddedLeaves18_hm`, `GR9.sixContactMin_of_open45_pz_eb_sf_u_hm`
  (consumer (ii): `openTextbookLeaves13HF_of_open16_P ... hP`), `GR9.sixContactMin_of_open72_sf_u_hm`,
  `sixContactMin_of_open79_hm`. Dry-run chain compiled first try (7.7 s, no errors), `sixContactMin_of_open79_hm`
  standard axioms.
- **Count printed by the script (autofold's rule): strict 5/24 on 29 -> 5/24 on 29; strictest 5/24 -> 5/24** (as the
  integrator expected; 3 GLUE rows out: picRepresentableAbVar, kleimanPicZeroProper954SiteQ, hodgeTateDecompOr; 3 GLUE
  rows in: conradAppB, scholzeH1AbVar, t10TateDuality; poincareComplement proved by PR #86, no row).

## 4. The fold (VERIFIED, 11-17 16:43)
- `python3 scratch/fold-c8/fold_c8.py`: wrote `ZInQKernel/OneProof/H/C8Chain.lean` and `TailZ87.lean`
  (`OpenResearchLeaves61` = 60 without hodgeTateDecompOr; `OpenAddedLeaves28` = {conradAppB, scholzeH1AbVar,
  t10TateDuality}; `openResearchLeaves60_of_OpenResearchLeaves61 n l` fills hodgeTateDecompOr by
  `DeRhamScholze.HTMerge.hodgeTateDecompOr_of_scholzeH1Milne l.scholzeH1AbVar l.t10TateDuality`;
  `sixContactMin_of_open80 r t l` with `poincareComplement_proof` and `c8Inputs_of_leaves`), switched Main.lean,
  kinds.tsv (3 rows dropped, 3 added). claims.tsv / volatile.tsv not touched (no row for any of the six fields).
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.OneProof.H.C8Chain
  ZInQKernel.OneProof.H.TailZ87`: Build completed successfully (16331 jobs, 30 s); frozenTarget
  [propext, Classical.choice, Quot.sound].
