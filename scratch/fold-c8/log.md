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
