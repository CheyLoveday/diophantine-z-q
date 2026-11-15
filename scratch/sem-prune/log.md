# sem-prune results log

- 2026-11-14 19:35 start. Base 9165959a (leaf-fold14-int). `git merge origin/wip/gap-triage`: already up to date.
- PruneScan.lean taken from origin/wip/prune-scan 095d8050 (unused-argument positions are not uses);
  DeadCascade.lean from the same branch; prune_edit.py precedent: genus-fold 98a02e43.
- Base build `lake build +ZInQKernel.OneProof.Main` started.
- Base build OK (frozenTarget: propext, Classical.choice, Quot.sound). DumpCompact on base: 13414 constants
  (scratch/sem-prune/hashes_before.txt). PruneScan on base (2 min): 68 top fields, 0 unused, prune set empty
  (*-before.txt).
