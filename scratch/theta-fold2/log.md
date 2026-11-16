# theta-fold2 results log

- 11-16 01:46 start. Base 47aaf586 (wip/leaf-fold31). Merged origin/wip/theta-direct (584bbb24, includes 311bd23a).
  Tools (DumpCompact, PruneScan, DeadCascade, cmp_hashes, prune_lib, kinds_counts) copied from scratch/pi0-fold, paths changed.
  lean/.lake/build copied from ~/dzq-wt/pi0-fold (lean/ZInQ identical).
- Plan: ThetaDirect's import closure reaches TailZ24 (via ThetaModularityM46, GammaStarArea; TailK not importable from it),
  so TailK cannot import the proof. But TailZ25 (sixContactMin_of_open19) is outside the closure: thread hθ only through
  gluePieces_of_open4 and sixContactMin_of_open4..open18, and supply the proof in TailZ25. open19..open35, Main and
  Contrib callers (X0ModuliUsed calls open29) keep their signatures. No Contrib file calls open4..open18 (grep).
- 02:12 base build OK (13697 jobs; first attempt hit the 10-min background limit and was restarted), frozenTarget
  axioms standard. DumpCompact 17299 constants (hashes_before.txt). PruneScan base: 25 + 10 + 9 + 1 = 45 fields,
  0 unused (prunescan-base-out.txt). kinds before: H rows 45, strict 34 LEAF / 11 GLUE, strictest 34 / 11.
- 02:27 step 1 (plumb.py) build OK (13706 jobs; +ThetaDirect modules), frozenTarget axioms standard. PruneScan step 1:
  exactly OpenAddedLeaves17.thetaRatiosAlgebraic unused; prune set = the field in OpenAddedLeaves4, 6, 7, 8, 9, 12-17
  (11 entries, prune-set-step1.txt; the same as theta-direct's patch).
- 02:33 step 2 (prune.py, prune_out.txt: 11 fields, 12 assignments, 1 constructor element edited). No dead readers
  left on this base (addedLeaves5_of_open6, addedLeaves11_of_open12, sixContactMin_of_open16 already gone).
  Module docs of TailK's moved block and TailZ25 updated. kinds.tsv/claims.tsv rows deleted (removed-rows.txt).
  kinds after: H rows 44, strict 34 LEAF / 10 GLUE, strictest 34 / 10.
