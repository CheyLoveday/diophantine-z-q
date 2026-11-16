# dcy3-fold results log

- 11-15 23:00 start. Base 094bdd96 (wip/leaf-fold29). origin/wip/dcy3-used (36240662) already an ancestor of the base
  (DeligneComponentsY3Used.lean present, not yet imported by the chain).
  lean/.lake/build was missing: copied from ~/dzq-wt/r6-nf (lean/ identical). Base build rebuilds part of the tree.
- Tools copied from scratch/r6-nf (PruneScan, DeadCascade, DumpCompact incl. Contrib.OneProof, cmp_hashes, prune_lib),
  paths changed to scratch/dcy3-fold/.
- 11-15 23:29 **BASE DOES NOT BUILD.** `lake build +ZInQKernel.OneProof.Main` on 094bdd96: every module up to
  TailZ37 and the Contrib modules build, but ZInQKernel/OneProof/Main.lean fails: `Unknown identifier
  H29Split.LegendreThreeSquares`, `JonesPallX2Y2Z16`, `TYZLemma29PrintedNe3`, `TYZThm21At31`,
  `tyzLemma29Mod2_of_sixLeaves` (Main.lean:66-75). Cause: leaf-fold29 (3b2562f1) hand-folded h29-ne3 into Main but did
  not copy h29-ne3's drop-in scratch/h29-ne3/TYZLemma29Mod2.lean over ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean
  (the tree still has h29-fix's version). origin/wip/leaf-fold29's tip 305280f7 changes only docs.
  Workaround for this task's checks: the drop-in is copied into the working tree LOCALLY ONLY and is never committed
  (that Contrib file is outside this task's allowed edits). The integrator must apply it to leaf-fold29.
