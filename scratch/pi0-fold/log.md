# pi0-fold results log

- 11-16 00:10 start. Base ec797e65 (wip/leaf-fold30). lean/.lake/build missing: copied from ~/dzq-wt/dcy3-fold (lean/ZInQ identical).
  Tools copied from scratch/dcy3-fold (DumpCompact incl. Contrib.OneProof, PruneScan, DeadCascade, cmp_hashes, prune_lib), paths changed.
- 00:20 **BASE DOES NOT BUILD** (ec797e65 = origin/wip/leaf-fold30 minus its docs-only tip ddbcfd61):
  `lake build +ZInQKernel.OneProof.Main` reports a build cycle TailZ23 -> TailZ40 -> TailZ39 -> ... -> TailZ24 -> TailZ23.
  Cause: module-name collision. rigid-prune's `TailZ40` (0bf41b17, QMFamilyGroupLaw; imported by TailZ23 and by
  Contrib/OneProof/DeligneComponentsY3Used, which TailZ34 imports) was overwritten by leaf-fold30's autofold output
  (56dcca02, persists-dvr, `sixContactMin_of_open34`, imports TailZ39).
  Fix (committed separately, so the integrator can see it): rigid-prune's module restored as TailZ40 verbatim
  (56dcca02^), leaf-fold30's autofold module moved verbatim to the new TailZ60 (the first name of my reserved range),
  Main.lean imports TailZ60. No other file touched (DeligneComponentsY3Used is Contrib, not editable, so TailZ40 has to
  keep rigid-prune's content).
