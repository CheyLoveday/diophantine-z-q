# goodmodel-iso results log

## 11-16 16:10 setup
- Base wip/group-law-dvr 3ab4d8eb; merged origin/main (already ancestor, c1e4ed1b) and origin/wip/neron-ext (901a0efd), no conflicts.
- Top bundle on this tree: TailZ45 `sixContactMin_of_open38 (r : OpenResearchLeaves28) (t : OpenTextbookLeaves13) (l : OpenAddedLeaves19)`;
  `mumfordGroupLawConn` in r (TailZ45:58 region), `neronSchemeExtensionExists` in t (TailZ44:110). VERIFIED (read).
- group-law-dvr's F2 patch generator scratch/group-law-dvr/fold/make_patch.py targets this same TailZ45 (main unchanged since). VERIFIED (read).

## Route analysis
- Suggested step (1) "F is a Néron model (BLR 1.2/8)" needs a group law on F: the tree's proof
  (NeronExt.isNeronModelOver_of_grpObj, NeronExtAb.lean) takes `[GrpObj X]`; its Weil-extension step
  `RelativeGroupLaw.exists_opens_diagonal_difference_extension` uses the target's group law. In
  NeronGoodModelIso, F has no group law (constructing it is the point of MumfordGroupLawDVR). So (1) is circular. VERIFIED (read).
