# ga-rigidity results log

- Base: wip/leaf-fold33b (75d94fe7) + merge origin/main (ee33f214) = 795180cf.
- Rows: `UnipotentForward.SGA7_IX_3_5_ForwardGeom` (ZInQKernel/Contrib/OneProof/UnipotentForward.lean:420) and
  `SGA33Steps.SGA7_IX_Cor3_3` (ZInQKernel/Contrib/OneProof/SGA7IX33Cor.lean:64). Both use semistability
  `GroupModelO.IsSemistable 𝒩 := ZInQ.HeightSplit.HasSemiAbelianIdentityComponent (geomSpecialFibre 𝒩)`
  (TailZ7.lean:196; definition TailY.lean:76): open connected subgroup U, faithfully flat hom U → B (AbVar) with kernel
  𝔾_m^r in the functor of points. VERIFIED (read).
- queue11-verdict.md is not present on any local branch (searched all refs); its content is taken from the task brief.
