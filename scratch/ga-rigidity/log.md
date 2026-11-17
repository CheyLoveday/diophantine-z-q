# ga-rigidity results log

- Base: wip/leaf-fold33b (75d94fe7) + merge origin/main (ee33f214) = 795180cf.
- Rows: `UnipotentForward.SGA7_IX_3_5_ForwardGeom` (ZInQKernel/Contrib/OneProof/UnipotentForward.lean:420) and
  `SGA33Steps.SGA7_IX_Cor3_3` (ZInQKernel/Contrib/OneProof/SGA7IX33Cor.lean:64). Both use semistability
  `GroupModelO.IsSemistable 𝒩 := ZInQ.HeightSplit.HasSemiAbelianIdentityComponent (geomSpecialFibre 𝒩)`
  (TailZ7.lean:196; definition TailY.lean:76): open connected subgroup U, faithfully flat hom U → B (AbVar) with kernel
  𝔾_m^r in the functor of points. VERIFIED (read).
- queue11-verdict.md is not present on any local branch (searched all refs); its content is taken from the task brief.
- G1.lean (§0 defs IsGaHom/NoGaSubgroup, algPt calculus, Step (1) unit_additive_eq_one, gaHom_torus_trivial): compiles, no errors. VERIFIED.
- GaR.lean §4 (valuative argument; gaHom_proper_point: a hom 𝔾_a → B, B proper group scheme over any field k, kills every k-point): compiles. VERIFIED.
- GaR.lean §5-§6 (closedPoint_eq_ev, ext_of_points; gaHom_proper_trivial and gaHom_abVar_trivial = Step (2)): compiles. VERIFIED.
- GaR.lean §7 (factor_openImm, gaHom_add, gaHom_factors_open: a hom 𝔾_a → G factors through every open subgroup U ⊆ G, k alg. closed): compiles. VERIFIED.
