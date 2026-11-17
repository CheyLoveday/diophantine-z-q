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
- GaR.lean §8 (gaHom_trivial_of_semiAbelian, noGaSubgroup_of_semiAbelian = Step (3)): compiles, whole file no errors. VERIFIED.
- Contribution files: ZInQKernel/Contrib/OneProof/GaRigidity.lean (= GaR.lean with module doc) and GaRigiditySGA7.lean
  (NoGaInIdComp, IsSemistableDef34, HasSemistableReductionDef34; leaves SGA7_IX_Cor3_3_Def34, SGA7_IX_3_5_ForwardGeom_Def34;
  discharges sga7_IX_Cor3_3_of_def34, sga7_IX_3_5_ForwardGeom_of_def34). Compile pending dependency build.
- autofold.json written; `autofold.py --dry-run` succeeds: strict count 12/22 on 34 -> 13/21 on 34; strictest 11/23 -> 12/22
  (-1 GLUE in this base: sga7_IX_3_5_ForwardGeom is LEAF in this base's kinds.tsv; -2 if queue11 re-rated it GLUE). VERIFIED (ran).
- queue11 verdict file absent locally; SGA 7 not read (no network): reading of Déf. 3.4 as "no 𝔾_a" taken from the brief. UNVERIFIED.
- lake build GaRigidity + GaRigiditySGA7: success (12822 jobs). VERIFIED.
- lake build +Main +Discharges +GaRigiditySGA7: success (16075 jobs). #discharges: sga7_IX_3_5_ForwardGeom by
  sga7_IX_3_5_ForwardGeom_of_def34 (assumes SGA7_IX_3_5_ForwardGeom_Def34), sga7_IX_Cor3_3 by sga7_IX_Cor3_3_of_def34
  (assumes SGA7_IX_Cor3_3_Def34); axioms standard. Output in Discharges-output.txt. VERIFIED.
- AutofoldDryRun.lean (dry-run module, first line stripped) compiles; sixContactMin_of_open61 standard axioms. VERIFIED.
