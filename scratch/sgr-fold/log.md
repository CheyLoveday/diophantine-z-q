# sgr-fold results log

- 11-15 22:43 start. Base 862bd440 (wip/leaf-fold-hx) merged with origin/wip/sgr-direct 56478c75 -> e38f8de4.
  .lake/build and lean/.lake/build copied (reflink) from ~/dzq-wt/sgr-direct.
- 22:50 base `lake build +ZInQKernel.OneProof.Main` OK (12996 jobs); frozenTarget axioms standard (build-base.txt).
- base DumpCompact: 16258 constants (hashes_before.txt); frozenTarget type in frozenTarget_before.txt.
- base PruneScan: OpenResearchLeaves22 29, OpenTextbookLeaves11 12, OpenAddedLeaves17 14, OpenGlue7 1 = 56 fields,
  0 unused (prunescan-base-out.txt, used-fields-base.txt, unused-all-base.txt, prune-set-base.txt).
- Design (VERIFIED by reading): the consumer of shimuraGoodReduction / modelCoordinateResidue on the chain is
  TailO `glue4_of_open6` (sixContactMin_of_open6 -> open4); TailN `glue4_of_open5` is the gen-5 twin (off the
  sixContactMin stack). Fields: OpenAddedLeaves6.shimuraGoodReduction, OpenGlue6.modelCoordinateResidue (TailO);
  OpenAddedLeaves7..16.shimuraGoodReductionNoGuard, OpenGlue7.quotientP1Coordinate (TailX);
  OpenAddedLeaves17.shimuraIntegralModelRep (TailZ34). Top bundles have no r1r2 field (moduli leaves restated).
  Plan: (A) TailO imports SGRDirectNV; OpenGlue6 and OpenGlue7 gain `nvLocalInertia : SGRDirect.NVLocalInertia`
  and `heckeSqrtBranchAny : SGRDirect.HeckeSqrtBranchAny`; glue4_of_open6 sets heckeVertWitness :=
  SGRDirect.heckeVertWitness_of_nvSqrtAny (R1R2fp_of_rep r.r1r2) (torsionStructure_ofK5 t.t5) l.qmAutCard
  (serreRigidity3_of_T35_5 ..) l.alFixedPoints g.nvLocalInertia g.heckeSqrtBranchAny; glue6_of_open7 copies.
  Stack theorem types unchanged (g : OpenGlue7 throughout; X0ModuliUsed/ThetaWeierstrass8 pass g to open29).
  (B) PruneScan, prune. (C) TailZ36: OpenGlue8 {nvLocalInertia}; openGlue7_of_OpenGlue8 r t l g fills
  heckeSqrtBranchAny by SGRDirect.heckeSqrtBranchAny_of_elkies at the top (R1R2fp from x6Rows_of_open14 on the
  composed down-conversions, T5 from mumfordTorsionAlgClosed, r.elkiesX6StarPrinted); sixContactMin_of_open30.
- 23:02 step A (TailO import SGRDirectNV; OpenGlue6/7 + nvLocalInertia, heckeSqrtBranchAny; glue4_of_open6 by
  SGRDirect.heckeVertWitness_of_nvSqrtAny; glue6_of_open7 copies): TailX built alone OK, then
  `lake build +ZInQKernel.OneProof.Main` OK (12997 jobs, 7.5 min); frozenTarget axioms standard.
- 23:13 PruneScan after step A (prunescan-stepA-out.txt): exactly OpenAddedLeaves17.shimuraIntegralModelRep and
  OpenGlue7.quotientP1Coordinate unused; prune set 12 FIELD lines (prune-set-stepA.txt): OpenAddedLeaves6
  .shimuraGoodReduction, OpenGlue6.modelCoordinateResidue, OpenGlue7.quotientP1Coordinate, shimuraGoodReductionNoGuard
  in OpenAddedLeaves7/8/9/12/13/14/15/16, OpenAddedLeaves17.shimuraIntegralModelRep. No other field became unused
  (curveBijIso of gen 6 is filled by the proof curveBijIso_lf7).
- step B (prune_sgr.py, prune_sgr_out.txt, 64 deleted lines): the 12 fields and their assignments; off-chain
  cascade: OpenAddedLeaves10/11 (wholly unused off-chain generations) also lose shimuraGoodReductionNoGuard because
  addedLeaves11_of_open12 (read by the off-chain sixContactMin_of_open16) reads gen 12's; addedLeaves5_of_open6
  (TailO, referenced only by its #print) deleted as a dead reader.
- step C: ZInQKernel/Contrib/OneProof/SGRFold.lean (imports TailZ35 + SGRDirectElkies): research14_of_open29,
  added12_of_open29, heckeSqrtBranchAny_of_open29, openGlue7_of_nvLocalInertia. ZInQKernel/OneProof/H/TailZ36.lean:
  OpenGlue8 {nvLocalInertia}, openGlue7_of_OpenGlue8, sixContactMin_of_open30. Main imports TailZ36, g : OpenGlue8,
  open30.
- 23:25 build after B+C: `lake build +ZInQKernel.OneProof.Main` OK first try (13000 jobs, 9.3 min); axioms of
  heckeSqrtBranchAny_of_open29, openGlue7_of_nvLocalInertia, sixContactMin_of_open30, frozenTarget standard.
