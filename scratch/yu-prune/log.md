# yu-prune results log

- 11-15 02:10 start. Base 688b450d. Build tree copied (reflink) from ~/dzq-wt/gt-qm (.lake/build, lean/.lake).
  Tools copied to scratch/yu-prune/ (PruneScan from scratch/one-proof, PruneScanDead = sem-prune's variant,
  DeadCascade, prune_edit.py, cmp_hashes.py, DumpCompact) with output paths in scratch/yu-prune/.
- 02:14 **Base does not build at TailZ32** (VERIFIED): `lake build +ZInQKernel.OneProof.Main` fails with
  `TailZ32.lean:1:0: import ZInQKernel.Contrib.MulEtale.Direct.Original.StacksCore.Tactic.EgaSgaAttribute failed,
  environment already contains 'Stacks.EgaSga.instInhabitedWork.default' from
  ZInQKernel.Contrib.CloudW01Spread.StacksCore.Tactic.EgaSgaAttribute`. The two files are the same Stacks port
  (only the header comment differs); TailZ31's closure has the CloudW01Spread copy and leaf-fold19's MulEtale wrapper
  the MulEtale/Direct/Original copy. So TailZ32 and Main.lean fail on 688b450d itself; everything up to TailZ31 builds.
  Fixing it needs a Contrib edit (not allowed here). Workaround for the checks: variants of the tools rooted at
  `HDec.HSyn.sixContactMin_of_open25` (TailZ31): DumpCompact31.lean, PruneScan31.lean, DeadCascade31.lean.
- 02:15 base DumpCompact31: 13599 constants (OneProof modules + QMLattice), hashes_before31.txt;
  axioms of open25 = propext, Classical.choice, Quot.sound.
- 02:17 base PruneScan31 (root open25): OpenResearchLeaves19 30, OpenTextbookLeaves10 14, OpenAddedLeaves16 14,
  OpenGlue7 1 = 59 fields, 0 unused (frozenTarget itself has 58: OTL11 drops mulEtaleAbelianScheme). *-base.txt.
- 02:38 step 1 (plumbing, scratch/yu-prune/plumb.py) compiled first try: `lake build ZInQKernel.OneProof.H.TailZ31`
  OK (12139 jobs); open25 axioms standard.
- 02:41 PruneScan31 after step 1: exactly `OpenTextbookLeaves10.yuThm11` UNUSED; prune set 9 fields
  (TextbookLeaves.t27, OpenTextbookLeaves2/3/4/6.t27, OpenTextbookLeaves7/8/9/10.yuThm11), no constants
  (prune-set-step1.txt). Plus OpenTextbookLeaves11.yuThm11 (TailZ32), which the open25 root cannot see.
- 02:43 DeadCascade31: dead readers fibreComTrivial_of_gp3, fibreSimple_of_gp3, gluePieces_of_gluePieces3 (TailD),
  gluePieces_of_open2 (TailE), gluePieces_of_open3 (TailI) + generated casesOn/recOn (dead-cascade.txt).
