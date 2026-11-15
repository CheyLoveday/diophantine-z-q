# genus-fold results log

## Setup (11-14 16:00)
- origin/wip/genus-route already merged in base (e38375b3).
- Copied PruneScan.lean, DeadCascade.lean (origin/wip/prune-scan 9991ed35) and DumpCompact.lean
  (scratch/one-proof) into scratch/genus-fold/, output paths changed to scratch/genus-fold/.
- prune_edit.py does not exist on any origin ref; the deletions are done by hand following commit 0218a662.

## Step 1 (11-14 16:25): Genus modules — COMPILED (lake build), VERIFIED
- DumpCompact on base (after `lake build +ZInQKernel.OneProof.Main`, 9.5 min, axioms standard):
  scratch/genus-fold/hashes_base.txt, 11811 constants.
- scratch/genus-fold/split_closed.py splits scratch/genus-route/Closed.lean (verbatim, `#print` lines dropped)
  into ZInQKernel/OneProof/Genus/DimJac.lean (38 KB), GenusBound.lean (88 KB), LocalDer.lean (56 KB).
  Namespaces renamed: DimJacGlue -> GenusFold.DimJacGlue, ModularSplit.DimJac -> GenusFold.DimJac
  (H/TailZ10 has root copies with those names, which would clash once TailD imports these modules),
  GenusRoute -> GenusFold. Imports: kernel Contrib/HDecomp modules only (the 10 of Closed.lean).
  Build: 10 s + 14 s + 15 s.
- Genus/Bridge.lean (imports H.TailC + Genus.LocalDer; namespace HDec.HSyn): DimJ1Le5, t34Le (:= GenusFold.dimJ1Le,
  accepted directly since HDec.PkgI3.AbVar / LeafModCurves.IsJ1 are the kernel's after the dedupe),
  dimJ1Le5_of_t34, dim_J1_le_of5, G0Split.javanpeykarJ1_of_le, the two rfl/type examples. Built 4.6 s.

## Step 2 (11-14 16:45): TailD edited — COMPILED, VERIFIED
- H/TailD.lean: `import ZInQKernel.OneProof.Genus.Bridge`; E2 `LeafModCurves.dim_J1_le t.t34 N hN0 J hJ1` ->
  `dim_J1_le_of5 t34Le N hN0 J hJ1`; G18 `javanpeykarJ1 hR18 hBelyi t.t34 ...` -> `javanpeykarJ1_of_le hR18 hBelyi t34Le ...`.
  No statement changed. `lake build +ZInQKernel.OneProof.Main` succeeds (8m45s); frozenTarget axioms
  [propext, Classical.choice, Quot.sound]. No clash with TailZ10's root DimJacGlue/ModularSplit.DimJac.
