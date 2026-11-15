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

## Step 3 (11-14 17:20): prune — COMPILED, VERIFIED
- PruneScan after step 2 (2 min): OpenTextbookLeaves10 unused [genusX1Field]; the other three top bundles 0 unused.
  prune-set (9 fields): TextbookLeaves.t34, OpenTextbookLeaves2/3/4.t34, OpenTextbookLeaves6/7/8/9/10.genusX1Field
  (kept as prune-set-before.txt, used-fields-before.txt, unused-all-before.txt).
- DeadCascade (40 s): dead readers modCurveLeaves_of_bundles, glueOutputs_of_leaves, sixContactMin_of_leaves,
  sixContactMin_of_leaves_pin, sixContactMin_of_open (LPrefix), sixContactMin_of_leaves2 (TailA), plus generated
  casesOn/recOn of the nine bundles (dead-cascade-before.txt).
- scratch/genus-fold/prune_edit.py (written here; no prune_edit.py exists on any origin ref) deletes the 9 fields
  (with field docstrings), 10 one-line assignments into removed fields (incl. TailN's and TailO's
  `t34 := t34_of_split5 …`, which assign the removed OpenTextbookLeaves4.t34), the inline `genusX1Field := …` in
  TailO's sixContactMin_of_open6_poincare literal, the 6 dead readers and their `#print axioms` lines.
  Output: prune_edit_out.txt. 11 files, 134 deletions, 1 line changed (the inline literal).
- `lake build +ZInQKernel.OneProof.Main`: success (16 min), frozenTarget axioms [propext, Classical.choice, Quot.sound].
