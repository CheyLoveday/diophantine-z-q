# r17-rebase log (results only)

Branch wip/r17-rebase from origin/wip/r17-print 785e3f29; merged origin/main c0f3d085 (leaf-fold33, top
sixContactMin_of_open48 in TailZ55): merge 09ec5c5b, no conflicts (VERIFIED, git).

## Step 1: build on the merged tree
* `lake build ZInQKernel.Contrib.OneProof.CarayolPrinted` (imports NewformDict, CarayolLevel, DSCoeffExt):
  success, 10691 jobs, no edits needed (VERIFIED, 2026-11-16 23:2x).

## New contribution ZInQKernel/Contrib/OneProof/CarayolPrintedIrr.lean (VERIFIED: compiles, no warnings; lake build OK)
* `adjoin_eq_top_of_irreducible_odd`: ρ-family in M₂(K), 2 ≠ 0, no invariant subspace but 0, K², and an involution C in the
  span with det C = −1 ⟹ the K-algebra spanned is M₂(K) (Burnside's form). Proof: e=(1+C)/2, f=(1−C)/2, e a f, f b e lin. indep.
* `CarayolThmAIrr` (leaf): CarayolThmA with the Burnside clause replaced by plain irreducibility (Ribet's word) + oddness
  (∃ c, c*c = 1 ∧ det ρ(c) = −1). `carayolThmA_of_irr : CarayolThmAIrr → CarayolThmA`;
  `carayolR17'_of_printedIrr : CarayolThmAIrr → EigenformCoeffFieldFinite → LadicCond.CarayolR17'`.
* Split: `CarayolExistence` (irreducible, odd, unramified, traces) and `CarayolConductor` (∀ such ρ, condExp = v_p(N));
  `carayolThmAIrr_of_split`, `carayolR17'_of_split`.

## Step 2: clash check (VERIFIED)
* `lake build` of all 244 top-level Contrib modules (contrib-tops.txt, tops.py) + OneProof.Main + Discharges on the merged tree:
  success, 14354 jobs (build-all-summary.txt).
* AllContrib.lean (all 244 tops incl. CarayolPrintedIrr) FAILS on a PRE-EXISTING clash not involving the new modules:
  'PkgI6.TraceContainsRamificationIdx' declared by ZInQKernel.Contrib.Different.Local (only in the closure of the old
  aggregate top ZInQKernel.Contrib.AllContrib) and by ZInQKernel.HDecomp.Textbook.Different (in every OneProof contribution's closure).
* clashloop.sh: dropping ZInQKernel.Contrib.AllContrib, AllContrib2.lean (243 tops incl. CarayolPrintedIrr) elaborates;
  `carayolR17'_of_printedIrr` standard axioms (clashloop-out.txt).
* Dropped top: NewNames.lean lists the 71 constants declared in CarayolPrintedIrr, CarayolPrinted, NewformDict, CarayolLevel
  (new-names.txt); DroppedTopCheck.lean (imports ZInQKernel.Contrib.AllContrib) finds none of them in that environment;
  positive control PkgI6.TraceContainsRamificationIdx found (dropped-top-check.txt). So no name clash from the new modules.
