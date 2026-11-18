# fold-cm results log

Base: wip/leaf-fold33b 0bcb3b0b1 (top `HDec.HSyn.sixContactMin_of_open80`, TailZ87, `OpenResearchLeaves61`,
`OpenTextbookLeaves18`, `OpenAddedLeaves28`; render_open: H strict 5/24 on 29).
Ruling quoted (Jack, to "Should [the CM-branch package] fold now?"): "Fold now at +4 (Recommended)".
Build artifacts: fold-c8's .lake/build (head be73b91c5, no ZInQKernel/ difference to 0bcb3b0b1) reflink-copied.

## 1. Components (VERIFIED, git)
* origin/wip/cm-fold-rebase 664e00417, merge-base with the base 67950e829 (top open76, TailZ83). 106 files, all added
  (no existing file modified). Its route: `sixContactMin_of_open77_cm` over TailZ80's GR9 chain and cm-branch2's
  `CMBranch/R5Prune*` copies, base `CMBranch.sixContactMin_of_open4_cm`.
* origin/wip/y3-x6b 9a2bbbe3f, on top of 664e00417; 61 files, all added. Its route copies the CM route's weak-row
  copies (`_y3`).

## 2. The live chain of the base (VERIFIED, read in ZInQKernel/OneProof/H/)
open80 (TailZ87) -> open79_hm (C8Chain) -> open72_sf_u_hm -> open45_pz_eb_sf_u_hm -> open37..8 `_sf_u_c8`
-> open7/6/4 `_hf_pz_eb_u_c8` (C8Chain L775: base `sixContactMin_of_open4_hf_pz_eb_u_c8`, NoCM/FS5 at L705-708).
Three copy reroutes since the components' base: SSFChain (`_sf`, TailZ84), D2A6Chain (`_u`, TailZ85), C8Chain (`_c8`/`_hm`,
TailZ87). The live base reads `r.r6 : D2A6.R6U` (`modelG3G6_of_leaves3U`, `linkedTateLocal_of_leaves3_hf_u`,
`kernelFieldExists_of_split_hf_u''`) and `l.c8` (GaloisPiecesC8 in `afterG7_of3_hf_pz_eb_u_c8`).
The CM base `CMBranch.sixContactMin_of_open4_cm` (Open4.lean) reads `r.r6 : PkgI2.RaynaudCriterionNF` (NC readers
`modelG3G6NC_of_leaves3`, `linkedTateLocalNC_of_leaves3_hf`, `kernelFieldExistsNC_of_split_hf`), and
`l.t09SymmIsogenyExists` through `detTate_of_leaves4_pz`: fields that the u/c8 generation-4 bundles
(`OpenResearchLeaves2EBU`, `OpenAddedLeaves4PZC8`) no longer have.

## 3. Manuscript checks (VERIFIED by reading diophantine_zq.tex; computation below)
* `pullback_check.py` -> `pullback_check.txt`: G^6 - 97200 F^2 - H^2 = 0 exactly (F, G from L381-383, H from L512);
  prime support of discriminants, leading coefficients and pairwise resultants of the ten factors = {2,3,5,7,11,13};
  J(inf) = -57600/7^6 is not a branch value.

## 4. Inbox 84.1 (VERIFIED, read on this host 18:55)
The running autoland loop (started 11-17 04:14) runs ~/dzq-runs/autoland-loop.sh (mtime 04:14), whose docs-only
merge filter has no claims.tsv/volatile.tsv exemption. The exemption exists only in autoland-loop.sh.new (15:23,
not installed). So 84.1 is NOT live.

## 5. Merge of component 1 and the CM base on the live bundles
* `git merge 664e00417` (5cb492e59): clean, all files added.
* `ZInQKernel/Contrib/OneProof/CMBranchUC8.lean` (new): cm-branch's localized theorems composed with d2a6b's and
  fold-c8's replacements; top `HDec.HSyn.sixContactMin_of_open4_cm_u_c8 (r : OpenResearchLeaves2EBU)
  (t : OpenTextbookLeaves4HFPZ) (l : OpenAddedLeaves4PZC8) (g : OpenGlue4) h20 hYu hθ + 7 CM inputs`.
  `lake env lean`: 0 errors (VERIFIED, second try; first try missed the `g7DegreeBound_gp4` argument).
* Dirty scan of the base top (`DirtyLive.lean` -> `dirty-live.tsv`, 6.7 min): 963 dirty of 97078 ZInQKernel constants;
  722 in D2A6Chain, 130 in C8Chain, 1 TailZ87, 0 in SSFChain; the 109 in the original tree are covered by
  cm-branch2's `_r5` copies or are the deleted GR/FS5 producers (checked by name).
