# leaf-fold33 log

Base: fork main after w82 (leaf-fold32b 03f2467d + STATUS.md wording, 5e235a40).

1. Merged wip/poincare-proof (5795bbc0) and wip/neron-sh-proof (3842078a).
2. One autofold (`scratch/leaf-fold33/autofold.json`), TailZ46, `sixContactMin_of_open39`:
   - `poincareComplement` by `PoincareComplement.poincareComplement_of_open`. Its spec in poincare-proof was written
     on 0caafe66; on this base `phiAmpleIsogeny` is supplied by `PicFix.phiAmpleIsogeny_of_printed` from the added
     leaves `mumfordKLFiniteSectionAC` and `mumfordPhiSurjectiveAC`, and `milneIsogenyQuasiInverse`, `cartierSmooth`
     are proved (`milneIsogenyQuasiInverse_proof`, `cartierSmooth_proof`), so those are used directly.
   - `blr_7_2_1` (dict-models' printed form, which replaced `neronBaseChangeStrictHenselization` in leaf-fold32) by
     `NeronSH.neronBaseChangeUnramifiedDVR_proof`: `DictModels.NeronBLR72.BLR_7_2_1` is by definition
     `ReductGlue.NeronBaseChangeUnramifiedDVR`, which neron-sh-proof proves with no hypotheses.
   - autofold: strict 16/21 on 37 -> 15/20 on 35; strictest 16/21 -> 15/20 (blr_7_2_1 was flagged "pending reading",
     so it counted GLUE: the strict GLUE count drops by one, and one LEAF field goes).
3. Checks (VERIFIED):
   - `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` and both contributions: OK.
   - `#print axioms ZInQ.OneProof.frozenTarget`: [propext, Classical.choice, Quot.sound].
   - Hash guard (DumpCompact before/after): before 14038, after 14083, only before 0, only after 45 (all in TailZ46),
     changed 1 (`ZInQ.OneProof.frozenTarget`).
   - `lake env lean scripts/one_proof/OpenStatements.lean`: 43 open hypotheses.
   - `render_open.py` then `render_open.py --check`: ok, 43 open hypotheses, all classified (35 H, strictest 15/20, 8 others).
   - `frontier_crosswalk.py` regenerated (H-72 poincareComplement unmatched now), `--check` ok.
   - `scratch/contrib-kit/DischargesTest.lean` rerun after the fold (output saved).
4. Branch: pushed as wip/leaf-fold33b, because wip/leaf-fold33 already existed on the fork (a parallel, unfinished
   fold made before this one: the same two discharges plus pic-smooth's picZeroAbVar, autofold count
   16/21 on 37 -> 18/20 on 38, with no regeneration of the docs). pic-smooth's part is left out here: it replaces the
   GLUE field picZeroAbVar by four leaves, one of them pending reading (picZeroSmoothPosChar, GLUE), so it neither
   removes a field nor lowers the strict GLUE count (this fold: 15/20 on 35; with pic-smooth: 18/20 on 38).
5. Route A's C_d chain (gzopt-dict, a backlog task that met its target): merged wip/gzopt-dict (period-odd, cd-optimal,
   gz-optimal, heegner-32, gz-conj and gz-weil's final files; clean merge). Hand fold of Main.lean, as
   scratch/gzopt-dict/MainEdit.lean shows (rewritten for the current Main): the binder `hL3 : GZDecomp.GrossZagierHeegner`
   (kinds: composite, GLUE) is replaced by `hGZ : GZAlg.GrossZagierAlgOptCd`, `hQ : GZAlg.Gamma0QExpansion`,
   `hW : CdOpt.EtaW32Character` (published, LEAF; rows from scratch/gzopt-dict/autofold-formula.json, packet, label,
   tier and area issue of hL3), through
   `GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd`,
   `fhNonvanishingCd_of_fhNonvanishing`, `Heegner32.grossZagierHeegnerCd_of_printed hCM`,
   `GZAlg.grossZagierFormulaCd_of_alg` and `GZConj.grossConjugationCd`; `HeckeThetaNewform` is no longer needed.
   The claims row of hL3 is removed. Strict GLUE count over all hypotheses: -1 (the 10 TYZ/GZ hypotheses: hCM, h33
   GLUE; the rest LEAF). Checks (VERIFIED): `lake build +Main +Discharges`; frozenTarget standard axioms; hash guard
   against step 3 (14083 constants, only frozenTarget changed); OpenStatements 45; render_open --check ok (35 H,
   strictest 15/20, 10 others); crosswalk regenerated, --check ok; DischargesTest rerun. Host paths in merged logs
   replaced by worktree names.
6. Merged fork main c1e4ed1b (the blueprint's height-decomposition chapter). chain-w84 then failed CHECKLR and RENDER:
   the chapter's Lean targets `HDec.HSyn.OpenTextbookLeaves13.*` were also declared by poincare-proof's dry-run
   output `scratch/poincare-proof/FoldDryRun.lean` (written on 0caafe66, where autofold's next generation had the
   same name), so autoform found them twice. The file is renamed `FoldDryRun.lean.txt` (content unchanged).
   `autoform check blueprint --lean-root .` and `autoform render ... --require-declarations` then pass (VERIFIED).
7. phi-ample (mumfordKLFiniteSectionAC proved from picRepresentableAbVar and picZeroAbVar, no new leaf): merged
   wip/phi-ample, autofold scratch/phi-ample/autofold.json -> TailZ47, `sixContactMin_of_open40`; strict
   15/20 on 35 -> 14/20 on 34, strictest the same. Checks (VERIFIED): build +Main +Discharges; frozenTarget standard
   axioms; hash guard against step 5 (only frozenTarget changed, 12 new constants, all in TailZ47); OpenStatements 44;
   render_open --check ok (34 H, strictest 14/20, 10 others); crosswalk --check ok; DischargesTest rerun; autoform
   check blueprint --lean-root . ok. Scratch copies of HDec.HSyn bundles (phi-ample's FoldDryRun.lean,
   neron-sh-proof's FoldCheck.lean) renamed .lean.txt, as in step 6.
8. homfree-noemb (homFreeFiniteAlgClosed rerouted away, no new leaf; manual fold, scratch/homfree-noemb/FOLD.md):
   merged wip/homfree-noemb; reran `scratch/homfree-noemb/Taint.lean` on this tree and regenerated the two
   contribution files with `gen/gen.py` (patched to read the top module from Main.lean instead of TailZ45, and the
   consumers header to import TailZ47): 39 + 96 declarations, top `sixContactMin_of_open40_hf` over
   `OpenTextbookLeaves14HF`. `#discharges`/OpenStatements read bundles only from ZInQKernel.OneProof modules, so a
   hand-written `OneProof/H/TailZ48.lean` (autofold's pattern) defines `OpenTextbookLeaves15` (= OpenTextbookLeaves14
   without the field, docstrings kept), its map to `OpenTextbookLeaves14HF`, and `sixContactMin_of_open41`; Main uses
   it (autofold parses the new Main). kinds/claims rows of homFreeFiniteAlgClosed dropped. Checks (VERIFIED): build
   +Main +Discharges; frozenTarget standard axioms; hash guard against step 7 (only frozenTarget changed, 12 new
   constants, all in TailZ48); closure of frozenTarget (270264 constants) has no AVB1.HomFreeFiniteAlgClosed,
   PkgI3.HomFreeFinite, HomFreeFiniteAlgClosedNoEmb or sorryAx; OpenStatements 43; render_open --check ok (33 H,
   strictest 13/20, 10 others); crosswalk --check ok; DischargesTest rerun; autoform check and render ok after
   renaming scratch/homfree-proof/FoldDryRun.lean to .lean.txt (it redeclared OpenTextbookLeaves13).
   Note for later folds: deg-det's DegEqDetTate route reads homFreeFiniteAlgClosed in characteristic p and no longer
   fits; degpoly-proof's recommended spec does not read it.
9. hW and hfx (frozenTarget binders, both proved outright with no new leaf): merged wip/etaw32-proof
   (`EtaW32Character.etaW32Character_proof`, from Mathlib's eta S/T laws) and wip/hfx-proof
   (`HfxProof.tyzTestVectorExists`; brings fork PR #39's Hurwitz approximation), hand fold of Main.lean (binders
   removed, proofs passed), kinds rows of hW and hfx and the claims row of hfx dropped. Checks (VERIFIED): build
   +Main +Discharges; frozenTarget standard axioms; hash guard against step 8 (only frozenTarget changed);
   OpenStatements 41; render_open --check ok (33 H, strictest 13/20, 8 others); crosswalk --check ok; DischargesTest
   rerun; autoform check blueprint ok.
   Not folded (log of the lead): fold33-combine's in-place prunes of sga3_VIB_3_10_Nbhd and of mumfordGroupLawConn /
   neronSchemeExtensionExists delete Lean targets named by the blueprint chapter (OpenResearchLeaves28 fields), so
   they fail autoform check; charpoly-charp needs T6 in characteristic p and conflicts with the homfree reroute.
10. hQ (frozenTarget binder, the q-expansion principle for Gamma0(N), proved outright with no new leaf): merged
    wip/gamma0-qexp (`Gamma0QExp.gamma0QExpansion_proof`), hand fold of Main.lean, kinds row dropped. Checks
    (VERIFIED): build +Main +Discharges; frozenTarget standard axioms; hash guard against step 9 (only frozenTarget
    changed); OpenStatements 40; render_open --check ok (33 H, strictest 13/20, 7 others); crosswalk --check ok;
    DischargesTest rerun; autoform check blueprint ok. Route A's C_d chain now rests on hGZ (Gross-Zagier over the
    algebraic X0(N)) and hCM only.
11. hP23 (frozenTarget binder, TYZ Proposition 2.3 first assertion, proved outright with no new leaf): merged
    wip/hp23-proof (`HP23Proof.tyzProp23Printed`), hand fold of Main.lean, kinds row dropped. Checks (VERIFIED):
    build +Main +Discharges; frozenTarget standard axioms; hash guard against step 10 (only frozenTarget changed);
    OpenStatements 39; render_open --check ok (33 H, strictest 13/20, 6 others); crosswalk --check ok;
    DischargesTest rerun; autoform check blueprint ok.
