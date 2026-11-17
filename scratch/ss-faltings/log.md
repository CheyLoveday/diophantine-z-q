# ss-faltings results log

Base: fork main d435851d (branch wip/ss-faltings). Task: reroute SS2/SS3 off SGA 7 IX Cor. 3.3 (`sga7_IX_Cor3_3_Def34`).

## 1. Trace of the readers (VERIFIED, read in source)

- d2a6-reroute's taintD-out.txt (section COR33, read from origin/wip/d2a6-reroute): `sga7_IX_Cor3_3_Def34` ->
  `sga7_IX_3_3_SHpre` -> `sga7_IX_3_3_SH` -> `sga7_IX_3_3`, `semistablePersistsSHcp` (OpenResearchLeaves14GMEB).
- Readers (EichlerBoundCopy.lean):
  - `ss1_ss3_of14NF_hf_gm_pz_eb` (L3067): SS1 AND SS3 from `GapNeron.ss1_ss3_of_cpNF r.semistablePersistsSHcp ...`.
    SS1 (`SemistableReductionThm`) is tainted too: its global form uses persistence twice (NeronDVR.lean
    `semistableReductionThm_of_leaves_nfNF`: at bad places through `F O ≤ L₀`, and at semistable places of `A`).
  - `researchLeaves9_of_open14_hf_gm_pz_eb` (L2981): SS2 := `semistableNeronBaseChange_noSGA3 r.blr_1_2_4 r.sga7_IX_3_3 ...`.
- Downstream (OpenResearchLeaves9EB -> 8EB fields `semistableReductionThm`, `semistableNeronBaseChange`,
  `semistablePersists`), read only by
  - `heightRowsNo20_of8_hf_eb` (L470): R18, R19, R21, R22, StableHeightFinite via TailY's `r18_of_leaves`,
    `r19_of_leaves`, `r21_of_leaves'`, `r22_of_upper`, `stableHeightFinite_of'` -- each uses SS2 only through
    `stableFaltingsHeight_eq_of_semistable` (TailY L163: kernel height = height of any semistable Neron model), via
    `isStableFaltingsHeight_iff`, `exists_semistable_neron`, `stableFaltingsHeight_ne_bot`.
  - `r20Lower_of8_hf_eb` (L498): `r20Lower_of_leaves'` (TailY L666) uses SS3 to make Neron models over the
    compositum of the two semistable fields semistable, then the identification.
- Finding: the readers never need semistability of a base change of a *given* semistable model except in r20Lower,
  where a common semistable field for A and B suffices. SS2 is used only for invariance of the height of a semistable
  Neron model under finite extension -- Faltings 1983's statement.

## 2. Merge of main f3402e89 (fold-b112; top TailZ83, `sixContactMin_of_open76`) -- done, clean merge

## 3. SSFaltings.lean compile (VERIFIED)
- `lake env lean ZInQKernel/Contrib/OneProof/SSFaltings.lean`: no errors (after fixing `pazukiC2_nonneg` namespace
  `ZInQ.HeightSplit` and the compositum `L := KA ⊔ KB` as a `let` with `IntermediateField.finiteDimensional_sup`).

## 4. Trace on the new top (VERIFIED, `lake env lean scratch/ss-faltings/TaintS.lean` -> taintS-out.txt)
- Top `HDec.HSyn.sixContactMin_of_open76` (TailZ83). Closure 274529 constants; 28 carriers (25 in TailZ80 =
  bost-gr9's chain copy, namespace `HDec.HSyn.GR9`; `OpenResearchLeaves55/56/57` in TailZ81-83); 110 tainted (T),
  852 T+S lines.
- Readers unchanged except R21: bost-gr9 moved R21 to `ZInQ.BostGR9.r21_of_grBost'` (reads SS1, SS2 through TailY's
  identification). New `ZInQKernel/Contrib/OneProof/SSFaltingsGR9.lean`: `r21_of_grBostF`, `r21_of_grBostF'`.
- sz-raynaud: `raynaudSemistableSHOr` is mapped from `silverbergZarhinThm35` by the copied conversion
  `openResearchLeaves54_of_OpenResearchLeaves55` (copied verbatim by the chain generator): nothing to do by hand.

## 5. Chain (VERIFIED)
- `python3 scratch/ss-faltings/gen/gen_chain.py ZInQKernel/Contrib/OneProof/SSFChain.lean`: 100 blocks; 72
  declarations, 28 structures; edits cor33_fields 38, ss_fields 6, assign 43, hss 4, ss13 1, rows 1, r20 1.
- `lake build ZInQKernel.Contrib.OneProof.SSFChain`: EXIT 0; `HDec.HSyn.sixContactMin_of_open76_sf` depends on axioms
  [propext, Classical.choice, Quot.sound].
