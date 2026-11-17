# sga33-steps log

## Setup
- Base: wip/sga33-steps = 222c98bf (origin/main already merged); merged origin/wip/leaf-fold33b (db99b5b4) — not on main.
- Field: `HDec.HSyn.OpenResearchLeaves38.sga7_IX_3_3_SHpre : DictModels.SGA7Pre.SGA7_IX_3_3_SHpre`
  (def in ZInQKernel/Contrib/OneProof/SGA7IX33SHPre.lean). VERIFIED (read).
- Consumers (VERIFIED, grep): only `SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre'` (TailZ45 copies / NoSGA3Copy / GoodModelIsoCopy),
  which yields `SGA7PersistsNF.SGA7_IX_3_3_SH` (arbitrary c), read by `SGA3Nbhd.NF.sga7_IX_3_3_of_SH'` (c₁ built from an
  arbitrary upstream c) and `semistablePersistsSHcp_of_SH'`. The consumers use the arbitrary-c form, so step 3 is needed.
- Prior task sga33-shpre (origin/wip/sga33-shpre) restricted the field to AC residue fields (bypass fold, not autofold).
  This task instead proves the field itself from the printed Cor. 3.3.

## Plan (Lean file ZInQKernel/Contrib/OneProof/SGA7IX33Cor.lean)
- LEAF `SGA33Steps.SGA7_IX_Cor3_3`: any DVR extension O ⊆ O' (O'∩K=O), no henselian, no finiteness; 𝒩.IsSemistable;
  canonical u (generic fibre = bcDVR gen); conclusion: iso e : U ≅ W with e ≫ W.ι = U.ι ≫ u.
- step 1 `cor33SH_of_cor33` (specialization), step 2 `openImm_range_iff_iso` + `semistableNeronModels_of_has`,
  step 3 `exists_aut_factor` + `image_idCompSet_eq`; field: `shpre_of_cor33`.
- SGA7IX33Cor.lean: compiles with lake env lean, no errors/warnings (VERIFIED, 00:2x 11-17). Fixes: open ReductGlue; range of iso via e.hom.surjective; calc for unit.
- lake build +Main +Discharges +SGA7IX33Cor: Build completed successfully (14274 jobs), 15m25s (VERIFIED).
- Statement.lean: rfl check of the verbatim copy passes (VERIFIED).
- Discharges.lean (discharges.txt): `DISCHARGES [OpenResearchLeaves38.sga7_IX_3_3_SHpre] by SGA33Steps.shpre_of_cor33,
  still assumes: [SGA33Steps.SGA7_IX_Cor3_3]`, and by `shpre_of_cor33SH` assuming `[SGA7_IX_Cor3_3_SH]`; standard axioms
  for shpre_of_cor33, shpre_of_cor33SH, cor33SH_of_cor33 (VERIFIED). 39 open, 11122 theorems checked, 51 discharge one.
- autofold.py --dry-run: strict 16/18 on 34 -> 17/17 on 34; strictest 16/18 -> 17/17 (VERIFIED).
  FoldCheck.lean (dry-run output minus line 1, TailZ63 content): compiles; sixContactMin_of_open56 standard axioms (VERIFIED).
