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
