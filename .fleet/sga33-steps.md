# sga33-steps (fleet note)

**Result.** I proved the field `OpenResearchLeaves38.sga7_IX_3_3_SHpre` (`DictModels.SGA7Pre.SGA7_IX_3_3_SHpre`)
with its exact type and no other hypothesis. It follows from one new leaf, `SGA33Steps.SGA7_IX_Cor3_3`: SGA 7 I
Exp. IX Cor. 3.3 (p. 348, Déf. 3.4 p. 349; the locator comes from the reading in the brief and was not re-read here).
The leaf is in printed form, specialized to traits: any DVR extension O ⊆ O' with O' ∩ K = O, no henselian or
finiteness condition, the canonical u, and the conclusion stated as an isomorphism N⁰ ×_O O' ≅ N'⁰.

The reading named three steps; each is proved in Lean in `ZInQKernel/Contrib/OneProof/SGA7IX33Cor.lean`:
1. base specialization (`cor33SH_of_cor33`);
2. dictionary: iso ⇔ open immersion with image N'⁰ (`openImm_range_iff_iso`), N'⁰ open over a DVR, and
   HasSemistableReduction ⇒ the given Néron model is semistable (uniqueness of Néron models);
3. c = u ≫ α by the Néron mapping property (`exists_aut_factor`), where α fixes the unit section and so maps N'⁰
   onto itself (`image_idCompSet_eq`).

**Compiles (VERIFIED).**
- The new file compiles with no warnings and only the standard axioms.
- `#discharges`: `DISCHARGES [OpenResearchLeaves38.sga7_IX_3_3_SHpre] by SGA33Steps.shpre_of_cor33`, still assuming
  only `[SGA33Steps.SGA7_IX_Cor3_3]`.
- autofold spec: `scratch/sga33-steps/autofold.json`. The dry run gives strict 16/18 → 17/17, i.e. −1 GLUE.
- The dry-run fold (`scratch/sga33-steps/FoldCheck.lean`, `sixContactMin_of_open56`) compiles with only the standard
  axioms.

**Remains.**
- Run the fold itself (integrator).
- A human reading of Cor. 3.3 / Déf. 3.4 to confirm the base hypotheses and the k(s)/κ̄ meaning of "semistable".
  The leaf is flagged "unread". If the print needs a henselian or finite base, the fallback is
  `SGA7_IX_Cor3_3_SH` → field (`shpre_of_cor33SH`).
- The locators.md row (proposed in `scratch/sga33-steps/rows-proposed.md`).

Report: `docs/research/sga33-steps.md`.
