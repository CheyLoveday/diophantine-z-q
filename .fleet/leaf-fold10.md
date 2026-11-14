# leaf-fold10 (fleet summary)

**Result: the single proof now rests on 62 open fields, strict LEAF/GLUE 45/17 (leaf-fold9: 63 fields, 42/21).**
`ZInQ.OneProof.frozenTarget` goes through the new top `HDec.HSyn.sixContactMin_of_open12`
(`ZInQKernel/OneProof/H/TailZ15.lean`), with bundles `OpenResearchLeaves10` (30), `OpenTextbookLeaves10` (17),
`OpenAddedLeaves9` (14) and `OpenGlue7` (1). Four folds were taken, each strict −1:
1. **dimjac-glue**: `dimJacobianEqGenus` is proved with no hypotheses (`TailZ10`, `TailZ11`).
2. **shimura-glue**: `y3Connected` (composite) now follows from Deligne's `π₀` theorem in printed form,
   `ShimuraGlue.DeligneComponentsY3Printed` (`TailZ12`, `TailZ13`).
3. **reduct-glue**: `r6` now follows from `ReductSplit.RaynaudSemistable` (SGA 7 IX 4.7 over a DVR). The glue
   `FixedTorsionRationalImperfect` is proved (`TailZ14`, `TailZ15`).
4. **reduct-glue**: SS1 `semistableReductionThm` and SS3 `semistablePersists` now follow from
   `SemistablePersistsDVR` (SGA 7 IX 3.3) and `NeronLocalizesDVR` (BLR 1.2/4, counted as a consequence).
   `SemistableAlmostAll` comes from the chain's EGA IV and Zariski proofs.

**frozenTarget, hypotheses removed:** `dimJacobianEqGenus`, `y3Connected`, `r6`, `semistableReductionThm`,
`semistablePersists`. **Added:** `deligneComponentsY3Printed`, `raynaudSemistable`, `semistablePersistsDVR`,
`neronLocalizesDVR`. The TYZ and GZ hypotheses are unchanged.

**Compiles (VERIFIED).**
- `lake build +ZInQKernel.OneProof.Main` exits 0, and `frozenTarget` has axioms `[propext, Classical.choice,
  Quot.sound]`.
- `DumpCompact` with `cmp_hashes`: 0 constants removed, 1 changed (`frozenTarget`), 712 new, all in
  `TailZ10`–`TailZ15`.
- `Check10`: 62 fields and no `sorryAx` in the closure.
- The three copied modules are verbatim (`verbatim_check10.py`).
- Every new module is under 150 KB (the largest, `TailZ14`, is 117 KB).
- No existing module or statement was changed, and no FaithCheck was needed.

**Caveats.**
- `raynaudSemistable` and `semistablePersistsDVR` are marked "published form pending the base review", like
  reduct-split's four DVR leaves.
- Under fork main's newer ruling (frontier r5), `deligneComponentsY3Printed`, like `gonzalezRotgerCountX6`, would
  count as a candidate. The count is then 43/19.

**Not folded.**
- shimura-glue's `r1r2` and `x6ConicModel` splits: strict GLUE unchanged, lenient −1.
- reduct-glue's SS2: strict +1.
- reduct-glue's printed-base forms: no gain.
- Cloud PRs W11/W14/W15/W16: not on fork main.

Report: `docs/research/leaf-fold10.md`. Log: `scratch/leaf-fold10/log.md`.
