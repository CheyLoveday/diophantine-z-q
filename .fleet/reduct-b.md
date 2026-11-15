# reduct-b (fleet summary)

**Result.** The three strict-GLUE SGA 7 IX DVR fields of the top research bundle (`semistableReductionDVR` 3.6,
`raynaudSemistable` 4.7, `semistablePersistsDVR` 3.3a) are Lean theorems. No statement was changed, and none was
found false or vacuous.
- **K1**: `ReductB.semistableReductionDVR_of_raynaud` proves 3.6 from 4.7 plus the textbook fields Mumford §4 and
  `[m]` étale. The proof takes `m ∈ {3,4}`, the torsion field of definition `K'`, and a `K'`-embedding
  `K̄ → (K')‾`, so no Galois action has to be transferred.
- **Route B**:
  - `strictHenselizationNeron_of_pair` (the instance `K' = K`, `O' = O`);
  - `raynaudSemistable_of_SH_pair`;
  - `semistablePersistsDVR_of_SH_pair`.
- **Recommended fold (option B)**: drop the three fields and add `RaynaudSemistableSH`, `SemistablePersistsSH` and
  `StrictHenselizationPair`. All are reduct-glue Props already in kernel TailZ14. Strict GLUE drops by 3 (by 2 if the
  composite pair is counted as GLUE), and the field count is unchanged.
- **Option A**: K1 alone removes `semistableReductionDVR` and adds no field.

**cp variant.** This adds `[CharZero K]` and `[PerfectField κ(O)]` to the SH leaves.
- It works for 3.3a. SS1 and SS3 re-type-check at number fields (`ss1_ss3_of_cp`, `perfectField_residue_nf`).
- It cannot fill 4.7 and 3.6 for their other consumers, `r6 = PkgI2.RaynaudCriterion` and
  `r8 = PkgI2.GrothendieckMonodromy`. Both are stated over every field. Doing it would mean restating r6/r8 and
  about 25 kernel consumers, which was not attempted.

**What compiles (VERIFIED).** `scratch/reduct-b/ReductB.lean` (= `RBBase.lean`, reduct-glue's file, + `Body.lean`)
compiles with `lake env lean` in 52 s and 7.6 GB. It has no sorry and no axiom, and its 11 `#print axioms` lines are
all standard. `fold_uses` re-derives r6, r8, SS1 and SS3 with the TailZ15/TailZ9 terms after the replacement.

**What remains.**
- `scratch/reduct-b/FoldSnippet.lean.txt` (`OpenResearchLeaves13`, `sixContactMin_of_open16`) has not been compiled
  against the real TailZ19, which is not built here.
- The reading risk: SGA 7 IX may assume an algebraically closed residue field, in which case option B's SH 4.7 field
  is stronger than the print for imperfect residue fields.
- Every locator is UNVERIFIED (no network). Report: `docs/research/reduct-b.md`.
