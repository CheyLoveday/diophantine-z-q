# sh-route results log

Base e38375b3 (wip/w62). Lean 4.35 / Mathlib v4.35.0.

## Setup
- Base.lean, Body.lean: verbatim copies of scratch/reduct-glue/{Base,Body}.lean. olean/ShRG.lean = their
  concatenation (diff with scratch/reduct-glue/ReductGlue.lean empty, VERIFIED); compiled to olean/ShRG.olean
  (110 s, 7.6 GB, no errors, VERIFIED 17:20).

## Top.lean (namespace ShRoute) — compiles over ShRG (VERIFIED 17:40, no errors)
- `IsSHUnram O O₁ hO` := SH DVR ∧ K₁/K algebraic ∧ uniformizer ↦ uniformizer ∧ κ₁/κ separable.
- LEAF `NeronBaseChangeSH` (BLR 7.2/1, 1.2/2; UNVERIFIED): char 0, IsSHUnram ⇒ Néron base change.
- `isSHNeronExt_of : NeronBaseChangeSH → IsSHUnram → IsSHNeronExt`.
- GLUE (commutative algebra) `SHExists0`, `SHInside0`, `SHPair0`.
- `StrictHenselization{Neron,Pair,Inside}0` = reduct-glue statements + `[CharZero K] [PerfectField κ(O)]`;
  each proved from NeronBaseChangeSH + the matching CA Prop.
- `RaynaudSemistable0`, `SemistablePersistsDVR0`, `SemistableUnipotent0` (char-0 forms) proved from the printed
  SH leaves (reduct-glue's proofs replayed).
