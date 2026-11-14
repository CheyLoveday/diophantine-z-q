# reduct-glue (2026-11-14)

**Verdict: all four glue Props reduct-split left are proved in Lean from published leaves.**
`scratch/reduct-glue/ReductGlue.lean` = verbatim reduct-split `Reduction.lean` + new namespace `ReductGlue`; compiles
(`chk.sh`, ~56 s, 7.6 GB), no sorry/axiom, 44 `#print axioms` all `[propext, Classical.choice, Quot.sound]`.

- `FixedTorsionRationalImperfect` ← bundle leaf `MulEtaleAbelianScheme` (A[m] étale; fixed K̄-point of an étale
  K-scheme is rational). Proves `FixedTorsionRational` for every field.
- `SemistableAlmostAll` ← kernel `AbVarSpreadsOut` (EGA IV leaves) + `ProperSmoothGenConnected` + vendored Néron
  property of abelian schemes.
- `SemistableLocalGlobal` ← new leaf `NeronLocalizesDVR` (BLR §1.2 Prop. 4). Proved on the way: DVRs of a number
  field are the localizations (residue fields agree), Néron uniqueness over a DVR, fibre identification, and the
  transport glue `SemiAbelianFieldIsoInvariant`.
- `SemistableNeronBaseChangeLocalGlobal` ← new leaves `IdentityComponentOL` (SGA 3 VI_B 3.10),
  `OpenImmersionOfLocal` (EGA IV₃ 8.10.5) + `NeronLocalizesDVR`.
- `rows_of_leaves_noGlue`: reduct-split's seven rows from `ReductLeaves` + 6 leaves (`ReductGlueLeaves`) +
  `FaltingsLemma5`, no project glue.

Printed bases: strictly henselian / complete versions of all SGA 7 / Serre–Tate fields (`*SH`,
`SerreTateThm2Complete`). The general-DVR leaf is proved from the printed form for **4.7** (the flagged one),
**3.3a** and **3.5**, via the strict-henselization leaves `StrictHenselizationNeron`, `StrictHenselizationPair`,
`StrictHenselizationInside` (EGA IV 18.8 / Stacks / BLR 1.2/2). Left as named glue (needs stated): `ReductionFromSH`
(3.6), `IdentityComponentFromSH` (3.3b), `SerreTateFromComplete`.

Risks: all locators UNVERIFIED (no network). SPECULATIVE whether BLR 1.2/4 is printed with localizations and whether
EGA IV 8.10.5 lists open immersions. Report: docs/research/reduct-glue.md; log: scratch/reduct-glue/log.md.
