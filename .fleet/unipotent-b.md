# unipotent-b (2026-11-14)

**Main result.** The field `semistableUnipotent : ReductSplit.SemistableUnipotent` keeps its statement word for
word and is now a Lean theorem: `UnipotentB.semistableUnipotent_of_printedGen`. It uses:
- the new LEAF `SemistableUnipotentPrintedGen`: SGA 7 IX 3.5 as printed over a strictly henselian trait, with
  `K^s`, semistability over `k(s)`, the iff, and the echelon clause `(σ-1)(τ-1) = 0`; wording UNVERIFIED (no
  network);
- the existing leaf `StrictHenselizationInside`;
- the existing bundle leaf `MulEtaleAbelianScheme`;
- one GLUE, `SemiAbelianDescendsSepClosed`, needed only when `k(s)` is imperfect; proved for perfect `k(s)`.

The `K^s` versus `K̄` axis is fully proved: inertia restricts to `K^s`, and the torsion of `A(Ω)` comes from `K^s`
through a separably closed version of `exists_lift_of_etale`. `SemistableUnipotentSH` (statement unchanged) is also
proved. A variant leaf that reads semistability over `κ̄` gives the field with no glue
(`semistableUnipotent_of_printedGeom`).

**The task's restricted form is done, but it does not fold.** `SemistableUnipotentPrinted` (`[CharZero K]`,
`[PerfectField k(s)]`) proves `SemistableUnipotentSH0` and then `SemistableUnipotent0` with no glue. The uses check
fails, though:
- Row r6 (`PkgI2.RaynaudCriterion`, quantified over every field) applies the field at an arbitrary `K`. With the
  restricted field it fails: "failed to synthesize CharZero K" (`UsesFail.lean`).
- r6 is consumed by `QML3.goodReduction`, which has `[CharZero K]` but an arbitrary DVR whose residue field is not
  assumed perfect.

Row r8 is inert: a dependency-closure BFS from `sixContactMin_of_open15` (`Deps.lean`) finds no consumer.

**What compiles.** `scratch/unipotent-b/UnipotentB.lean` imports only `TailZ14` and has no sorry, no warnings and
no errors. Its 18 `#print axioms` lines are all standard. `UsesCheck.lean` (restricted r6 from the restricted field)
also compiles. `UsesFail.lean` fails as expected and is kept as the record. The before/after table is in
`docs/research/unipotent-b.md` §5.

**What remains.** Read SGA 7 IX 3.5 in the print to fix three things: the wording, whether semistability is read
over `k(s)` or geometrically, and the number. `SemiAbelianDescendsSepClosed` is unproved (it needs SGA 3 XIV maximal
tori and descent of properness). Dropping the inert r8 is a lead decision.
