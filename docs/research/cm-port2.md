# cm-port2: fold the CM fibre split through the proper integral Y₃ model

**VERIFIED (Lean).** The CM order port supplies the unchanged `HDec.CMBranch.CMFibreSplit` from
the open83 research fields. The generated fold removes that field and introduces
no leaf or glue field. The port is on fork main `c3624d0e3` (clean merge
`6954f7422`).

- Before: **H strict LEAF/GLUE 5/27 on 32** (main's `kinds.tsv`).
- After: **H strict LEAF/GLUE 5/26 on 31** (autofold dry run; strictest agrees).

## Exact statements and suppliers

**VERIFIED (source).** [Statements.lean](../../scratch/cm-port2/Statements.lean)
copies the bodies of `CMFibreSplit`, `CMHomFieldModel` and `CMCurveOrder324`
verbatim and imports their dependencies. The existing consumer, matrix-unit
splitting proof (`cmMatrixUnitSplit_of`), curve-order proof
(`cmCurveOrder324_of`) and its specialization (`cmCurveOrder_of_324`) are
unchanged.

[The R6U provider](../../ZInQKernel/Contrib/OneProof/CMCurveOrder/R6U.lean)
copies the Hom-field proof. The changed call is `good_of_QML3U`, passing
`T324_subset_T u` instead of `three_mem_T u`. The old Raynaud criterion on
all inertia drops out of the provider. The two existing R6U components
are the conclusion about wild inertia and the proper integral full-level-three
moduli model; the good-reduction theorem reads only the latter.

| Supplier on open83 | How the new provider gets it |
| --- | --- |
| Good reduction outside `T(u)` | `good_of_QML3U` uses `R6U.2` and `T324_subset_T u`. |
| `R6U` | The existing conversions from `silverbergZarhinThm35`, `elliotWildInertiaTrivial` and `neronSchemeExtensionDedekind`, paired with `y3FullThreeRepZ30`, as in `Y3Open`. |
| Fibre cover (G2) | `fibreCoverExists_of_propTSAll'` on the same inputs as `Y3Copy5`. The moduli row uses `y3ToP1j` and the existing ray-class conversion; the vertical witness uses `heckeSqrtBranchAny_proof y3ToP1j`, as in TailZ90. The Néron extension and `deligneCanonicalModelY3EveryPrint`, together with the integral model, also supply the group law and connectedness inputs through the existing conversions. |
| Néron–Ogg–Shafarevich | `neronOggShafarevich_of_sep` on the existing `neronOggShafarevichSep`. |
| Yu dichotomy (T27), Hom lattice (T6), torsion (T5) | `yuB6Alg_of'`, `homFreeFiniteC` and `AvSplit.Final.h25` from the existing uniformization, GAGA and torsion proofs. |

**On-the-spot (Lean glue).** [CMCurveOrderLive.lean](../../ZInQKernel/Contrib/OneProof/CMCurveOrderLive.lean)
takes the inputs of the existing bundle conversions directly, so it does not
need an old bundle that already contains the goal. The fine moduli model and
Deligne form give the same connectedness and ray-class statements that the
live path threads to the fibre-cover call. The same T5, automorphism, rigidity,
fixed-point and vertical-witness proofs then supply Proposition TS for that
call. The Hom-field proof uses the resulting rational fibre, constructs the
kernel field of the Hom-lattice action and passes to its compositum with the
fibre field, as before. The existing matrix-unit proof then applies to the
model over that compositum. This introduces no new mathematical hypothesis.
The inherited on-the-spot corner and order arguments are sketched in
[cm-curve-order](cm-curve-order.md#manuscript-check-and-proof).

## Manuscript check

**VERIFIED (11/5 TeX).** In the proof of `thm:height`, L529–530 gets good
reduction from the proper model and its universal abelian scheme.
L557–561 uses good reduction of each conjugate in the Hom-field construction.
`D2A6.hasGoodReduction_of_z30` implements the first step: classify the generic
fibre, use properness to extend the classifying map over the valuation ring,
then pull back the universal abelian scheme. The residue characteristic is
greater than 324 outside `T(u)`, so it does not divide 30. This constructs
a good model and thus addresses the concern about multiplicative reduction
at these places. At L814–818, semistability after adjoining prime-to-residue-
characteristic torsion gives the wild-inertia assertion for the later conductor
bound. The port packages that component using the live conversion; it does
not infer good reduction from trivial wild inertia. The CM split at L582–586
then uses the Hom field and the existing matrix-unit and order proofs.

**STANDARD (from the existing print reading).** Silverberg–Zarhin, *Ann. Inst.
Fourier* 45 (1995), Thm. 3.5, p. 406, cited at L816: semistability given rational
`n`-torsion, `n ≥ 3` and prime to the residue characteristic.
[The page reading](sz-raynaud.md#4-known-issues-in-the-sources) confirms
`≥`, so both `n = 3` and the `n = 5` substitute in residue characteristic 3
are covered. The wild-inertia sentence remains an existing manuscript premise.
There are no new leaves to rate; no existing flag or rating changes.

## Known issues

- The `Y₃` input is the existing GLUE row for the manuscript's own conclusion
  at L473–477. It states representability in polarization-free form; the
  relative canonical-polarization comparison is still open, as recorded in
  [y3-route-a](y3-route-a.md) and [d2a6b](d2a6b.md#9-known-issues).
  The port uses the row as a premise and makes no claim to prove that comparison.
  The old direct locator to Buzzard for level three is inapplicable; the
  manuscript invokes Buzzard at level five (L443–446) and descends to level
  three. The precise Buzzard locator is UNVERIFIED here. No alternate source is
  substituted.
- The previously merged CM argument gets the endomorphism dichotomy from the
  chain's Yu supplier rather than redoing the Hodge-centralizer argument at
  L564–577. That inherited difference is recorded in
  [cm-curve-order](cm-curve-order.md#known-issues); this port starts with the same
  dichotomy. It supplies no Gross–Zagier or Tian–Yuan–Zhang argument.

## Fold and handoff

[Autofold spec](../../scratch/cm-port2/autofold.json) and
[computed counts](../../scratch/cm-port2/autofold-counts.txt).
`python3 scripts/one_proof/autofold.py scratch/cm-port2/autofold.json --dry-run`
generates the [fold](../../ZInQKernel/Contrib/OneProof/CMCurveOrder/FoldOpen84.lean).
It promotes `OpenResearchLeaves64` to `OpenResearchLeaves65` and open83 to
open84. The [scratch headline](../../scratch/cm-port2/MainDryRun.lean) keeps
`OpenTextbookLeaves18`, `OpenAddedLeaves28` and the four separate assumptions
`hRC`, `h54`, `hB`, `hK` as on Main. `Main.lean` and `kinds.tsv` have not
been edited. The integrator can use the generated proof or run the same spec
without `--dry-run` in the integration worktree.

**VERIFIED (Lean 4.35.0).** The provider and generated fold compiled, and
`Statements.lean` proved the three definitional equalities by `Iff.rfl`.
The [axiom output](../../scratch/cm-port2/axioms.txt) reports only `propext`,
`Classical.choice` and `Quot.sound` for the new `FrozenTarget`, the new
`SixContactMin` and the CM proofs. The stock `#discharges` check against
unmodified Main reports `DISCHARGES [OpenResearchLeaves64.cmFibreSplit]` by
`cmFibreSplit_of_liveInputs`, with exactly seven existing research inputs;
the field-binder check also reports `DISCHARGES [cmFibreSplit]`.
[Transcripts](../../scratch/cm-port2/discharges.txt) and
[results log](../../scratch/cm-port2/log.md). The checks ran one Lean
process at a time with the local dependency caches, not a cold build.
