# Theorem 5.3 lane: deliveries of 2026-11-19 (second upstream batch)

This note records what the second upstream batch of the Theorem 5.3 lane adds, how each piece is
classified, and which inputs stay named. Nothing here discharges a hypothesis of
`ZInQ.OneProof.frozenTarget`. The common-coordinate leaf is not wired by this batch. Lane labels (E1, E2,
RC32, RC36, RC37, U7) are those used on issue #83.

## New files

All 43 new modules use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`):
893 constants, each checked with `Lean.collectAxioms`. No new line is longer than 100 columns.

**The ramification step (`CloudB3RC53/Finiteness/TwoInSupportCompositum.lean`).** This new file
carries a proof that lives inside `TwoInSupport.lean` on the integration branch. Since existing
modules change only in folds, it is upstreamed as a new file that keeps the declarations' names:
`unramifiedOutsideSup_proof` (the inertia group of a compositum restricts to the trivial inertia
groups of its factors), and from it `finiteUnramifiedSupport_proof`, `twoPowerRootsRamified_proof`
and `h2_of_hasFullTwoTorsion_proof`. So `h2`, every place above 2 lies in `S`, follows from full
`2`-power torsion alone, and the two statements that `TwoInSupport.lean` still lists as stated are
proved. `E2ChainActual.lean` and `StagedBounds.lean` import this file instead of
`TwoInSupport.lean`; that import line is the only difference from their integration-branch
versions.

**Ring class fields (lane E1, `CloudB3E1Dihedral/`).**
- `ringClassDihedral`: conjugation by τ acts by inversion on Gal(H_f/K). This is PROVED, so the
  statement `RingClassDihedral` of `CloudB3E2Norm/XiConj.lean`, which cites Cox, Lemma 9.3, no
  longer needs the print.
- The route is short: J·κJ = (N J) for every J prime to f, Frobenius transport along τ, and
  uniqueness of Frobenius at unramified primes. Ideals prime to f generate. τ-stability of H_f comes
  from Bauer's theorem, using the Chebotarev density theorem already in the tree.
- `xiConj_family'` (`XiConjNoPrint.lean`) is the anticyclotomy of the family character with no
  print and no named input.
- `exists_genuineFamilyMovingCharacter_xiConj` provides one family character with exact supports
  that serves both leaves.

**The common-coordinate inputs (lanes E1 and E2, `CloudB3E2Norm/`, `CloudB3E1Torsion/`,
`CloudB3E1RingClass/`).**
- **Chain inputs.** `e2ChainInputsS_of_actual` builds the chain inputs from the actual objects.
  - It derives the conductor, its admissibility, the 2-part, the separation and the q-conditions.
  - Named: the Cai–Chen–Liu print with its anchor, `hS2N`, `hrk`, `hQS0`, `hpidx` and `hQ3`, each with
    its tex lines and its status (stated by the text, or a formalization requirement).
- **Good reduction.** `hgood_of_support` (`E2ChainGood.lean`) gives good reduction of the actual
  curve outside 6ℓ, from the integral model `[0, 2ℓ, 0, −3ℓ², 0]` with Δ = 2⁸·3²·ℓ⁶.
- **Support requirements.** `SupportReq.lean` derives `hS2N` and `h3ℓ` from:
  - `LevelPrimesBad` (GLUE: Carayol, Théorème A), naming the primes dividing the newform level as
    primes of bad reduction;
  - `hbase`, the fixed support inside the data's support;
  - `hS₀D`, the coefficient support containing the fixed support (tex 2729–2741).
- **Coefficient field and family character.** `exists_leafCoef` (`FamilyCoef.lean`) supplies them
  for the leaf over ℚ(s₀), with exact supports.
- **First-stage model shape.** `st0Shape_of_inputs` (`St0Shape.lean`) supplies the shape of the
  first-stage models.
  - Named: `GenCxResidualIso`, the PRINT `StageEulerZero` (Milne, *Arithmetic Duality Theorems*,
    I.5.1, I.4.10(c), I.2.8; used at tex 4520–4550), and `StageH0LtH1`.
  - `GenCxResidualIso` is reduced to the standard-old reference family by `GenCxResidual.lean`,
    `RingChangeResidual.lean`, `GenCxActualForm.lean`, `GenCxStaged.lean` and the ring-change files
    of `CloudB3E1Torsion/` (`genCxResidualIso_staged_of_standardOld`).
  - `standardOld_producerBounds_staged` (`StagedBounds.lean`) instantiates the producer bounds and
    leaves the Milne prints named.
- **Model comparisons.** `kmCoord_comparison_unit` (`KmLamUnit.lean`), `kmCoord_smul` (`KmScale.lean`)
  and the augmented lift (`AugLift.lean`) handle the comparison of two models.
- **Retained models.** `RetainedModels.lean` builds retained models of the full support from the
  chain data.

**Central stage comparison (lanes E2 and U7).**
- `CentralSpecC1.lean`: `CentralStageComparison₂`, with the concrete coefficient half proved (named:
  `hψ1`).
- `CentralTwistDict.lean`: the twist dictionary between the central curve and the presentation.
- `RC53Assist/CentralStageReduction/ReductionV3.lean`: `comparisonOfDictionary` builds the reduction
  `red` and proves `hred` from a twist dictionary. The dictionary's existence is not claimed.

**The Kummer coefficient comparison (lane RC37, `OneProof/RC/Wiring/KummerComp*.lean`).**
- For K = ℚ(√k) with k < 0, there is a genuine chain map from the truncated compact central Kummer
  complex with ℚ₂/ℤ₂ coefficients to the discrete Selmer complex. It is a quasi-isomorphism in every
  degree. `kc_hcomp_central` proves the calibration's `hcomp` for it.
- One input is named: `KcArithSelmerLevel`, the finite-level Selmer group described through G_{K,S}.
  It now assumes E elliptic, a fix from its external review.
- `KcSelSplit.lean` splits it as `KcSelOfLoc ∧ KcLocOfSel`. The first follows from a per-place input
  `KcSelOfLocFinite` (PRINT + GLUE: Milne, I.3.8, pp. 46–47, outside S; locator unverified).
  `KcLocOfSel` stays named (Silverman, X.4.4; locator unverified).

## Statements shown false or uninhabited, recorded in Lean

- **`not_retainedMapsToCochains`** (`RetainedModels.lean`): the unconditional
  `RetainedMapsToCochains` of `CommonCoordinate18Retained.lean` fails for a zero complex. Its
  docstring now says so; nothing uses it.
- **`not_orthComparisonInverse_ecurve`** (`OrthNoInverse.lean`, `InvariantSocle.lean`, `ModTwo.lean`):
  for the curves E_ℓ, the structure `OrthComparisonInverse` is uninhabited at every stage i ≥ 1. This
  holds for any comparison φo, as soon as there is an index.
  - The obstruction is ⊕_v H⁰(K_v, M) at two places that both go from zero to full conditions.
  - The text inverts the comparison only after the inner limit, with the retained old-place lattice
    comparison (tex 3704–3790).
  - `OrthInvLoc.lean` states that localized form (`OrthComparisonInverseLoc`, `hlift_of_urSurj`).
    Its two named inputs, the local contractions and `UrSurj`, are true only after localization;
    `UrSurj` still needs det(Φ − 1) ≠ 0.
  - The docstrings of `DualPres.lean` and `H20PairedLift.lean` record this. No result that uses the
    finite-stage structure reaches the headline.

## Comment-only changes

- `MilneADT_I_2_8` (`RC/Limits/LocalPrints.lean`): the verbatim text of Milne, I §2 (p. 26
  conventions; p. 31, Theorem 2.8), kind PRINT + GLUE. The printed vanishing bound "r ≥ 2" is read as
  r > 2.
- `IwasawaGenerators` (`RC/Local/TameLocalPlace.lean`, `TamePlaceBridge.lean`): relabelled as a
  classical input not cited by the manuscript, plus GLUE.
- `CalibrationLeafLit.lean` and `SignedNonVacuity.lean`: the signed calibration covers either sign
  of h, and the concrete comparison inhabits the signed input for k < 0.
- `KummerInj.lean`: ι and `hcomp` are proved.

## Review status

- **Signed calibration (lane RC36; on `main` since the merge of |141|).** An independent review
  rated it SOUND. It rebuilt the files from a clean clone, found standard axioms only, checked the
  signs (no |t| substitution, no positivity) and checked that the type matches
  `KummerCoordinateBlockLit.rank_one`.
  - The theorem is a conditional implementation. Named inputs: `KummerCoefficientComparisonSigned`,
    finite generation, the two rational coranks, the nine book statements of the calibration, and
    `KummerCorankOneGlue`.
  - `KummerCorankOneGlue` assumes rank one AND finite Ш. At the covered addresses both come from the
    Kolyvagin print at analytic rank one, through the BCDT print.
- **Kummer coefficient comparison (lane RC37).** The same review rated it SOUND WITH FIXES. The one
  required fix, the ellipticity premise, is in this batch. Optional notes on locators and wording
  are applied.
- **Local–global decomposition glue (on `main`).** Reviewed. An isolated current-tree
  build / axiom / import check is still pending.
- **Remaining new files.** Each was reviewed by its delivering lane's reviewer before delivery. They
  have not had a second, independent review.

## Draft ledger rows for the integrator

`credits.tsv` and `reviews.tsv` belong to the integrator. These rows are offered for the fold that
lands this batch; `fold` and `commit` are left for the integrator.

```
item	kind	contributor	ai_assisted	relayed_by	url	fold	commit
signedCalibrationRankOne	reduction	project	yes		https://github.com/Deicyde/diophantine-z-q/pull/141
ringClassDihedral	proof	project	yes		(this pull request)
kummerCoefficientComparison	reduction	project	yes		(this pull request)
centralStageComparisonC2	reduction	project	yes		(this pull request)
commonCoordinateChainInputs	reduction	project	yes		(this pull request)
orthComparisonInverseObstruction	statement-check	project	yes		(this pull request)
```

The lane's contributions note for the `RC53Assist` work (`rc53assist-contributions-20261119.md`,
added in this batch) carries its own draft rows.
