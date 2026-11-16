# aftate-or results log

Target: make weber-field's `R16IsJ1Dict.AfTateCharPolyPicZero` printed (base wip/weber-field f2cf835b).

## Setup
- 11-16 06:40 build dirs copied (reflink) from ~/dzq-wt/weber-field (same commit f2cf835b): .lake/build, lean/.lake/build.

## Inventory (VERIFIED by reading the tree)
- `R16IsJ1Dict.AfTateAt` (charpoly form), `AfTateWeakOddAt` (satisfies + odd), `component_charpoly`,
  `odd_of_charpoly` (needs `TateModuleFree`, `χ(−1) = 1`), `weakOdd_of_afTate`, `r16CoreY_of_weakOdd`,
  `abVarIso_picZero_of_isJacobian`, `exists_picZero`, `AfTateWeakOddAt.of_iso`, `fieldX1Equiv` (R16IsJ1Dict.lean).
- `X1Igusa.Weber.WeberFieldComparison` (N ≥ 2, ∃ P of exact order N, ℚ-relations of (j, f₁) on {g₂g₃ ≠ 0} = relations of
  (j, w(P))), proved `weberFieldComparison`; `adjoin_wOf : ℚ(j)(w(P)) = fieldX1 P` (WeberField.lean).
- `X1Igusa.x1PointsConjugate_of_igusaGL2DS` (X1Igusa.lean).
- Oddness in the tree: only as the clause of isj1-dict's `AfTateWeakOdd*` leaves and as the Lean consequence
  `odd_of_charpoly` of the charpoly form. No bundle leaf gives oddness of `V_ℓ(A)` components for the existential `A`
  (searched: `T12_ComplexConjEigen` gives only balanced ±1 eigenspaces on all of `V_ℓ(A)`; `GaloisRep.IsOdd` concerns
  other representations; no Ribet irreducibility leaf). VERIFIED (grep of ZInQKernel).
- Mathlib: `ModularForm.levelOne_weight_two_rank_zero` (no weight-2 level-one forms), for the `N = 1` case.

## Lean (scratch/aftate-or/AfTateOr.lean, `lake env lean`)
- 11-16 06:45 defs `IsX1AlgDS`, `AfTateOrAt`, leaf `AfTateDSOr`; `weakOddAt_of_orAt`, `orAt_of_afTateAt`,
  `orAt_of_weakOddAt` compile. VERIFIED.
- 11-16 07:05 `isX1AlgDS_of_isX1Model` (kernel model ⇒ DS's X₁(N)_alg, N ≥ 2; uses weberFieldComparison, adjoin_wOf,
  fieldX1Equiv, X1PointsConjugate) compiles; axioms standard. VERIFIED.
- 11-16 07:15 `not_isNewform_one` (Mathlib `levelOne_weight_two_rank_zero`), `weakOdd_of_dsOr`,
  `r16CoreY_of_dsOr_igusaDS : AfTateDSOr → IgusaGL2DS → MumfordTorsionAlgClosed → R16CoreY` compile; axioms
  [propext, Classical.choice, Quot.sound]. VERIFIED.
- 11-16 07:50 contribution ZInQKernel/Contrib/OneProof/AfTateOr.lean (same declarations + docstrings): `lake build ZInQKernel.Contrib.OneProof.AfTateOr` Build completed successfully (11357 jobs; only the new module compiled, 9.7 s). VERIFIED.
- 11-16 07:55 #discharges (scratch/aftate-or/Discharges.lean -> Discharges-output.txt): `DISCHARGES [OpenResearchLeaves23.r16CoreY] by AfTateOr.r16CoreY_of_dsOr_igusaDS still assumes: [AfTateOr.AfTateDSOr, X1Igusa.IgusaGL2DS, AvSplit.MumfordTorsionAlgClosed] axioms: [propext, Classical.choice, Quot.sound]`; all #print axioms standard. VERIFIED.
- 11-16 08:00 autofold spec scratch/aftate-or/autofold.json (field r16CoreY; leaves afTateDSOr NEW, igusaGL2DS unchanged
  from weber-field). `python3 scripts/one_proof/autofold.py scratch/aftate-or/autofold.json --dry-run`:
  `strict count: 45/10 on 55 -> 47/9 on 56; strictest 43/12 -> 45/11`. Output (line 1 stripped) =
  scratch/aftate-or/FoldDryRun.lean; `lake env lean` compiles; `HDec.HSyn.sixContactMin_of_open31` axioms
  [propext, Classical.choice, Quot.sound]. VERIFIED.
