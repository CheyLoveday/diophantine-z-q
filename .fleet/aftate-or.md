# aftate-or (fleet summary)

**Result.** weber-field's `AfTateCharPolyPicZero` (review: GLUE) is replaced by the new leaf
`AfTateOr.AfTateDSOr`, rated LEAF (printed form). `r16CoreY` is discharged from it plus the existing LEAF
`X1Igusa.IgusaGL2DS` and the bundle's `mumfordTorsionAlgClosed`:
`AfTateOr.r16CoreY_of_dsOr_igusaDS : AfTateDSOr → IgusaGL2DS → MumfordTorsionAlgClosed → R16CoreY`
(standard axioms).

How the new leaf answers the review's three objections:
- **DS 9.5.4 wording.** The conclusion is (characteristic polynomial) ∨ (satisfies ∧ odd). These are isj1-dict's
  `AfTateAt` and `AfTateWeakOddAt` verbatim, so either reading gives the leaf by or-introduction. The consumers' form
  is recovered from either disjunct (Cayley–Hamilton, `odd_of_charpoly`, `component_charpoly`).
- **Existential over models.** The leaf is now universal over models of DS's own `X₁(N)_alg` (`IsX1AlgDS`: a smooth
  proper curve with function field `ℚ(j, f₁)`, where `f₁` is the kernel's Weber function, given by generators and
  relations), with a rational point, and over all `Pic⁰` representatives.
- **K_N dictionary.** Both directions are proved: `isX1AlgDS_of_isX1Model` (weberFieldComparison + Igusa) and
  `isX1Model_of_isX1AlgDS`.

Never stronger: `dsOr_of_picZero` and `dsOr_of_weakPicZero` derive the new leaf from isj1-dict's leaves. `N = 1` is
handled by `not_isNewform_one`, from Mathlib's `S₂(SL₂(ℤ)) = 0`.

**Compiles (VERIFIED).**
- `lake build ZInQKernel.Contrib.OneProof.AfTateOr`: OK.
- `#discharges`: `DISCHARGES [OpenResearchLeaves23.r16CoreY] by AfTateOr.r16CoreY_of_dsOr_igusaDS`, still assuming
  `[AfTateDSOr, IgusaGL2DS, MumfordTorsionAlgClosed]`, standard axioms.
- Fold dry run (`scratch/aftate-or/autofold.json`): strict 45/10 → 47/9, strictest 43/12 → 45/11;
  `sixContactMin_of_open31` has standard axioms.
- Under the review's rating of the old leaf (GLUE), this fold is −1 GLUE.

**Remains (readings, not glue).**
- Under the "satisfies" reading, oddness of `ρ_{A_f,ℓ}` must come from the printed `det ρ_{A_f,ℓ} = χχ_ℓ` for the same
  `A_f`. No tree leaf gives it (T12, Faltings, DSThm965, Hodge–Tate and CharPolyIndepOfEll checked; report §4).
- `A_f` stays existential, since there are no Hecke correspondences in Lean.
- Locators are UNVERIFIED (no network).

Report: docs/research/aftate-or.md. Scratch: scratch/aftate-or/.
