# r16-close: `r16CoreY` through the leaves of aftate-fix2, with Diamond–Shurman 9.5.4 as printed

Task r16-close, branch `wip/r16-close`, base `origin/main` c0f3d085c (leaf-fold33b; `frozenTarget` through
`HDec.HSyn.sixContactMin_of_open48`, TailZ55), with aftate-fix2 (c56922c0) merged (no conflicts; it brings
`ZInQKernel/Contrib/OneProof/{AfTateLambda,AfTateOr,R16IsJ1Dict,R16Used,WeberField,X1Igusa}.lean`, none of them on
main before). Date 2026-11-16/17. New Lean: `ZInQKernel/Contrib/OneProof/R16CoreYSatDet.lean`. Scratch:
`scratch/r16-close/` (results log `log.md`). Nothing else under `ZInQKernel/` or `blueprint/` was edited. Model
work, no human review.

Marks: **VERIFIED** = compiled, or read in a source or a file of this tree. **STANDARD** = published, with a
reference. **SPECULATIVE** = a judgement. **UNVERIFIED** = recalled without a source.

## 0. Result

1. **Statement check: Diamond–Shurman Thm 9.5.4 prints "satisfies", not "characteristic polynomial"**
   (VERIFIED: read in both printings on this host, `~/cloud-b4/w24/diamond-shurman-2005-original.pdf`, printed
   pp. 390–391, and `…-2016-fourth-printing.pdf`, pp. 401–402; the independent W24 check
   `~/cloud-b4/w24/reports/report-ds954.md` reads the same). The print says that `ρ_{f,λ}(Frob_𝔭)` "satisfies the
   polynomial equation" `x² − a_p(f)x + χ(p)p = 0`. DS print "the characteristic equation" only in Thm 9.6.5,
   the general-weight theorem, whose `ρ_{f,λ}` is an abstract representation, not the realization on `A_f`.
   DS derive the determinant `det ρ_{f,λ} = χχ_ℓ^{k−1}` only for 9.6.5's `ρ` (Exercise 9.6.3(a)).
   So aftate-fix2's leaf `AfTateLam.AfTateDSLambda` (the characteristic polynomial on `V_λ(A_f)`) **is stronger
   than its print**. It is not a printed-form LEAF. aftate-fix2's "reading risk" is resolved against it.

2. **`r16CoreY` is discharged with five new hypotheses: four printed-form LEAF and one GLUE** (VERIFIED,
   compiled, standard axioms; §3):

   ```lean
   theorem AfTateLam.r16CoreY_of_sat_det (h1 : AfTateLam.HeckeJ1DS) (h2 : AfTateLam.AfShimura)
       (hS : AfTateLam.AfTateDSLambdaSat) (hD : AfTateLam.AfDetLambda) (hI : X1Igusa.IgusaGL2DS)
       (hM : AvSplit.MumfordTorsionAlgClosed) : R16Split.R16CoreY
   ```

   It is aftate-fix2's `r16CoreY_of_printed` with its third leaf replaced by aftate-fix2's fallback pair
   (`dsLambda_of_sat_det`, proved by aftate-fix2):
   - `AfTateDSLambdaSat` is DS Lemma 9.5.3 together with Thm 9.5.4 **as printed** (LEAF).
   - `AfDetLambda` is `det ρ_{f,λ}(Frob_p) = χ(p)p` (GLUE: no print found).

3. **Count.** `r16CoreY` (GLUE) leaves. Five fields enter: `heckeJ1DS`, `afShimura`, `afTateDSLambdaSat`,
   `igusaGL2DS` (published, LEAF) and `afDetLambda` (consequence, GLUE). **GLUE is unchanged; the target −1 GLUE is
   not reached.** The obstacle is exactly the determinant of `ρ_{f,λ}` on `A_f`. The composite glue `r16CoreY` is
   replaced by the single statement `det ρ_{f,λ}(Frob_p) = χ(p)p`. Fold dry-run numbers are in §3.

4. **Fields of main (VERIFIED, grep of `docs/one-proof/kinds.tsv` and `ZInQKernel/OneProof/H/`):**
   - `mumfordTorsionAlgClosed` is an open textbook LEAF field of main's bundles (kinds.tsv row 28). It is proved
     by fork PR #54 (`ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof`, branch
     `origin/proof/mumford-torsion-review-20261117`), which `origin/wip/fold34-pr` is folding. Not on main.
     The spec uses `{t}.mumfordTorsionAlgClosed`; after fold34-pr, substitute the proof.
   - `X1Igusa.IgusaGL2DS` is neither a field nor proved on main. It enters as a new leaf, as in aftate-fix2.

5. **None of the leaves is proved outright** (§4). Each is a theorem about modular Jacobians (Hecke
   correspondences, Shimura's quotient, Eichler–Shimura, Igusa) with no Lean infrastructure in Mathlib or the
   tree. Printed forms, locators and ratings are in §4; every DS locator was read in this task.

## 1. The determinant: what is missing

`R16CoreY` (a fixed bundle field) asks, on each `ι`-component of `V_ℓ(A_f)`, for the trace `ι(a_p)` and the
determinant `ι(χ(p))p` of Frobenius. From the printed "satisfies" form on a 2-dimensional `V_λ`, the
characteristic polynomial follows except when `ρ_{f,λ}(Frob_p)` is a scalar root of the quadratic. So one more
input is needed, and **either of these suffices**:

- **Determinant**: `det ρ_{f,λ}(Frob_p) = χ(p)p` (`AfDetLambda`, proved sufficient by `dsLambda_of_sat_det`).
  Its derivation needs two things the tree does not have (VERIFIED, grep: no `e_ℓ`-pairing on `PkgI3.AbVar`):
  the Weil pairing on `V_ℓ(J₁(N))`, Galois-equivariant into `ℚ_ℓ(1)`, and the adjointness `T_p* = ⟨p⟩⁻¹T_p`.
- **Trace**: `tr ρ_{f,λ}(Frob_p) = a_p`. With "satisfies" this also gives the characteristic polynomial: a scalar
  root `r` with `2r = a_p = r + r'` forces `r = r'` (argument, not formalized). No print of the per-`λ` trace on
  `A_f` was found either. Shimura 1973 Thm 1's zeta clause gives only the total Euler factor, and the audit
  (locators.md row R16) attaches an extra `Γ₀`/Fricke condition to it.

Comparing with main's research LEAF `dsThm965Printed` (DS 9.6.5, characteristic polynomial for an abstract `ρ`)
does not close the gap. By Chebotarev and continuity it shows `ρ_{f,λ}(g)² − t'(g)ρ_{f,λ}(g) + d'(g) = 0` for
all `g`. The determinants then agree off the closed subgroup `S` of elements acting as scalars. This decides the
question only when `S` has infinite index, and excluding an open `S` needs the arithmetic of `A_f`
(SPECULATIVE outline, not formalized).

Candidate printed sources for the determinant, all unread (UNVERIFIED): Shimura 1971 Thm 7.14, and Ribet, LNM 601
(1977) §§1–2. If a statement check finds `det ρ_{f,λ} = χχ_ℓ` printed for the realization on `A_f` (or the
characteristic polynomial, at either `K_f ⊗ ℚ_ℓ` or `K_{f,λ}`), `afDetLambda` becomes a LEAF and the count drops
by one GLUE. aftate-fix2's `dsLambda_of_tensor` already accepts the `ℚ_ℓ ⊗ K_f` form.

## 2. Lean

`ZInQKernel/Contrib/OneProof/R16CoreYSatDet.lean` (new) imports `ZInQKernel.Contrib.OneProof.R16Split` (which
declares `R16Split.R16CoreY`) and `ZInQKernel.Contrib.OneProof.AfTateLambda` (aftate-fix2). It does not import
`OneProof.Main`. It contains one theorem, `AfTateLam.r16CoreY_of_sat_det`, defined as
`r16CoreY_of_printed h1 h2 (dsLambda_of_sat_det hS hD) hI hM`. The statements (all aftate-fix2's, unchanged) are
in `AfTateLambda.lean`:
- §5: `HeckeJ1DS`, `AfShimura`;
- §9: `AtFrobLam`, `AfTateDSLambdaSat`, `AfDetLambda`;
- `X1Igusa.lean`: `X1Igusa.IgusaGL2DS`.

The docstrings of `AfTateDSLambda` and `AfTateDSLambdaSat` in `AfTateLambda.lean` still describe DS 9.5.4 as
undecided. That file is aftate-fix2's and was not edited. The corrected wording is in the new file's header and
in the autofold leaf docs.

## 3. Checks

PENDING (filled in from scratch/r16-close/log.md when run).

## 4. Leaf ratings and printed forms

Every DS locator below was read in this task, in the 2005 printing (pdftotext of the audit copy; page numbers
from the running heads). That reading is AI-read, not a human reading.

| leaf | Lean | printed form? | kind / strict | printed statement and locator | reason |
|---|---|---|---|---|---|
| `heckeJ1DS` | `AfTateLam.HeckeJ1DS` | **yes** | published / LEAF (unread) | DS §6.3 (pp. 226–227): the double-coset operator `[Γ₁αΓ₂]₂` on `Div`, `Pic⁰` of `X₁(N)`, `Γ₂τ ↦ Σ_j Γ₁β_j(τ)`; Prop. 5.2.1 (p. 171): the representatives `(1 j; 0 p)` and, for `p ∤ N`, `(m n; N p)(p 0; 0 1)`; §7.9 (p. 300): `T_p` and `⟨d⟩` are defined over `ℚ`. | The Lean action on `[x_τ] − [x_τ']` through Abel–Jacobi is DS's divisor formula with these representatives. Over `ℚ` is §7.9. It is a consequence of the print plus the standard passage from a `ℚ`-rational correspondence to an endomorphism of `J` over `ℚ` (STANDARD; Shimura 1971 §7.2, unread). Not stronger: aftate-fix2 §5 argues uniqueness. |
| `afShimura` | `AfTateLam.AfShimura` | **yes** | published / LEAF (unread) | Shimura 1973 Thm 1, pp. 526–527 (read by the locator audit, row R16: the `ℚ`-rational quotient, the coefficient-field action, `dim A_f = [K_f:ℚ]`); DS Def. 6.6.3 (p. 241): `A_f = J₁(M_f)/I_f J₁(M_f)`; Prop. 6.6.4 (pp. 241–242). | `IsAfQuotient` is the universal property of `J/I_f J` (STANDARD), and `I_f` is DS's annihilator. Only the unconditional clauses of Thm 1 are used. Weakening: newforms only, `N ≥ 2`. |
| `afTateDSLambdaSat` | `AfTateLam.AfTateDSLambdaSat` | **yes** (read) | published / LEAF (unread: no human reading) | DS Lemma 9.5.3 (p. 390): `V_ℓ(A_f)` free of rank 2 over `K_f ⊗_ℚ ℚ_ℓ`; Thm 9.5.4 (pp. 390–391): `ρ_{f,λ}` 2-dimensional over `K_{f,λ}`, and `ρ_{f,λ}(Frob_𝔭)` satisfies `x² − a_p(f)x + χ(p)p = 0` for `p ∤ ℓN`. | `dim_{K_λ} V_λ = 2` is the λ-factor of 9.5.3. DS's `ρ_{f,λ}` is the λ-projection of `V_ℓ(A_f)` (DS Exercise 9.5.2(a), read), which is the base change `K_λ ⊗_{ℚ_ℓ⊗K_f} V_ℓ(A_f)` of the Lean. "Satisfies" is the printed wording. Weakening: newforms only, unramifiedness dropped. |
| `afDetLambda` | `AfTateLam.AfDetLambda` | **no** | consequence / GLUE | `det ρ_{f,λ}(Frob_p) = χ(p)p` for `p ∤ Nℓ`. Not in DS for 9.5.4 (VERIFIED: DS's determinant statements are in §7.6 (`E[N]`) and §9.6 (9.6.5's `ρ`) only). Candidates: Shimura 1971 Thm 7.14, Ribet 1977 (UNVERIFIED, unread). | True (STANDARD: `ρ_{f,λ}` has `det = χχ_ℓ`), but no printed locator was read. See §1. |
| `igusaGL2DS` | `X1Igusa.IgusaGL2DS` | **yes** | published / LEAF (unread) | DS Thm 7.6.3 (p. 289): `ρ : Gal(ℚ(j, E_j[N])/ℚ(j)) ≅ GL₂(ℤ/N)`, with `E_j : y² = 4x³ − (27j/(j−1728))x − 27j/(j−1728)` of (7.12) (p. 281). | The Lean states surjectivity in every basis of `E_j[N]` over an algebraic closure of `ℚ(j)`, which is the printed isomorphism. x1-igusa's locator was UNVERIFIED and is now read. |
| (dropped) `afTateDSLambda` | `AfTateLam.AfTateDSLambda` | **no** | — | DS 9.5.4 prints "satisfies" (above) | Stronger than the print. It is still used inside the proof, derived from the pair. |

Proposed `locators.md` rows (that file is not this task's to edit):
- `heckeJ1DS`: DS GTM 228 (2005) §6.3 pp. 226–227, Prop. 5.2.1 p. 171, §7.9 p. 300; read (AI).
- `afTateDSLambdaSat`: DS Lemma 9.5.3 p. 390, Thm 9.5.4 pp. 390–391 (2016: pp. 401–402); read (AI), wording
  "satisfies the polynomial equation".
- `afDetLambda`: no locator; Shimura 1971 Thm 7.14 and Ribet 1977 to be checked.
- `igusaGL2DS`: DS Thm 7.6.3 p. 289, (7.12) p. 281; read (AI).

## 5. Files

- `ZInQKernel/Contrib/OneProof/R16CoreYSatDet.lean`: the contribution (new).
- `scratch/r16-close/Target.lean`: verbatim copy of `R16Split.R16CoreY` with `copy_iff : … := Iff.rfl` and the
  discharge at the copy.
- `scratch/r16-close/Discharges.lean`, `Discharges-output.txt`: `#discharges` and the axiom prints.
- `scratch/r16-close/autofold.json` (made by `make_spec.py`), `FoldDryRun.lean`, `FoldDryRun-output.txt`: the fold
  spec and its dry run.
- `scratch/r16-close/log.md`: the results log.
