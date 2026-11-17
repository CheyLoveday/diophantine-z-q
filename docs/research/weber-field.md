# weber-field: `WeberFieldComparison` (`ℚ(j, f₁) = ℚ(j)(x(P))`) proved

Task weber-field, branch `wip/weber-field`, base `wip/x1-igusa` 62d9b7c5. Date 2026-11-16.
Lean: `ZInQKernel/Contrib/OneProof/WeberField.lean` (new, 973 lines, 48 KB). It imports `X1Igusa`, `RingClassLattice`,
the vendored uniformization `Thm_PeriodPair_isUniformization_toPoint` (AnthropicFLT) and Tau Ceti's
`DivisionPolynomial.Torsion.Roots` and `.Coprimality`. It does not import `OneProof.Main` and has no build-time code.
Scratch: `scratch/weber-field/`; the results log is `log.md`.
Nothing else under `ZInQKernel/` or `blueprint/` was edited. This is model work with no human review.

Marks:
- **VERIFIED**: compiled, or read in a file of this tree.
- **STANDARD**: published, with a reference.
- **SPECULATIVE**: a judgement.
- **UNVERIFIED**: a theorem number recalled without a source (this host has no network).

## 0. Result

**`X1Igusa.Weber.WeberFieldComparison` is proved in Lean, with no hypotheses.** VERIFIED: it compiles,
`#print axioms` gives `[propext, Classical.choice, Quot.sound]`, and `lake build ZInQKernel.Contrib.OneProof.WeberField`
succeeds.

```lean
theorem X1Igusa.Weber.weberFieldComparison : X1Igusa.Weber.WeberFieldComparison
```

The statement is x1-igusa's (`scratch/x1-igusa/WeberComparison.lean`). That scratch file is not a module, so `wOf`,
`evAn`, `evAlg` and `WeberFieldComparison` are copied verbatim into the new file, in the same namespace. A string match
against the scratch file confirms the copies (`log.md`). x1-igusa's `adjoin_wOf` (`ℚ(j)(w(P)) = ℚ(j)(x(P)) =
fieldX1 P`) is copied too.

Consequences:
- **Gap closed.** The function-field step that x1-igusa §4 left between `R16IsJ1Dict.AfTateCharPolyPicZero` and
  Diamond–Shurman 9.5.4 is now a Lean theorem.
  - It identifies the ideal of polynomial relations of `(j, f₁)` over `ℚ` with that of `(j, w(P))`, for a point `P` of
    exact order `N` of the kernel's `E_j`.
  - With `adjoin_wOf`, this gives `ℚ(j, f₁) ≅ Frac(ℚ[J,T]/I) ≅ ℚ(j)(w(P)) = fieldX1 P = K_N`.
- **Rating.** `afTateCharPolyPicZero` remains a published leaf (printed form, unread). Its dictionary caveat is
  discharged.
  - Two caveats remain, and neither is a glue gap. `IsCurve` for `X₁(N)_alg` is part of DS's construction of that
    curve. The DS 9.5.4 wording question (characteristic polynomial against equation) is unchanged.
- **Fold.** The fold is the same as x1-igusa's and still a strict −1: `r16CoreY` (GLUE) is replaced by
  `afTateCharPolyPicZero` and `igusaGL2DS`, both LEAF. No new leaf was introduced.
  - Dry run (VERIFIED): `strict count: 45/10 on 55 -> 47/9 on 56; strictest 43/12 -> 45/11`.
  - The generated `sixContactMin_of_open31` compiles with the standard axioms.

## 1. The proof

The proof follows the sketch in x1-igusa §4: uniformization, division polynomial, identity theorem. The one
change: the sketch's factor-by-factor argument is replaced by a prime-ideal lemma, which avoids explicit
irreducible factors. All statements below are VERIFIED (compiled).

**§A. Algebraic lemma** (`exists_root_of_isPrime`).
- Statement: let `I ⊆ ℚ[J][T]` be a prime ideal with `I ∩ ℚ[J] = 0` and `0 ≠ Φ ∈ I`. Then
  `I = ker(F ↦ F(j, θ))` for some `θ ∈ \overline{ℚ(j)}`.
- Proof: `ℚ(j)[T]` is the localization of `ℚ[J][T]` at `ℚ[J]∖0` (Mathlib's `Polynomial.isLocalization`).
  - `I` extends to a nonzero prime of this PID, which is maximal and equal to `(p)`.
  - It contracts back to `I` (`IsLocalization.under_map_of_isPrime_disjoint`).
  - `θ` is a root of `p`.

**§B. Clearing denominators** (`Clears`, `exists_clears`).
- Substitute `G = 27J/D` and `x = 46656T/D`, with `D = J − 1728`, into any `P ∈ ℚ[G][x]`.
- Then some `Φ ∈ ℚ[J][T]` and `k` satisfy `e(Φ) = e(D)^k · P(27e(J)/e(D), 46656e(T)/e(D))` for every ring map `e` to a
  field of characteristic 0 with `e(D) ≠ 0`.
- Proof by induction on `P`.

**§C. The two specializations of the universal curve `y² = x³ − (G/4)x − G/4`.**
- Mathlib's `map_ΨSq` makes `ΨSqₙ` commute with specialization.
- Over `\overline{ℚ(j)}` (`evK_clears`, `exists_point_of_root`):
  - `G ↦ g_j` gives Diamond–Shurman's `E_j` (`EDSBar_eq`).
  - A root `θ` of the cleared `ΨSqₙ` gives, via Tau Ceti's `eval_ΨSq_eq_zero_iff_exists_zsmul_eq_zero`, a nonzero
    `n`-torsion point.
  - x1-igusa's change of variables `cDS` carries that point to a point `P` of the kernel's `E_j` with `w(P) = θ`.
- Over `ℂ` (`ez_clears`, `curveC_smul`, `eval_ΨSq_weber_eq_zero_iff`):
  - `G ↦ g₂³/g₃²` and `x ↦ (g₂/g₃)℘` give the curve `ℂ/⟨1, τ⟩` up to the change of variables `u² = g₂/g₃`.
  - The vendored uniformization (`toPoint` additive, with kernel the lattice) gives:
    `ΨSqₙ((g₂/g₃)℘_τ(1/N)) = 0 ⟺ n/N ∈ ⟨1, τ⟩`.

**§D. Analysis on `ℍ`.**
- **Holomorphy of `g₂`, `g₃`, `Δ`, `j`** (`diffOn_G2f`, `diffOn_G3f`, `diffOn_Jf`):
  - `g₂`, `g₃` are Eisenstein series: `T5Glue.G_eq_E` with `ModularFormClass.holo` and
    `UpperHalfPlane.mdifferentiable_iff`.
  - `Δ ≠ 0` is `disc_ppD_ne_zero`, which gives the holomorphy of `Δ` and `j`.
- **Holomorphy of `τ ↦ ℘_τ(1/N)`** (`diffOn_Pf`):
  - The lattice sum is reindexed over `ℤ²` (`latEquiv`).
  - Each term `1/(c − ω)² − 1/ω²` is bounded on a vertical strip by `K‖v‖⁻³` (`key_bound`, `shift_bound`,
    `wTerm_bound`). The bound uses Mathlib's `EisensteinSeries.r_mul_max_le`, `auxbound1` and `auxbound2`.
  - Then `differentiableOn_tsum_of_summable_norm` applies.
- **`f₁` on all of `ℍ`** (`weber_eq_Wf`): `f₁ := g₂g₃℘(1/N)/Δ` is holomorphic on `ℍ` and equals `T5Glue.weber` where
  `g₂g₃ ≠ 0`.
- **Special values** (`g3_I`, `g2_ρ`): `g₃(i) = 0` and `g₂(ρ) = 0`, from homothety invariance (`T5Glue.IsScale`).
  - Hence `j(i) = 1728` and `j(ρ) = 0`, so `j` is not a root of any nonzero polynomial on `ℍ` (`exists_eval_Jf_ne`).
  - Also some `τ₀` has `g₂g₃ ≠ 0` (`exists_good_point`).
- **Identity theorem** (`eq_zero_of_eventually`, `eq_zero_or_eq_zero`): holomorphic functions on `ℍ` form a domain.

**§E. Assembly** (`weberFieldComparison`).
- Let `I = {F : F(j, f₁) ≡ 0 on ℍ}`.
  - `I` is prime (§D).
  - `I ∩ ℚ[J] = 0`, since `j` is not constant.
  - By the identity theorem, `I` equals the ideal of `F` vanishing where `g₂g₃ ≠ 0`, which is the statement's
    left-hand side.
  - `I` contains the cleared `ΨSq_N`, by §C over `ℂ` with `N/N = 1 ∈ Λ`. That polynomial is nonzero by Tau Ceti's
    `ΨSq_ne_zero_of_Δ_ne_zero`.
- §A gives `θ`, and §C gives `P` with `w(P) = θ` and `N • P = 0`.
- If `P` had order `d < N`, the cleared `ΨSq_d` would lie in `I`. Evaluating at `τ₀` would give `d/N ∈ ⟨1, τ₀⟩`,
  which contradicts `div_nat_not_mem`.

## 2. Checks (all VERIFIED)

| check | command | outcome |
|---|---|---|
| development file | `lake env lean scratch/weber-field/WeberField.lean` | no errors; `weberFieldComparison` axioms `[propext, Classical.choice, Quot.sound]` |
| contribution | `lake build ZInQKernel.Contrib.OneProof.WeberField` | `Build completed successfully (11356 jobs)`; only the new module compiled (7.3 s) |
| `#discharges` | `lake env lean scratch/weber-field/Discharges.lean` (output `Discharges-output.txt`) | `61 open hypotheses, 2609 theorems checked, 16 discharge one`; `r16CoreY` by `X1Igusa.r16CoreY_of_picZero_igusaDS` (imported), still assuming `[AfTateCharPolyPicZero, IgusaGL2DS, MumfordTorsionAlgClosed]`; `weberFieldComparison`, `exists_root_of_isPrime`, `diffOn_Pf`, `eval_ΨSq_weber_eq_zero_iff`, `exists_point_of_root`, `adjoin_wOf`: standard axioms |
| fold dry run | `python3 scripts/one_proof/autofold.py scratch/weber-field/autofold.json --dry-run`, line 1 stripped, `lake env lean scratch/weber-field/FoldDryRun.lean` | `strict count: 45/10 on 55 -> 47/9 on 56; strictest 43/12 -> 45/11`; `HDec.HSyn.sixContactMin_of_open31` standard axioms |
| verbatim statement | string match of `def wOf`, `def evAn`, `def evAlg`, `def WeberFieldComparison` blocks against `scratch/x1-igusa/WeberComparison.lean` | all four identical |

`WeberFieldComparison` is not an open hypothesis of `frozenTarget`. It is the justification that
`afTateCharPolyPicZero` is the print, so `#discharges` lists no new discharge for it. The `r16CoreY` lines come from
the imported `X1Igusa`.

## 3. Leaf ratings

No new leaf. The fold's leaves are x1-igusa's.

| leaf | Lean | printed form? | kind / flag | reason |
|---|---|---|---|---|
| `afTateCharPolyPicZero` | `R16IsJ1Dict.AfTateCharPolyPicZero` | **yes** (DS 9.5.3 + 9.5.4 at `X₁(N)_alg`); its `K_N` dictionary step is now proved | published, unread; flag updated in `scratch/weber-field/autofold.json` | The print is about DS's `X₁(N)_alg`, defined by its function field `ℚ(j, f₁)`. `weberFieldComparison` with `adjoin_wOf` identifies that field with the kernel's `fieldX1 P` for `P` of exact order `N`, which is what `IsX1Model` asks. The curve is smooth, projective and geometrically connected by DS's construction (part of the print, not glue). Two items stay open, both readings rather than glue: the DS 9.5.4 wording (fallback `AfTateWeakOddPicZero`) and the locators (UNVERIFIED) |
| `igusaGL2DS` | `X1Igusa.IgusaGL2DS` | yes (x1-igusa §6) | published, unread | unchanged |
| (`WeberFieldComparison`) | `X1Igusa.Weber.WeberFieldComparison` | n/a: GLUE, **proved** (`weberFieldComparison`) | — | — |

**Autofold spec.**
- `scratch/weber-field/autofold.json` is x1-igusa's spec with three changes:
  - `imports` is `ZInQKernel.Contrib.OneProof.WeberField`, which imports `X1Igusa`.
  - The flag and doc of `afTateCharPolyPicZero` record that the dictionary step is proved.
  - The name and note are updated.
- Discharge, proof term and leaf set are unchanged.
- The task asked to update scratch/x1-igusa's spec if the leaf set changed. It did not change, and that file
  belongs to another task, so it was not edited. The integrator can use either spec: they produce the same fold, and
  this one also builds the comparison proof.

## 4. Findings

1. **The statement is correct as stated** (proved).
   - The restriction `N ≥ 2` is needed: `℘(1)` is a pole, and `1/N ∉ Λ` is used.
   - The hypothesis `g₂(τ)g₃(τ) ≠ 0` matches `T5Glue.weber`'s generic branch.
   - The proof shows the left-hand side is equivalent to vanishing of `g₂g₃℘(1/N)/Δ` on all of `ℍ`.
2. **New reusable facts** (VERIFIED, in the new file):
   - `τ ↦ ℘_{⟨1,τ⟩}(c)` is holomorphic on `ℍ` for real `c ∉ ℤ` with `|c| ≤ 1/2` (`diffOn_tsum_wTerm`).
   - `g₃(i) = 0` and `g₂(ρ) = 0` for Mathlib's `PeriodPair`; `j(⟨1,i⟩) = 1728` and `j(⟨1,ρ⟩) = 0`.
   - The division-polynomial criterion at Weber's point, via the vendored uniformization.
   - The prime-ideal lemma for `ℚ[J][T]`.
3. **Remaining gaps.** Nothing is left open for `WeberFieldComparison`.
   - Two other steps would be needed to make "`AfTateCharPolyPicZero` = DS 9.5.4" a Lean theorem rather than a
     reading. Both are part of DS's construction, not glue: `IsCurve` for `X₁(N)_alg`, and the elementary step from
     equal ideals to an isomorphism of function fields between a Lean scheme model and the meromorphic-function field
     `ℚ(j, f₁)`.
   - The kernel has no Lean object for `X₁(N)_alg` defined from meromorphic functions, so these are matters of
     reading, not Props to prove (SPECULATIVE).

## 5. Files

- `ZInQKernel/Contrib/OneProof/WeberField.lean`: the contribution.
- `scratch/weber-field/WeberField.lean`: the development version (the same declarations, without the module docstring, plus `#print axioms`).
  `PartA.lean` and `PartD.lean` are earlier fragments of it.
- `scratch/weber-field/Discharges.lean` and `Discharges-output.txt`: the `#discharges` check.
- `scratch/weber-field/autofold.json`, `FoldDryRun.lean`, `FoldDryRun-output.txt`: the fold spec and its dry run.
- `scratch/weber-field/log.md`: the results log.
