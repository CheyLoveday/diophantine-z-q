# aftate-or: `AfTateCharPolyPicZero` restated in printed form (`AfTateDSOr`)

Task aftate-or, branch `wip/aftate-or`, base `wip/weber-field` f2cf835b. Date 2026-11-16.
Lean: `ZInQKernel/Contrib/OneProof/AfTateOr.lean` (new; imports `ZInQKernel.Contrib.OneProof.WeberField` and
Mathlib's `NumberTheory.ModularForms.LevelOne.DimensionFormula`; not `OneProof.Main`; no build-time code).
Scratch: `scratch/aftate-or/` (results log `log.md`). Nothing else under `ZInQKernel/` or `blueprint/` was edited.
Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a file of this tree. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number recalled without a source (no network on this host).

## 0. Result

**`r16CoreY` is discharged from the new leaf `AfTateOr.AfTateDSOr`, the existing LEAF `X1Igusa.IgusaGL2DS` and the
bundle's `mumfordTorsionAlgClosed`** (VERIFIED: compiled, standard axioms, `#discharges` recorded):

```lean
theorem AfTateOr.r16CoreY_of_dsOr_igusaDS (h : AfTateOr.AfTateDSOr) (hI : X1Igusa.IgusaGL2DS)
    (hM : AvSplit.MumfordTorsionAlgClosed) : R16Split.R16CoreY
```

`AfTateDSOr` answers the review's three objections to weber-field's `AfTateCharPolyPicZero`:

| objection | fix in `AfTateDSOr` |
|---|---|
| DS 9.5.4 may print only that Frobenius *satisfies* the polynomial | The conclusion is the disjunction **(characteristic polynomial) ∨ (satisfies ∧ odd)**. The two disjuncts are isj1-dict's `AfTateAt` and `AfTateWeakOddAt`, as definitional bodies: `orAt_of_afTateAt` and `orAt_of_weakOddAt` are bare `Or.inl` and `Or.inr`. The consumers' form is recovered from either disjunct (`weakOddAt_of_orAt`): Cayley–Hamilton, isj1-dict's `odd_of_charpoly`, then `component_charpoly` (ds965-weak's Chebotarev method on each `ι`-component). |
| the leaf is existential over models | The model is now **universal** over DS's own construction. `IsX1AlgDS N X` says `X` is a smooth proper geometrically connected curve over `ℚ` with function field `ℚ(j, f₁)`, where `f₁` is the kernel's Weber function `T5Glue.weber ⟨1, τ⟩ (1/N)`; the field is given by generators and relations. The leaf also asks for a rational point and is universal over all `Pic⁰` representatives. Only `A = A_f` stays existential (no Hecke correspondences on `J₁(N)` in Lean). |
| the `K_N` model clause needs a dictionary step | `IsX1AlgDS` is DS's definition of `X₁(N)_alg`, so no dictionary step is needed inside the leaf. The dictionary to the kernel's `IsX1Model` is **proved in both directions**: `isX1AlgDS_of_isX1Model` (uses weber-field's `weberFieldComparison` and Igusa) and `isX1Model_of_isX1AlgDS`. |

**Rating: `afTateDSOr` is a LEAF (printed form).** Under the characteristic-polynomial reading of DS 9.5.4 it is the
print, by or-introduction and transport along isomorphisms. Under the "satisfies" reading it is the print plus oddness
of `ρ_{A_f,ℓ}`. Oddness is a consequence of the printed determinant formula `det ρ_{A_f,ℓ} = χ χ_ℓ` for the same
`A_f` (Shimura 1971 Thm 7.14, Ribet 1977; numbers UNVERIFIED). §4 explains why oddness must come from the print: the
tree has no other source of it. It is never stronger than isj1-dict's leaves (`dsOr_of_picZero`,
`dsOr_of_weakPicZero`, proved).

**Fold** (VERIFIED, dry run): `strict count: 45/10 on 55 -> 47/9 on 56; strictest 43/12 -> 45/11`.
- `r16CoreY` (GLUE) is replaced by `afTateDSOr` and `igusaGL2DS`, both LEAF.
- The generated `HDec.HSyn.sixContactMin_of_open31` compiles with the standard axioms.
- The count is the same as weber-field's, whose spec flagged `afTateCharPolyPicZero` as `unread`, which counts as LEAF.
  Under the review's rating of that leaf (GLUE), weber-field's fold changed GLUE by 0 and this one changes it by −1.

## 1. Statements (all in namespace `AfTateOr`; VERIFIED, compiled)

```lean
def toQ : Polynomial (Polynomial ℤ) →+* Polynomial (Polynomial ℚ)          -- coefficients ℤ → ℚ
def ev2 {K} [CommRing K] (F : Polynomial (Polynomial ℤ)) (a b : K) : K   -- F(a, b)

def IsX1AlgDS (N : ℕ) (X : Over SpecQ) : Prop :=
  IsCurve X ∧ ∃ (_ : IsIntegral X.left) (jX tX : X.left.functionField),
    Subfield.closure {jX, tX} = ⊤ ∧
    ∀ F : Polynomial (Polynomial ℤ), ev2 F jX tX = 0 ↔
      ∀ τ : UpperHalfPlane, (T5Glue.pp τ).g₂ ≠ 0 → (T5Glue.pp τ).g₃ ≠ 0 →
        X1Igusa.Weber.evAn N (toQ F) τ = 0

def AfTateOrAt (N) (χ) (f : CF N 2) (J : AbVar ℚ) : Prop :=
  ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0), Surjective π.hom.left ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ b : (ℚ_ℓ ⊗ K_f)-basis (Fin 2) of V_ℓ(A),
      (∀ p, p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          ∃ c : coeffField f, (c : ℂ) = χ p ∧ (frobMat ℓ A θ b σ).charpoly = esPoly ℓ a_p (c * p)) ∨
      ((∀ emb c, IsComplexConj c → LinearMap.det (frobOn ℓ A θ emb c) = -1) ∧
       ∀ p, p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          ∃ c : coeffField f, (c : ℂ) = χ p ∧ aeval (frobMat ℓ A θ b σ) (esPoly ℓ a_p (c * p)) = 0)

def AfTateDSOr : Prop :=                                   -- LEAF
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 2 ≤ N → IsNewform f χ →
    ∀ X : Over SpecQ, IsX1AlgDS N X → Nonempty (RatPt X) →
      ∀ (V : AbelianVariety ℚ) (rep : (picardFunctorDegree X.hom 0).obj.RepresentableBy V.group.X),
        PicardTensorCompatible X.hom V.group rep → AfTateOrAt N χ f (R16IsJ1Dict.ofVendored V)
```

The exact text is in the Lean file. Points about each definition:
- **`IsX1AlgDS`.** A field generated by two elements is determined up to isomorphism by their ideal of relations
  (`nonempty_ringEquiv_of_rel`, proved). So `IsX1AlgDS N X` says exactly `K(X) ≅ ℚ(j, f₁)`.
  - Integer coefficients avoid a `ℚ`-algebra structure on `K(X)`. Characteristic 0 follows from the relations.
  - `j = 1728 g₂³/Δ` and `f₁ = g₂g₃℘_τ(1/N)/Δ` on Weber's generic branch (`T5Glue.weber`, `RingClassLattice.lean`
    l.74). Both are read from the tree (VERIFIED).
  - The property is the same for any normalization of `f₁` in `ℚ(j)^× f₁ + ℚ(j)`, since these generate the same field
    (argument).
- **`AfTateOrAt`.** Its two disjuncts are verbatim the bodies of isj1-dict's `AfTateAt` and `AfTateWeakOddAt`. The
  or-introductions type-check by passing the hypothesis through unchanged.
- **`AfTateDSOr`.**
  - The rational-point hypothesis only weakens the leaf: DS's `X₁(N)_alg` has the rational cusp `∞`. The consumer
    has a rational point from `IsJ1`. The point is used to prove that the leaf is never stronger.
  - `N = 1` is omitted because `S₂(Γ₁(1)) = 0`. The consumer handles `N = 1` by `not_isNewform_one`, from Mathlib's
    `ModularForm.levelOne_weight_two_rank_zero`.

## 2. Proofs (glue, all VERIFIED: compiled, axioms `[propext, Classical.choice, Quot.sound]`)

| theorem | content |
|---|---|
| `weakOddAt_of_orAt` | `TateModuleFree → 0 < N → IsNewform f χ → AfTateOrAt → AfTateWeakOddAt`. From the first disjunct: the relation by `Matrix.aeval_self_charpoly`, and oddness by `R16IsJ1Dict.odd_of_charpoly` (Chebotarev T18, `χ(−1) = 1`). The second disjunct is the weak-odd form itself. |
| `orAt_of_afTateAt`, `orAt_of_weakOddAt` | the two or-introductions |
| `map_ev2`, `evAlg_toQ` | ring maps commute with `ev2`; weber-field's `evAlg (toQ F) P = ev2 F j (w P)` |
| `closure_eq_top` | `ℚ(j)(w(P))` (`= fieldX1 P`, `adjoin_wOf`) is generated as a field by `j` and `w(P)`. The proof goes through `Subfield.toIntermediateField`, using that `RatFunc ℚ` is generated by `X`. |
| `isX1AlgDS_of_isX1Model` | `X1PointsConjugate → 2 ≤ N → IsX1Model N X → IsX1AlgDS N X`. The model's `K(X) ≅ ℚ(j)(x(P'))`; Igusa gives `≅ ℚ(j)(x(P))` for weber-field's `P`; `adjoin_wOf` gives `ℚ(j)(w(P))`. The generators are the images of `j` and `w(P)`. Their relations are those of `(j, f₁)` by `weberFieldComparison`. |
| `evHom`, `isFractionRing_range`, `nonempty_ringEquiv_of_rel` | if fields `K, L` are generated by `(a, b)` and `(c, d)` with the same integer relations, then `K ≃+* L`. Proof: `ℤ[a,b] ≅ ℤ[J,T]/I ≅ ℤ[c,d]`, then `IsFractionRing.of_field` with `Subfield.mem_closure_iff`, then `IsFractionRing.ringEquivOfRingEquiv`. |
| `isX1Model_of_isX1AlgDS` | `2 ≤ N → IsX1AlgDS N X → IsX1Model N X` (the converse dictionary, no Igusa) |
| `cuspForm_one_two_eq_zero`, `not_isNewform_one` | `S₂(Γ₁(1)) = 0`: `Γ₁(1) = SL₂(ℤ)`, so `CF 1 2` is `CuspForm 𝒮ℒ 2`; Mathlib's dimension formula kills it. Hence no newform of level 1. |
| `weakOdd_of_dsOr` | `AfTateDSOr → X1PointsConjugate → TateModuleFree → AfTateWeakOdd`. For `IsJ1 N J` from `(X, P₀)`: take `N ≥ 2`, `IsX1AlgDS` by the dictionary, `V = Pic⁰` (`exists_picZero`), the leaf at `(X, P₀, V)`, then `weakOddAt_of_orAt`, then transport to `J` along `abVarIso_picZero_of_isJacobian`. |
| `r16CoreY_of_dsOr_igusaDS` | the discharge: `R16IsJ1Dict.r16CoreY_of_weakOdd` with `x1PointsConjugate_of_igusaGL2DS`; `TateModuleFree` comes from `mumfordTorsionAlgClosed` |
| `dsOr_of_picZero`, `dsOr_of_weakPicZero` | `AfTateCharPolyPicZero → X1PointsConjugate → AfTateDSOr`, and the same from `AfTateWeakOddPicZero`. **The new leaf is never stronger than either of isj1-dict's leaves.** |
| `weakPicZero_of_dsOr` | `AfTateDSOr → X1PointsConjugate → TateModuleFree → X1ModelExists → AfTateWeakOddPicZero` (the converse) |

## 3. Checks (VERIFIED, 2026-11-16, one Lean process at a time)

| check | command | outcome |
|---|---|---|
| development file | `lake env lean scratch/aftate-or/AfTateOr.lean` | no errors |
| contribution | `lake build ZInQKernel.Contrib.OneProof.AfTateOr` | `Build completed successfully (11357 jobs)`; only the new module compiled (9.7 s). Build tree copied (reflink) from weber-field's worktree at the same commit. |
| `#discharges` | `lake env lean scratch/aftate-or/Discharges.lean` (output `Discharges-output.txt`) | `61 open hypotheses, 2647 theorems checked, 17 discharge one`; see below |
| fold dry run | `python3 scripts/one_proof/autofold.py scratch/aftate-or/autofold.json --dry-run`, line 1 stripped, `lake env lean scratch/aftate-or/FoldDryRun.lean` | **`strict count: 45/10 on 55 -> 47/9 on 56; strictest 43/12 -> 45/11`**; `HDec.HSyn.sixContactMin_of_open31` standard axioms (`FoldDryRun-output.txt`) |
| verbatim disjuncts | `orAt_of_afTateAt`, `orAt_of_weakOddAt` compile with the hypothesis passed through unchanged (`⟨b, Or.inl hcp⟩`, `⟨b, Or.inr ⟨hodd, hw⟩⟩`) | the disjuncts are isj1-dict's bodies |

```
DISCHARGES [OpenResearchLeaves23.r16CoreY] by AfTateOr.r16CoreY_of_dsOr_igusaDS
  still assumes: [AfTateOr.AfTateDSOr, X1Igusa.IgusaGL2DS, AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 61 open hypotheses, 2647 theorems checked, 17 discharge one
```

All ten `#print axioms` lines in `Discharges-output.txt` are standard. They cover the discharge, both dictionary
directions, `weakOddAt_of_orAt`, `not_isNewform_one`, the never-stronger theorems and `nonempty_ringEquiv_of_rel`.

## 4. Oddness: where it comes from (finding)

The task said to take oddness "from where the tree already has it". The tree has oddness of `ρ_{A_f,ℓ}` on
`ι`-components in two places only. Both are VERIFIED by grep of `ZInQKernel/`:
1. as a clause of isj1-dict's `AfTateWeakOdd*` leaves;
2. as the Lean consequence `R16IsJ1Dict.odd_of_charpoly` of the characteristic-polynomial form.

No bundle leaf gives it for the existential `A`:
- **`T12_ComplexConjEigen`** gives `g`-dimensional `±1`-eigenspaces of complex conjugation on all of `V_ℓ(A)`.
  - Let `s₊` and `s₋` be the numbers of scalar components with `ψ(c) = ±1`, and `n` the number of non-scalar
    components (which have `det = −1`). Counting dimensions gives `2s₊ + n = g = s₊ + s₋ + n`, so `s₊ = s₋`. Scalar
    components can occur in balanced pairs (argument, SPECULATIVE).
- **`FaltingsTate`/`FaltingsSemisimple`** exclude scalars only together with `End⁰(A) = K_f` (Ribet 1980), which is
  not in the tree.
- **`DSThm965`** (Deligne's `ρ_f`): a scalar component `ψ ⊕ ψ` forces `ι(a_p) = ψ(Frob_p) + χ(p)p/ψ(Frob_p)`, so
  `ρ_f^{ss} ≅ ψ ⊕ ε₀χ_ℓψ⁻¹`. That is excluded only by Ribet's irreducibility (1977), which is not in the tree.
- **`HodgeTateDecompAbVar`/`EigenformHTNew`**: going from Hodge–Tate weights to a contradiction needs Sen–Tate theory,
  class field theory for `ℚ` and Ramanujan. None of these is in the tree.
- **`CharPolyIndepOfEll`**: the root-multiset argument excludes scalars only when `N_{K_f/ℚ}(P_p)` is irreducible for
  some `p`, which fails for CM forms.

So under the "satisfies" reading the leaf needs oddness from the printed determinant formula, inside the same
existential: the witness is DS's `A_f` for both prints.

The disjunction keeps the cost confined to that reading. Under the characteristic-polynomial reading, the first
disjunct needs nothing more.

## 5. Leaf ratings

| leaf | Lean | printed form? | kind / flag | reason |
|---|---|---|---|---|
| `afTateDSOr` (new) | `AfTateOr.AfTateDSOr` | **yes** | published; flag `unread: new printed leaf …` (`scratch/aftate-or/autofold.json`) | See the four reasons below the table. |
| `igusaGL2DS` | `X1Igusa.IgusaGL2DS` | yes (x1-igusa §6) | published, unread | unchanged |

Reasons for rating `afTateDSOr` printed:
1. **Wording.** If DS 9.5.4 prints the characteristic polynomial, the first disjunct is the print (`Or.inl`). If it
   prints "satisfies", the second disjunct is the print plus oddness, and oddness is a consequence of the printed
   `det ρ_{A_f,ℓ} = χχ_ℓ` with `χ(−1) = 1` (UNVERIFIED locator).
2. **Model.** The model is universal over DS's own `X₁(N)_alg`. The curve is given by its function field `ℚ(j, f₁)`,
   and `f₁` is the kernel's Weber function. The transport from DS's one curve to any model with a rational point, and
   to any `Pic⁰` representative, is proved for kernel models: the curve is determined by its function field, and
   `Pic⁰` is the Albanese (`dsOr_of_picZero`).
3. **Dictionary.** No dictionary step remains inside the leaf. Both directions of the dictionary are proved.
4. **Remaining weakenings** (each makes the leaf weaker than the print, never stronger):
   - `A` is existential;
   - newforms only;
   - unramifiedness is dropped;
   - a rational point is assumed.

**Remaining objections** (readings, not glue):
- the DS 9.5.4 wording now only decides which disjunct the print supplies;
- the source of the determinant formula under the "satisfies" reading;
- the locators (UNVERIFIED, no network).

Proposed `locators.md` row (not added, since that file belongs to another task): `afTateDSOr` | DS GTM 228 §7.7,
Lemma 9.5.3, Thm 9.5.4; Shimura 1971 Thm 7.14 (det) | UNVERIFIED. Check whether 9.5.4 says "characteristic
polynomial" or "satisfies", and where `det ρ_{A_f,ℓ} = χχ_ℓ` is printed.

## 6. Files

- `ZInQKernel/Contrib/OneProof/AfTateOr.lean`: the contribution.
- `scratch/aftate-or/AfTateOr.lean`: the development version (the same declarations, without the module docstring).
- `scratch/aftate-or/Discharges.lean`, `Discharges-output.txt`: the `#discharges` check and the axiom prints.
- `scratch/aftate-or/autofold.json`, `FoldDryRun.lean`, `FoldDryRun-output.txt`: the fold spec and its dry run.
- `scratch/aftate-or/log.md`: the results log.
