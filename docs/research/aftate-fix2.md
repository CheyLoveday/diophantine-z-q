# aftate-fix2: `r16CoreY` from Diamond–Shurman's `A_f`, universally, over `K_{f,λ}`

Task aftate-fix2, branch `wip/aftate-fix2`, base `wip/aftate-or` 7378fd4e with `origin/main` (0caafe66) merged.
Date 2026-11-16. Lean: `ZInQKernel/Contrib/OneProof/AfTateLambda.lean` (new; imports
`ZInQKernel.Contrib.OneProof.AfTateOr` and Tau Ceti's `NumberTheory.NumberField.LocalGlobal.Completion`; not
`OneProof.Main`; no build-time code). Scratch: `scratch/aftate-fix2/` (results log `log.md`). Nothing else under
`ZInQKernel/` or `blueprint/` was edited. Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a file of this tree. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number recalled without a source (no network on this host).

## 0. Result

**`r16CoreY` is discharged from three new leaves over genuine definitions, the existing LEAF
`X1Igusa.IgusaGL2DS` and the bundle's `mumfordTorsionAlgClosed`** (VERIFIED: compiled, standard axioms):

```lean
theorem AfTateLam.r16CoreY_of_printed (h1 : AfTateLam.HeckeJ1DS) (h2 : AfTateLam.AfShimura)
    (h3 : AfTateLam.AfTateDSLambda) (hI : X1Igusa.IgusaGL2DS)
    (hM : AvSplit.MumfordTorsionAlgClosed) : R16Split.R16CoreY
```

| review objection to `AfTateOr.AfTateDSOr` | answer |
|---|---|
| (1) `A` existential | **Resolved.** `AfTateDSLambda` is universal over every `(A, π, θ)` that is Diamond–Shurman's `A_f = J₁(N)/I_f J₁(N)` with its `K_f`-action. The Hecke algebra is a Lean object: `T_p` and `⟨d⟩` are the endomorphisms of `J` with DS's double-coset action on divisor classes of the points `x_τ ∈ X(ℂ)` (`IsHeckeT`, `IsDiamond`, `AtTau`); `I_f` is the kernel of `T_p ↦ a_p(f)`, `⟨d⟩ ↦ χ(d)` (free algebra); `A_f` is the universal quotient killing `I_f J` (`IsAfQuotient`); `θ(a_p) = T_p|A_f`, `θ(χ(d)) = ⟨d⟩|A_f` (`IsAfAction`). Existence is two separate printed leaves: the Hecke operators over `ℚ` (`HeckeJ1DS`, DS §6.3/§7.9) and `A_f` over `ℚ` (`AfShimura`, Shimura 1973 Thm 1, read by the locator audit). The glue proves that this `A` satisfies everything the consumer needs: surjectivity is part of `IsAfQuotient`, `dim A = [K_f:ℚ]` follows from the rank two of every `ι`-component (`R16Split.dim_eq_of_rank_two`), trace and determinant follow from §6. |
| (2) "satisfies" reading needs `det ρ = χχ_ℓ` | **Not resolvable in the tree; recorded as a reading risk.** The leaf states the characteristic polynomial (no oddness clause, no determinant clause). Deriving `det ρ_{f,λ} = χχ_ℓ` from a "satisfies" form needs the Weil pairing on `V_ℓ(J₁(N))` and the adjointness `T_p* = ⟨p⟩⁻¹T_p`; the tree has no Weil pairing on abelian varieties (VERIFIED, grep). The consumer `R16CoreY` uses the determinant, so the clause cannot be dropped. See §4. |
| (3) `ℚ_ℓ ⊗ K_f` in place of `K_{f,λ}` | **Resolved.** `AfTateDSLambda` is stated over `K_{f,λ} = λ.adicCompletion K_f` (Mathlib) for every place `λ ∣ ℓ`, on `V_λ = K_{f,λ} ⊗_{ℚ_ℓ ⊗ K_f} V_ℓ(A)` with `ℚ_ℓ → K_{f,λ}` from Mathlib's `ℚ_ℓ ≅ ℚ_{v_ℓ}` and Tau Ceti's completion map. The glue from `K_{f,λ}` to the consumers' `ι`-components (`AfTateLam.component`) is proved by base change directly; it does not need the semi-local decomposition `ℚ_ℓ ⊗ K_f ≅ ∏ K_{f,λ}` (each `ι` factors through its own `K_{f,λ_ι}`). Conversely `dsLambda_of_tensor` proves the `K_{f,λ}` leaf from the `ℚ_ℓ ⊗ K_f` form `AfTateDSTensor` (base change of a basis), so the leaf follows from the print in either form (`ρ_{A_f,ℓ}` over `K_f ⊗ ℚ_ℓ` or `ρ_{f,λ}` over `K_{f,λ}`). The assembly `K_{f,λ}`-form ⇒ `ℚ_ℓ ⊗ K_f`-form (which needs Tau Ceti's `semilocalEquiv`) is not needed for either direction that matters here and was not formalized. |

**Ratings** (§5): `heckeJ1DS` and `afShimura` printed form; `afTateDSLambda` printed form under the
characteristic-polynomial reading of DS 9.5.4, flagged "reading risk" for the "satisfies" reading.

**Fold** (dry run, §3): `r16CoreY` (GLUE) is replaced by `heckeJ1DS`, `afShimura`, `afTateDSLambda` and
`igusaGL2DS`, all kind published: **`strict count: 34/11 on 45 -> 38/10 on 48; strictest 34/11 -> 38/10`** (GLUE −1);
the generated `HDec.HSyn.sixContactMin_of_open36` compiles with the standard axioms. If the review moves
`afTateDSLambda` from "reading risk" to "pending reading" (§4), the count is 37/11 (GLUE unchanged).

## 1. Statements (namespace `AfTateLam`; VERIFIED, compiled)

The full text, with docstrings, is in the Lean file. Summary:

- `IsX1Gen N X jX tX`: `K(X) = ℚ(j_X, t_X)` and the integer relations of `(j_X, t_X)` are those of
  `(j(τ), f₁(τ))` on `ℍ` (the body of aftate-or's `IsX1AlgDS` with the generators named).
- `RegAt x g c`: the rational function `g ∈ K(X)` is the germ of a section `s` over an open `U` with
  `x ∈ U(ℂ)`, and `s(x) = c`.
- `AtTau N jX tX x τ` (`x = x_τ`): every `g = P(j_X,t_X)/Q(j_X,t_X)` whose meromorphic function
  `P(j,f₁)/Q(j,f₁)` has a limit `c` at `τ` (punctured neighbourhood) is regular at `x` with value `c`.
  Exactly one complex point satisfies this for each `τ` (the uniformization is holomorphic and non-constant,
  and the rational functions regular at a point determine it; argument, not formalized).
- `IsHeckeT N jX tX aj p t`: for all `τ, τ'` and the points `x_τ, x_{τ'}, x_{(τ+j)/p}, x_{(τ'+j)/p}` (and
  `x_{g(pτ)}, x_{g(pτ')}` for `p ∤ N`, `g = (a b; c d) ∈ SL₂(ℤ)`, `N ∣ c`, `d ≡ p mod N`):
  `t(aj x_τ − aj x_{τ'}) = Σ_j (aj x_{(τ+j)/p} − aj x_{(τ'+j)/p}) [+ (aj x_{g(pτ)} − aj x_{g(pτ')})]` in
  `J(ℂ)`. This is DS §6.3's `T_p` on `Pic⁰` through Abel–Jacobi, with the coset representatives of DS
  Prop. 5.2.1.
- `IsDiamond N jX tX aj d δ`: `δ(aj x_τ − aj x_{τ'}) = aj x_{gτ} − aj x_{gτ'}` for `g ∈ Γ₀(N)` with lower
  right entry `≡ d`.
- `evF χ f : FreeAlgebra ℤ (Nat.Primes ⊕ (ZMod N)ˣ) →ₐ ℂ` (`T_p ↦ a_p`, `⟨d⟩ ↦ χ(d)`), `heckeJ tp δ` (the
  same generators into `End J`), `KillsIf φ` (`φ ∘ h_J = 0` for `h ∈ ker evF`), `IsAfQuotient` (surjective,
  kills `I_f J`, universal among homomorphisms to abelian varieties killing `I_f J`), `IsAfAction`.
- `vQ ℓ`, `algQl ℓ λ : ℚ_ℓ → K_λ`, `rhoLam ℓ λ : ℚ_ℓ ⊗ K → K_λ`, `galR` (`σ` as a `ℚ_ℓ ⊗ K`-linear map of
  `V_ℓ(A)`), `frobLam ℓ A θ λ σ` (`ρ_{f,λ}(σ)` on `V_λ`).

```lean
def HeckeJ1DS : Prop :=     -- LEAF
  ∀ N, 2 ≤ N → ∀ X [IsIntegral X.left] jX tX, IsCurve X → IsX1Gen N X jX tX →
    ∀ P₀ J aj, IsJacobian X P₀ J aj →
      ∃ tp δ, (∀ p : Nat.Primes, IsHeckeT N jX tX aj p (tp p)) ∧ (∀ d, IsDiamond N jX tX aj d (δ d))

def AfShimura : Prop :=     -- LEAF
  ∀ N χ (f : CF N 2), 2 ≤ N → IsNewform f χ → ∀ X [IsIntegral X.left] jX tX, IsCurve X → IsX1Gen N X jX tX →
    ∀ P₀ J aj, IsJacobian X P₀ J aj → ∀ tp δ, (Hecke) → (diamond) →
      FiniteDimensional ℚ (coeffField f) ∧
        ∃ A π θ, IsAfQuotient χ f tp δ A π ∧ IsAfAction χ f tp δ π θ

def AfTateDSLambda : Prop := -- LEAF
  ∀ N χ f, 2 ≤ N → IsNewform f χ → ∀ X [IsIntegral X.left] jX tX, IsCurve X → IsX1Gen N X jX tX →
    ∀ P₀ J aj, IsJacobian X P₀ J aj → ∀ tp δ, (Hecke) → (diamond) →
    ∀ A π θ, IsAfQuotient χ f tp δ A π → IsAfAction χ f tp δ π θ →
    ∀ [NumberField (coeffField f)] ℓ [Fact ℓ.Prime] (λ : HeightOneSpectrum (𝓞 K_f)) [λ ∣ ℓ],
      ∀ [Module.Finite K_λ V_λ], ∀ p, p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
        ∃ c : K_f, (c : ℂ) = χ p ∧ (frobLam ℓ A θ λ σ).charpoly = X² − a_p X + c p   -- over K_λ
```

## 2. Glue (all VERIFIED: compiled, axioms `[propext, Classical.choice, Quot.sound]`)

| theorem | content |
|---|---|
| §0 `finrank_E`, `toMatrix_precomp`, `trace_det_precomp` | Generic. `R` a commutative `k`-algebra acting on `V`, `L` a field with `R → L`, `ε : L → Ω`, `E` the `k`-linear functionals `V → Ω` semilinear along `ε ∘ (R → L)`. A basis `1 ⊗ v_i` of `L ⊗_R V` gives the dual basis `φ_j = ε ∘ b_j^* ∘ (1 ⊗ –)` of `E` (every semilinear functional factors through `L ⊗_R V`, `liftφ`); precomposition by an `R`-linear `g` has matrix `ε(M_{g_L})ᵀ`, so `dim E = dim_L(L ⊗_R V)`, `tr = ε(tr g_L)`, `det = ε(det g_L)`. |
| §0b (copied from coeff-ext's `DSCoeffExt.lean`, §§2–4) | `place ι = {a ∈ 𝓞_K : ‖ι a‖ < 1}`, `τhat ι : K_{λ_ι} → ℚ̄_ℓ` continuous extending `ι`. |
| `liesOver_place` | `λ_ι ∣ ℓ`: `comap λ_ι` is the height-one prime of `𝓞_ℚ` with `natGenerator = ℓ`. |
| `τhat_algQl` | `ι̂ ∘ (ℚ_ℓ → K_λ)` is the structure map `ℚ_ℓ → ℚ̄_ℓ` (both continuous, equal on the dense `ℚ`). |
| `τhat_rhoLam`, `mem_eigenFun_iff_semilin`, `isScalarTower_tensor` | `ι̂ ∘ rhoLam = liftHom ι`; the kernel's `eigenFun ℓ A θ ι` is exactly `E` for `R = ℚ_ℓ ⊗ K`. |
| `component` | the kernel's `ι`-component: `V_λ` finite, `dim eigenFun = dim_{K_λ} V_λ`, `tr frobOn σ = ι̂(tr ρ_{f,λ}(σ))`, `det frobOn σ = ι̂(det ρ_{f,λ}(σ))`. |
| `lin_trace_det` | `charpoly g = X² − tX + d` gives `dim = 2`, `tr g = t`, `det g = d`. |
| `exists_frob` | a Frobenius element at a prime not dividing `S` (Chebotarev, `ZInQ.Contrib.frobeniusDense`, proved). |
| `charpoly_frobLam_of_basis`, `dsLambda_of_tensor` | a `ℚ_ℓ ⊗ K_f`-basis `b` with `charpoly(frobMat b σ) = X² − (1⊗a)X + (1⊗d)` gives `charpoly ρ_{f,λ}(σ) = X² − aX + d` over `K_λ` (`LinearMap.toMatrix_baseChange`, `Matrix.charpoly_map`); hence `AfTateDSTensor → AfTateDSLambda`. |
| `r16CoreY_of_printed` | `N = 1` by aftate-or's `not_isNewform_one`; for `N ≥ 2`, aftate-or's dictionary `isX1AlgDS_of_isX1Model` (with Igusa) gives `IsX1Gen`; L1 gives the Hecke operators, L2 gives `K_f` finite and `(A, π, θ)`; for each `ℓ, ι`, L3 at `λ_ι` with `component` and `lin_trace_det` gives trace `ι(a_p)` and determinant `ι(χ(p))p` on the `ι`-component and its rank 2 (at one Frobenius from `exists_frob`); `dim A = [K_f:ℚ]` from `R16Split.dim_eq_of_rank_two`. `TateModuleFree` from `mumfordTorsionAlgClosed`. |

## 3. Checks (VERIFIED, 2026-11-16, one Lean process at a time)

| check | command | outcome |
|---|---|---|
| development file | `lake env lean scratch/aftate-fix2/AfTateLambda.lean` | no errors (16 s) |
| target copy | `lake env lean scratch/aftate-fix2/Target.lean` | verbatim copy of `R16Split.R16CoreY`, `copy_iff : … ↔ R16Split.R16CoreY := Iff.rfl`, discharge at the copy, standard axioms |
| contribution, Main, Discharges | `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.AfTateLambda` | `Build completed successfully (13704 jobs)`; `AfTateLambda` built in 16 s; `frozenTarget` standard axioms |
| `#discharges` | `lake env lean scratch/aftate-fix2/Discharges.lean` (output `Discharges-output.txt`) | see below |
| fold dry run | `python3 scripts/one_proof/autofold.py scratch/aftate-fix2/autofold.json --dry-run`, line 1 stripped, `lake env lean scratch/aftate-fix2/FoldDryRun.lean` | `strict count: 34/11 on 45 -> 38/10 on 48; strictest 34/11 -> 38/10`; `'HDec.HSyn.sixContactMin_of_open36' depends on axioms: [propext, Classical.choice, Quot.sound]` |
| build-time code | `grep -n "#eval\|run_cmd\|initialize\|^syntax\|^notation\|^macro\|elab \|sorry\|^axiom"` on the contribution | only the docstring line "No `sorry`, no `axiom`, no build-time code" |

```
DISCHARGES [OpenResearchLeaves26.r16CoreY] by AfTateLam.r16CoreY_of_printed
  still assumes: [AfTateLam.HeckeJ1DS,
 AfTateLam.AfShimura,
 AfTateLam.AfTateDSLambda,
 X1Igusa.IgusaGL2DS,
 AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 56 open hypotheses, 3382 theorems checked, 18 discharge one
```

The nine `#print axioms` lines (`r16CoreY_of_printed`, `component`, `trace_det_precomp`, `finrank_E`,
`liesOver_place`, `τhat_algQl`, `lin_trace_det`, `exists_frob`, `dsLambda_of_tensor`) are all `[propext, Classical.choice, Quot.sound]`.

## 4. The determinant (objection 2): finding

What `R16CoreY` needs from each `ι`-component is the trace **and** the determinant of every Frobenius at
`p ∤ Nℓ`, i.e. the characteristic polynomial. `AfTateDSLambda` states the characteristic polynomial of
`ρ_{f,λ}(Frob)` over `K_{f,λ}`, with no oddness clause and no separate determinant clause.

- **Characteristic-polynomial reading of DS 9.5.4** (the print says "the characteristic equation of
  `ρ(Frob_𝔭)` is `x² − a_p x + χ(p)p = 0`"): the leaf is the print at DS's objects (over `K_{f,λ}`, for every
  `A_f`; unramifiedness dropped, newforms only, both weakenings).
- **"Satisfies" reading** (the print says only that `ρ(Frob_𝔭)` satisfies the polynomial): on a 2-dimensional
  `V_λ` this excludes only the case that `ρ(Frob_𝔭)` is a scalar root of the polynomial. Excluding it needs
  `det ρ_{f,λ} = χ χ_ℓ` (then Chebotarev and `χ(−1) = 1`, as isj1-dict's `component_charpoly` does). The review
  notes that DS may give the determinant only as Exercise 9.6.3(b) (not checked here: no copy of DS on this host).
  - *Derive it in Lean from the Weil pairing* (the review's option): not possible in the tree. It needs the
    `e_ℓ`-pairing on `V_ℓ(J₁(N))`, its Galois equivariance with `χ_ℓ`, and `T_p* = ⟨p⟩⁻¹ T_p` for the pairing
    (DS §6.3/§9.5, UNVERIFIED). `grep -rli "weil pairing\|weilPairing"` over `ZInQKernel/` finds only Tau Ceti
    elliptic-curve files and unrelated hits; there is no pairing on `PkgI3.AbVar` (VERIFIED).
  - *Drop the determinant clause where the consumers do not use it*: the consumer `R16CoreY` (a fixed bundle
    field) states `det(frobOn σ) = ι(c)p`, so it cannot be dropped.
  - *Bundle oddness into a second disjunct* (aftate-or's choice): the review rejected this unless the
    determinant is printed in 9.5.4, so it was not repeated.

So the reading risk is unchanged by this task and is now isolated in one flag: `afTateDSLambda` is kind
published with flag class **reading risk** (counts LEAF, as `raynaudSemistableSH`), and a statement check of
DS 9.5.4 decides it. If the check finds "satisfies", the alternative sources for the characteristic polynomial
of Frobenius on `V_λ(A_f)` are Shimura 1971 Thm 7.14 (UNVERIFIED) and Ribet, LNM 601 (1977), §1–2 (trace
`a_p` and determinant `χ(p)p` for `ρ_λ` realized on `A_f` for `k = 2`, UNVERIFIED). The leaf text needs no
change for either source.

## 5. Leaf ratings

| leaf | Lean | printed form? | kind / flag | reason |
|---|---|---|---|---|
| `heckeJ1DS` (new) | `AfTateLam.HeckeJ1DS` | **yes** | published; flag `unread: …` | The existence over `ℚ` of DS's `T_p` and `⟨d⟩` on `J₁(N) = Pic⁰(X₁(N))` (DS §6.3 defines them on `Div⁰`/`Pic⁰` by the double cosets, §7.9 shows they are defined over `ℚ`). The divisor action is DS's (coset representatives of DS Prop. 5.2.1), read through Abel–Jacobi `[x] − [x'] ↦ aj(x)/aj(x')`. Quantified over every model, every choice of generators `(j_X, t_X)` with the relations of `(j, f₁)` (any two such triples are isomorphic by `nonempty_ringEquiv_of_rel` and a curve is determined by its function field, so they all are DS's `(X₁(N), j, f₁)`), every rational base point and every Jacobian. Not stronger: the conditions determine `T_p` and `⟨d⟩` uniquely (an endomorphism over `ℚ` is determined on `J(ℂ)`, which is generated by the classes `[x_τ] − [x_{τ'}]`). |
| `afShimura` (new) | `AfTateLam.AfShimura` | **yes** | published; flag `unread: …` | Shimura 1973 Thm 1, read by the locator audit (row R16: the `ℚ`-rational quotient `A_f`, the coefficient-field action, `[K_f:ℚ] = dim A_f`). `IsAfQuotient` writes "quotient of `J` by `I_f J`" as the universal property, which `J/I_f J` has (the quotient of an abelian variety by an abelian subvariety is the cokernel among abelian varieties; STANDARD). `I_f` is the image of the kernel of `T_p ↦ a_p`, `⟨d⟩ ↦ χ(d)` (DS's `I_f = Ann_{𝕋_ℤ}(f)`, since `f` is an eigenvector with these eigenvalues). `θ` is DS Prop. 6.6.4's action. Weakening: newforms only, `N ≥ 2`. |
| `afTateDSLambda` (new) | `AfTateLam.AfTateDSLambda` | **yes under the characteristic-polynomial reading** of DS 9.5.4 | published; flag **reading risk** (§4) | A consequence of the print whether DS states it for `ρ_{A_f,ℓ}` over `K_f ⊗ ℚ_ℓ` (`dsLambda_of_tensor`, proved) or for `ρ_{f,λ}` over `K_{f,λ}` (directly). DS Thm 9.5.4 over `K_{f,λ}` (DS's `ρ_{f,λ}` is `V_ℓ(A_f)` decomposed along `K_f ⊗ ℚ_ℓ = ∏ K_{f,λ}`; `K_{f,λ} ⊗_{ℚ_ℓ⊗K_f} V_ℓ(A_f)` is that factor), **universal over every `A_f`**. Weakenings: newforms only, unramifiedness dropped, `V_λ` finite assumed (instance argument). `K_f` a number field is an instance argument (the print's presupposition). |
| `igusaGL2DS` | `X1Igusa.IgusaGL2DS` | yes (x1-igusa §6) | published, unread | unchanged; used only for aftate-or's dictionary `IsX1Model → IsX1AlgDS` |

**Why the definitions are genuine.** Every notion is spelled out over Mathlib and kernel objects: `X(ℂ)` and
regular functions (sections over opens and `ΓSpecIso`), the uniformization through `K(X) = ℚ(j, f₁)` (aftate-or's
relation data with the kernel's Weber function), `J(ℂ)` with its group law (morphisms into the group object), the
free algebra and `evF`, abelian-variety homomorphisms, Mathlib's `adicCompletion`, Tau Ceti's completion map,
the kernel's `V_ℓ(A)` and Galois action. No structure was introduced for the purpose. The only universally
quantified data that a reader must check against DS are the double-coset formulas in `IsHeckeT` and
`IsDiamond`.

Proposed `locators.md` rows (not added; another task's file):
- `heckeJ1DS` | Diamond–Shurman GTM 228 §6.3 (Hecke on `Div⁰`, `Pic⁰`), Prop. 5.2.1 (cosets), §7.9 (over `ℚ`); Shimura 1971 §7.2 | UNVERIFIED.
- `afShimura` | Shimura, J. Math. Soc. Japan 25 (1973) Thm 1, pp. 526–527 (audit row R16) | read by the audit for the quotient/action/dimension clauses.
- `afTateDSLambda` | Diamond–Shurman Lemma 9.5.3, Thm 9.5.4; Shimura 1971 Thm 7.14; Ribet 1977 | UNVERIFIED; check "characteristic equation" vs "satisfies".

## 6. Files

- `ZInQKernel/Contrib/OneProof/AfTateLambda.lean`: the contribution.
- `scratch/aftate-fix2/AfTateLambda.lean`: the development copy (identical).
- `scratch/aftate-fix2/BaseChange.lean`, `Defs.lean`: earlier development pieces (`BaseChange.lean` compiles against
  plain Mathlib).
- `scratch/aftate-fix2/Discharges.lean`, `Discharges-output.txt`: `#discharges` and the axiom prints.
- `scratch/aftate-fix2/autofold.json`, `FoldDryRun.lean`, `FoldDryRun-output.txt`: the fold spec and its dry run.
- `scratch/aftate-fix2/log.md`: the results log; `chk.sh`: the compile wrapper.
