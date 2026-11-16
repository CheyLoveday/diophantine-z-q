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
| (3) `ℚ_ℓ ⊗ K_f` in place of `K_{f,λ}` | **Resolved.** `AfTateDSLambda` is stated over `K_{f,λ} = λ.adicCompletion K_f` (Mathlib) for every place `λ ∣ ℓ`, on `V_λ = K_{f,λ} ⊗_{ℚ_ℓ ⊗ K_f} V_ℓ(A)` with `ℚ_ℓ → K_{f,λ}` from Mathlib's `ℚ_ℓ ≅ ℚ_{v_ℓ}` and Tau Ceti's completion map. The glue from `K_{f,λ}` to the consumers' `ι`-components (`AfTateLam.component`) is proved by base change directly; it does not need the semi-local decomposition `ℚ_ℓ ⊗ K_f ≅ ∏ K_{f,λ}` (each `ι` factors through its own `K_{f,λ_ι}`). |

**Ratings** (§5): `heckeJ1DS` and `afShimura` printed form; `afTateDSLambda` printed form under the
characteristic-polynomial reading of DS 9.5.4, flagged "reading risk" for the "satisfies" reading.

**Fold** (dry run, §3): `r16CoreY` (GLUE) is replaced by `heckeJ1DS`, `afShimura`, `afTateDSLambda` and
`igusaGL2DS`, all kind published. [dry-run line pending]

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
| `r16CoreY_of_printed` | `N = 1` by aftate-or's `not_isNewform_one`; for `N ≥ 2`, aftate-or's dictionary `isX1AlgDS_of_isX1Model` (with Igusa) gives `IsX1Gen`; L1 gives the Hecke operators, L2 gives `K_f` finite and `(A, π, θ)`; for each `ℓ, ι`, L3 at `λ_ι` with `component` and `lin_trace_det` gives trace `ι(a_p)` and determinant `ι(χ(p))p` on the `ι`-component and its rank 2 (at one Frobenius from `exists_frob`); `dim A = [K_f:ℚ]` from `R16Split.dim_eq_of_rank_two`. `TateModuleFree` from `mumfordTorsionAlgClosed`. |

## 3. Checks (VERIFIED, 2026-11-16, one Lean process at a time)

[pending]

## 4. The determinant (objection 2): finding

[pending]

## 5. Leaf ratings

[pending]

## 6. Files

- `ZInQKernel/Contrib/OneProof/AfTateLambda.lean`: the contribution.
- `scratch/aftate-fix2/AfTateLambda.lean`: the development copy (identical).
- `scratch/aftate-fix2/BaseChange.lean`, `Defs.lean`: earlier development pieces (`BaseChange.lean` compiles against
  plain Mathlib).
- `scratch/aftate-fix2/Discharges.lean`, `Discharges-output.txt`: `#discharges` and the axiom prints.
- `scratch/aftate-fix2/autofold.json`, `FoldDryRun.lean`, `FoldDryRun-output.txt`: the fold spec and its dry run.
- `scratch/aftate-fix2/log.md`: the results log; `chk.sh`: the compile wrapper.
