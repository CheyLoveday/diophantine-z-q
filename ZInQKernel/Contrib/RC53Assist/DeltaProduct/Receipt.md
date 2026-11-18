# Formal discriminant and differential normalization: verification receipt

## Scope and verification

- Base supplied for this contribution: `3b0ffbb9c83eaccb0f82808d806a4939205665b1`.
- Both final proof files passed the prescribed single-file Lean checks.
- Both scratch audit drivers passed with exit status 0. They contain exact copies of the corresponding final proof source followed by statement and axiom inspection commands.
- All 35 new theorems have exactly the axiom list `[propext, Classical.choice, Quot.sound]`. The period theorem and the existence-of-lattice theorem were inspected separately with the same result.
- Source inspection found no forbidden proof constructs, no new notation or syntax declarations, and no inspection commands in the final proof files. Every named declaration has a kind-labelled docstring and locators. The heartbeat bound is 800000.
- No existing source files were changed. No commits, checkout changes, or repository-wide compilation were performed. No independent review was performed.

## Files

- `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean`
  - Size: 25231 bytes
  - SHA256: `dc31d96bbaafdd3b1284605acb7dc7c2c832ee595fee4077bd6084b8ca557b84`
- `ZInQKernel/Contrib/RC53Assist/DeltaProduct/AnalyticMatching.lean`
  - Size: 10474 bytes
  - SHA256: `fb05b5c408f40eebf6f68f7d5fd5d430d47729a202f704b76c1e260a899088ee`
- `ZInQKernel/Contrib/RC53Assist/DeltaProduct/Scratch/FormalProductAudit.lean`
  - Size: 29087 bytes
  - SHA256: `63f097c5aa8cc5ea173c36a561f0b41691cce10474f590ea561ab45ae7a7d903`
- `ZInQKernel/Contrib/RC53Assist/DeltaProduct/Scratch/AnalyticMatchingAudit.lean`
  - Size: 12024 bytes
  - SHA256: `66179bdfa75a920fe1e1e99b9530da631e6c1b15e64bdf7b2f29c73194cf78b9`
- `ZInQKernel/Contrib/RC53Assist/DeltaProduct/Scratch/MakeReceipt.py`
  - Size: 8351 bytes
  - SHA256: `7267ecb72f6599575706f5144890c196190d0be8343222583e4b4de24645c467`

## What is proved of S1 and S3

### S1: formal product and concrete function-field presentation

The literal product identity is proved in both rational and integral formal power series. In rational coefficients, multiplication by `PowerSeries.C (1 / 1728)` is the precise interpretation of division by 1728. The integer identity has the factor 1728 on the right-hand side.

The proof first identifies the complex coefficient extension of the integral Euler product with the Taylor series of the analytic Euler product on the open unit disc. It then uses the proved analytic discriminant identity `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq_graded` and the existing Eisenstein coefficient identifications. No discriminant identity or equivalent conclusion is supplied as a hypothesis.

The Eisenstein-defined `jInvariantQ` is proved equal to `jProductQ`, which is the expanded integer-product expression used for the modular-curve library's `jq`. Consequently the concrete field `modularFunctionFieldQ M` is proved equal to `IntermediateField.adjoin ℚ {jProductQ, qPow M jProductQ}`.

The existing original module `Definitions/Def_ModularCurve_X0.lean` had no compiled object in the supplied environment. Its definitions were read, but it was not compiled, as required by the restriction on existing modules. The field comparison is therefore checked against its expanded product presentation, not against an import of the original qualified constant `ModularCurve.modularFunctionField`. A qualified-name bridge remains to be checked when that module's compiled object is supplied.

### S3: differential normalization and exact weak Weil data

For given convergent Laurent expansions, the formal condition `PullbackIsMultiple A x y ĝ c` is proved equivalent to the analytic identity `X' = 2πi c G (2Y + a₁X + a₃)`. The specialization to a cusp form uses the height `max R 0`.

For a nonconstant rational modular point at the exact level `newformLevel E`, the prescribed elliptic-curve coefficients and formal pullback identity imply the existing exact proposition `HasWeakWeilParametrization E`. The scalar is proved rational and nonzero; the lattice is obtained from the existing proved existence theorem; and period inclusion is obtained from the existing proved parametrization-periods theorem. Neither rationality of the scalar nor period inclusion is an extra hypothesis. There is also a version starting from the analytic derivative identity.

## What remains precisely

1. A scheme X₀(M) over ℚ, its smooth projective curve structure, and an identification of its function field and cusp q-expansion with the concrete field ℚ(j, j_M) and the existing rational cusp place.
2. The passage from the concrete function-field embedding of a nonconstant modular point to a scheme morphism X₀(M) → E, with extension across all points and the intended cusp normalization.
3. The converse algebraization of arbitrary `HasWeakWeilParametrization` data into a rational modular point or a rational scheme morphism. In particular, meromorphic Γ₀(M)-invariance by itself is not used as a substitute for proven membership in ℚ(j, j_M).
4. The qualified-name bridge to the original modular-curve module once its compiled object is available. The formal product identity itself has no remaining mathematical input.
5. Producing the required rational modular point from modularity, and integration into a larger theorem assembly, are not done by these translation theorems.

## Bibliographic status

Serre, *A Course in Arithmetic*, VII §4, is not manuscript-cited in the bibliography inspected in `diophantine_zq.tex`, lines 11009–11247. The entries `serrelocal` and `serre` concern local class field theory and the 1972 Galois-representation paper, respectively. The present formal product proof does not require a Serre leaf or any newly postulated standard fact.

## Exact theorem signatures and axiom inspection

All declarations below are in the namespace `ZInQ.Contrib.RC53Assist.DeltaProduct`. Signatures are copied verbatim from the final source, before the proof term. Imports and open namespaces are those in the corresponding source file. Axiom outputs below normalize line wrapping only; the axiom names and their order are those obtained by the completed scratch inspection commands.

### FormalProduct.lean

#### `iteratedDeriv_polynomial`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:66`

```lean
theorem iteratedDeriv_polynomial (n : ℕ) (p : Polynomial ℂ) :
    iteratedDeriv n (fun q => p.eval q) =
      fun q => ((Polynomial.derivative : Polynomial ℂ → Polynomial ℂ)^[n] p).eval q
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.iteratedDeriv_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `taylorZero_polynomial`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:82`

```lean
theorem taylorZero_polynomial (p : Polynomial ℂ) :
    taylorZero (fun q => p.eval q) = (p : PowerSeries ℂ)
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.taylorZero_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `polynomial_limit_taylor`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:94`

```lean
theorem polynomial_limit_taylor {ι : Type*} {l : Filter ι}
    {p : ι → Polynomial ℂ} {f : ℂ → ℂ} {s : Set ℂ}
    (h : TendstoLocallyUniformlyOn (fun i q => (p i).eval q) f l s)
    (hs : IsOpen s) (h0 : (0 : ℂ) ∈ s) (n : ℕ) :
    Tendsto (fun i => PowerSeries.coeff n (p i : PowerSeries ℂ)) l
      (𝓝 (PowerSeries.coeff n (taylorZero f)))
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.polynomial_limit_taylor' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `taylorZero_etaProduct`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:124`

```lean
theorem taylorZero_etaProduct :
    taylorZero (fun q : ℂ => ∏' n : ℕ, (1 - q ^ (n + 1))) =
      etaProductZ.map (Int.castRingHom ℂ)
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.taylorZero_etaProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `taylorZero_congr`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:159`

```lean
theorem taylorZero_congr {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 (0 : ℂ)] g) :
    taylorZero f = taylorZero g
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.taylorZero_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `taylorZero_mul`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:167`

```lean
theorem taylorZero_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorZero (f * g) = taylorZero f * taylorZero g
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.taylorZero_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `taylorZero_one`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:179`

```lean
theorem taylorZero_one : taylorZero (fun _ : ℂ => (1 : ℂ)) = 1
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.taylorZero_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `taylorZero_id`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:189`

```lean
theorem taylorZero_id : taylorZero (fun q : ℂ => q) = PowerSeries.X
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.taylorZero_id' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `taylorZero_pow`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:198`

```lean
theorem taylorZero_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    taylorZero (fun q => f q ^ n) = taylorZero f ^ n
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.taylorZero_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `qExpansion_discriminant_product`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:213`

```lean
theorem qExpansion_discriminant_product :
    UpperHalfPlane.qExpansion 1 ModularForm.discriminant =
      deltaProductZ.map (Int.castRingHom ℂ)
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.qExpansion_discriminant_product' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `qExpansion_E4Q`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:239`

```lean
theorem qExpansion_E4Q : UpperHalfPlane.qExpansion 1 ModularForm.E₄ =
    eisensteinE4Q.map (algebraMap ℚ ℂ)
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.qExpansion_E4Q' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `qExpansion_E6Q`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:247`

```lean
theorem qExpansion_E6Q : UpperHalfPlane.qExpansion 1 ModularForm.E₆ =
    eisensteinE6Q.map (algebraMap ℚ ℂ)
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.qExpansion_E6Q' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `map_deltaProductQ_complex`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:255`

```lean
theorem map_deltaProductQ_complex : deltaProductQ.map (algebraMap ℚ ℂ) =
    deltaProductZ.map (Int.castRingHom ℂ)
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.map_deltaProductQ_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `formal_delta_identity_Q`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:264`

```lean
theorem formal_delta_identity_Q : eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2 =
    1728 * deltaProductQ
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.formal_delta_identity_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `etaProductZ_map_rat`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:285`

```lean
theorem etaProductZ_map_rat : etaProductZ.map (Int.castRingHom ℚ) =
    ∏' n : ℕ, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (n + 1))
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.etaProductZ_map_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `deltaProductQ_eq_product`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:302`

```lean
theorem deltaProductQ_eq_product : deltaProductQ = PowerSeries.X *
    (∏' n : ℕ, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (n + 1))) ^ 24
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.deltaProductQ_eq_product' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `formal_delta_product_identity_Q`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:309`

```lean
theorem formal_delta_product_identity_Q : eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2 =
    1728 * PowerSeries.X *
      (∏' n : ℕ, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (n + 1))) ^ 24
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.formal_delta_product_identity_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `formal_delta_normalized_Q`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:318`

```lean
theorem formal_delta_normalized_Q :
    PowerSeries.C (1 / 1728 : ℚ) * (eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2) =
      PowerSeries.X * (∏' n : ℕ, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (n + 1))) ^ 24
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.formal_delta_normalized_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `map_eisenstein4Z_rat`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:340`

```lean
theorem map_eisenstein4Z_rat : eisenstein4Z.map (Int.castRingHom ℚ) = eisensteinE4Q
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.map_eisenstein4Z_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `map_eisenstein6Z_rat`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:355`

```lean
theorem map_eisenstein6Z_rat : eisenstein6Z.map (Int.castRingHom ℚ) = eisensteinE6Q
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.map_eisenstein6Z_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `formal_delta_identity_Z`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:370`

```lean
theorem formal_delta_identity_Z : eisenstein4Z ^ 3 - eisenstein6Z ^ 2 =
    1728 * deltaProductZ
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.formal_delta_identity_Z' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `formal_delta_product_identity_Z`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:378`

```lean
theorem formal_delta_product_identity_Z : eisenstein4Z ^ 3 - eisenstein6Z ^ 2 =
    1728 * PowerSeries.X *
      (∏' n : ℕ, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (n + 1))) ^ 24
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.formal_delta_product_identity_Z' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `constantCoeff_etaProductZ`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:387`

```lean
theorem constantCoeff_etaProductZ : PowerSeries.constantCoeff etaProductZ = 1
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.constantCoeff_etaProductZ' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `jInvariantQ_eq_product`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:408`

```lean
theorem jInvariantQ_eq_product : jInvariantQ = jProductQ
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.jInvariantQ_eq_product' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `modularFunctionFieldQ_eq_product_field`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:460`

```lean
theorem modularFunctionFieldQ_eq_product_field (M : ℕ) [NeZero M] :
    modularFunctionFieldQ M =
      IntermediateField.adjoin ℚ {jProductQ, qPow M jProductQ}
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.modularFunctionFieldQ_eq_product_field' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `formal_delta_product_Q`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:468`

```lean
theorem formal_delta_product_Q :
    PowerSeries.C (1 / 1728 : ℚ) * (eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2) =
      PowerSeries.X * ∏' n : ℕ, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)) ^ 24
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.formal_delta_product_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `formal_delta_product_Z`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/FormalProduct.lean:477`

```lean
theorem formal_delta_product_Z : eisenstein4Z ^ 3 - eisenstein6Z ^ 2 =
    1728 * PowerSeries.X *
      ∏' n : ℕ, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (n + 1)) ^ 24
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.formal_delta_product_Z' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### AnalyticMatching.lean

#### `hasQExpansionAbove_eulerOp`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/AnalyticMatching.lean:38`

```lean
theorem hasQExpansionAbove_eulerOp {x : LaurentSeries ℚ} {X : ℂ → ℂ} {R : ℝ}
    (eX : HasQExpansionAbove (toComplexLaurent x) X R) :
    HasQExpansionAbove (toComplexLaurent (eulerOp x))
      (fun τ => deriv X τ / (2 * Real.pi * Complex.I)) R
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.hasQExpansionAbove_eulerOp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `hasQExpansionAbove_omegaDenom`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/AnalyticMatching.lean:51`

```lean
theorem hasQExpansionAbove_omegaDenom {A : WeierstrassCurve ℚ}
    {x y : LaurentSeries ℚ} {X Y : ℂ → ℂ} {R : ℝ}
    (eX : HasQExpansionAbove (toComplexLaurent x) X R)
    (eY : HasQExpansionAbove (toComplexLaurent y) Y R) :
    HasQExpansionAbove (toComplexLaurent (omegaDenom A x y))
      (fun τ => 2 * Y τ + (A.a₁ : ℂ) * X τ + (A.a₃ : ℂ)) R
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.hasQExpansionAbove_omegaDenom' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `pullbackIsMultiple_iff_analytic`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/AnalyticMatching.lean:67`

```lean
theorem pullbackIsMultiple_iff_analytic {A : WeierstrassCurve ℚ}
    {x y : LaurentSeries ℚ} {ĝ : PowerSeries ℂ} {c : ℂ}
    {X Y G : ℂ → ℂ} {R : ℝ}
    (eX : HasQExpansionAbove (toComplexLaurent x) X R)
    (eY : HasQExpansionAbove (toComplexLaurent y) Y R)
    (eG : HasQExpansionAbove (HahnSeries.ofPowerSeries ℤ ℂ ĝ) G R) :
    PullbackIsMultiple A x y ĝ c ↔
      ∀ τ : ℂ, R < τ.im → deriv X τ =
        2 * Real.pi * Complex.I * c * G τ * (2 * Y τ + (A.a₁ : ℂ) * X τ + (A.a₃ : ℂ))
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.pullbackIsMultiple_iff_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `pullbackIsMultiple_cuspForm_iff_analytic`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/AnalyticMatching.lean:94`

```lean
theorem pullbackIsMultiple_cuspForm_iff_analytic {M : ℕ}
    (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2)
    {A : WeierstrassCurve ℚ} {x y : LaurentSeries ℚ} {c : ℂ}
    {X Y : ℂ → ℂ} {R : ℝ}
    (eX : HasQExpansionAbove (toComplexLaurent x) X R)
    (eY : HasQExpansionAbove (toComplexLaurent y) Y R) :
    PullbackIsMultiple A x y (qExpansion 1 g) c ↔
      ∀ τ : ℂ, max R 0 < τ.im → deriv X τ =
        2 * Real.pi * Complex.I * c * g (ofComplex τ) *
          (2 * Y τ + (A.a₁ : ℂ) * X τ + (A.a₃ : ℂ))
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.pullbackIsMultiple_cuspForm_iff_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `exists_rat_eq_of_rational_pullback`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/AnalyticMatching.lean:112`

```lean
theorem exists_rat_eq_of_rational_pullback {A : WeierstrassCurve ℚ}
    {x y : LaurentSeries ℚ} (hx : ∃ n : ℤ, n ≠ 0 ∧ x.coeff n ≠ 0)
    {b : ℕ → ℚ} {c : ℂ}
    (h : PullbackIsMultiple A x y ((PowerSeries.mk b).map (algebraMap ℚ ℂ)) c) :
    ∃ r : ℚ, (r : ℂ) = c
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.exists_rat_eq_of_rational_pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `qExpansion_eq_rational_coefficients`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/AnalyticMatching.lean:148`

```lean
theorem qExpansion_eq_rational_coefficients {M : ℕ} (E : WeierstrassCurve ℚ)
    (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2)
    (hg : ∀ n : ℕ, 0 < n → (qExpansion 1 g).coeff n = (E.LFunction n : ℂ)) :
    qExpansion 1 g =
      (PowerSeries.mk (fun n => if n = 0 then 0 else (E.LFunction n : ℚ))).map
        (algebraMap ℚ ℂ)
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.qExpansion_eq_rational_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `hasWeakWeilParametrization_of_modularPoint`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/AnalyticMatching.lean:169`

```lean
theorem hasWeakWeilParametrization_of_modularPoint (E : WeierstrassCurve ℚ)
    [E.IsElliptic] [NeZero (newformLevel E)]
    (g : CuspForm (Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hg : ∀ n : ℕ, 0 < n → (qExpansion 1 g).coeff n = (E.LFunction n : ℂ))
    {x y : LaurentSeries ℚ} (hpt : IsModularPointQ (newformLevel E) E x y)
    {c : ℂ} (hp : PullbackIsMultiple E x y (qExpansion 1 g) c) :
    HasWeakWeilParametrization E
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.hasWeakWeilParametrization_of_modularPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### `hasWeakWeilParametrization_of_analytic_modularPoint`

Locator: `ZInQKernel/Contrib/RC53Assist/DeltaProduct/AnalyticMatching.lean:194`

```lean
theorem hasWeakWeilParametrization_of_analytic_modularPoint (E : WeierstrassCurve ℚ)
    [E.IsElliptic] [NeZero (newformLevel E)]
    (g : CuspForm (Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hg : ∀ n : ℕ, 0 < n → (qExpansion 1 g).coeff n = (E.LFunction n : ℂ))
    {x y : LaurentSeries ℚ} (hpt : IsModularPointQ (newformLevel E) E x y)
    {c : ℂ} {X Y : ℂ → ℂ} {R : ℝ}
    (eX : HasQExpansionAbove (toComplexLaurent x) X R)
    (eY : HasQExpansionAbove (toComplexLaurent y) Y R)
    (hd : ∀ τ : ℂ, max R 0 < τ.im → deriv X τ =
      2 * Real.pi * Complex.I * c * g (ofComplex τ) *
        (2 * Y τ + (E.a₁ : ℂ) * X τ + (E.a₃ : ℂ))) :
    HasWeakWeilParametrization E
```

```text
'ZInQ.Contrib.RC53Assist.DeltaProduct.hasWeakWeilParametrization_of_analytic_modularPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Separately inspected dependencies

```text
'ZInQ.Contrib.RC53Assist.NewformPeriodsG1.parametrizationPeriodsGlue_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.CloudB3RC53.ModularWeil.exists_isLatticeOf' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Product-presentation definitions

```lean
def etaProductZ : PowerSeries ℤ :=
  ∏' n : ℕ, (1 - PowerSeries.X ^ (n + 1))
```

```lean
def deltaProductZ : PowerSeries ℤ := PowerSeries.X * etaProductZ ^ 24
```

```lean
def deltaProductQ : PowerSeries ℚ := deltaProductZ.map (Int.castRingHom ℚ)
```

```lean
def taylorZero (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0
```

```lean
def etaPolynomial (s : Finset ℕ) : Polynomial ℤ :=
  ∏ n ∈ s, (1 - Polynomial.X ^ (n + 1))
```

```lean
def eisenstein4Z : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3
```

```lean
def eisenstein6Z : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5
```

```lean
def jNumeratorZ : PowerSeries ℤ :=
  eisenstein4Z ^ 3 * (etaProductZ ^ 24).invOfUnit 1
```

```lean
def jProductQ : LaurentSeries ℚ :=
  HahnSeries.single (-1 : ℤ) 1 *
    HahnSeries.ofPowerSeries ℤ ℚ (jNumeratorZ.map (Int.castRingHom ℚ))
```
