Base: `53109239c3236c49fbf9e308d946cdc066322884`.

- Manuscript domain: `q ∉ Scoeff ∪ U`; `Scoeff` includes every late sieve and the moving theta prime. Tex 9471–9483, 9670–9674.
- `InertiaOn`: `T.Good q → q ∉ support → q ∉ U → ...`; `windowModel` and `buildWithFormwiseInertia` use `TypeDetectsRadicals χ support` and `T.m.primeFactors ⊆ support`.
- `ThetaCoeff.no_good_mem_stationary`: `T.Good q → q ∉ support` under the existing type-detection and Frobenius hypotheses. For primes, `q ∈ support ↔ q ∣ T.m` under the constructor hypotheses (c).
- `LabelData.T₁_m`: `(D.T₁ θ).m = D.m₁ * D.ℓ₀ θ`. Moving prime covered at the concrete type; no field connects all actual late sieves to `D.m₁`.
- `FormwiseHecke` and `hexcl`: require `T.Good q` and `q ∉ U`; `hexcl` additionally requires `q ∈ avoid`. No coefficient support test.
- Realization: `realize_of_stage` inherits `LevelSetup.old_good`; `realize` copies it and uses `test_coprime`. Required replacement: restricted old-level coprimality and `∀ q, Test T avoid q → q.Coprime old`, alongside the existing pool exclusion.
- Proposed restricted domain statements: active level coprimality; identity on seed inertia for subsets; integral Fourier formula and diamond translate; window Hecke formula. No new theorem or print.
- Stop: same-stage support coverage cannot be concluded; unchanged constructors exclude no additional `T.Good` sieve prime. No manuscript/source error established.
- Compile: no Lean files added; no Lean run or new axiom checks. Documentation whitespace checked with `git diff --cached --check`.
