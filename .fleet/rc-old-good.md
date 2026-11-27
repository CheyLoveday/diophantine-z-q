**Scoped stop: `InertiaOn` cannot exclude a coefficient sieve prime that remains `T.Good`.** Its `support` must satisfy `TypeDetectsRadicals χ support`, and the existing `ThetaCoeff.no_good_mem_stationary` rules out every `T.Good` prime from such a support. Together with `T.m.primeFactors ⊆ support`, this pins the prime part of `support` to the type modulus. `avoid` changes the ambient tests only. `hexcl` and `good_hecke` likewise have no explicit exclusion for the coefficient support of tex 9471–9483 and 9670–9674. No manuscript or printed-source error was established.

The concrete odd type `LabelData.T₁` has modulus `m₁ * ℓ₀`, so its moving prime is already excluded. To use the existing consumers unchanged, link that type to the same lifted stage and prove that every actual late sieve lies in the type modulus. If a sieve stays `T.Good`, a restricted Hecke proof cannot fill the current `hexcl`, and the Kummer comparison still needs control of the trace quotient at the extra prime.

`realize_of_stage` still takes unconditional coprimality through `LevelSetup.old_good`. The revised construction would need the actual old-level bound outside coefficient support and the ambient test `∀ q, Test T avoid q → q.Coprime old`, in addition to the existing pool exclusion. The analytic inputs stay with their current owners.

No Lean declarations or prints were added; no compilation or axiom checks were needed for this stop. The [report](../docs/research/rc-old-good.md) records the exact definitions, remaining inputs, and manuscript checks. The [results log](../scratch/rc-old-good/log.md) records the findings.

Final result SHA: `1c6dae293b3415a72194db8f04f1c2c8bb32afc6`. The status-only commit follows it and is identified by `git log -1 --format=%H -- .fleet/rc-old-good.md`.
