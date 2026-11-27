`exists_selection_of_prints` builds the old source with (E.9) and
(E.11), then chooses `k` with `exists_companionOldUnit`.
`Selection.leaf_and_oldUnit` supplies every conjunct of
`CompanionLeaf W` and the certificate `CompanionOldUnit A.old W.kfin`
for that same `k` and that same old source. `Selection.fresh_ramification`
proves that the quadratic field of the selected `k) has a ramified prime
outside both old supports. No new prints are introduced.

The manuscript's choice at tex 2595–2599 leaves the reference implicit.
Appendix E (7793–7796, 8193–8196) requires a nonzero reference retained by
the initial sieve. The already fixed genus partner cannot be that
reference, since the companion is required to be coprime to it. The
reference can be supplied by the existing BFH clause (ii) with the enlarged
splitting set, as used for a different witness at tex 8250–8254.

The inherited shell support slip at tex 10393–10404 is documented in
[rc-ksplit-seed](rc-ksplit-seed.md). That argument is downstream of this
provider.

## Declarations

All names are in `ZInQ.Manuscript.RC.CompanionUnit`.
Write `S₀ = levelPrimes ℓ = primes(2N)`,
`B = exclusions Sold T hstar = Sold ∪ T ∪ primes(|hstar|)`, and
`S = finalSupport ℓ Sold T hstar k = S₀ ∪ B ∪ primes(|k|)`.
`NegativeFilter` requires a negative squarefree integer, a unit square at
each prime of `S₀`, and divisibility by no prime of `B`. Its test at two
already excludes −1 and −3 and gives the odd discriminant condition
`k % 4 = 1`. The primes only in `B` impose no squareclass test.

| Theorem | Statement and use |
| --- | --- |
| `two_mem_levelPrimes` | `0 < N → 2 ∈ S₀`. Supplies the dyadic test used for the exceptions and residue modulo four. |
| `signed_class_iff` | At a prime `p`, if `−D₀` is a unit square, the unsigned relative class test on `d*D₀` is equivalent to the signed square test on `−d`: modulo eight for `p = 2`, modulo `p` otherwise. The coprimality test is kept separately. |
| `negativeFilter_iff_oldRetained` | If `k < 0` and `−D₀` is a unit square on `S₀`, then `NegativeFilter ℓ Sold T hstar k ↔ oldRetained S₀ B D₀ k.natAbs`. This gives squarefreeness, the signed local tests, and avoidance of the full pre-companion exclusion set. |
| `rootNumberAt_newformLevel` | With ellipticity and `ModularNewform`, `RootNumber E w → RootNumberAt E (CST.newformLevel E) w`. The level of the newform divides every level of a cusp form with the same coefficients and is itself an eligible level. Thus it agrees with the least cusp-form level and with the functional-equation level. |
| `exists_negative_reference` | The existing BFH clause (ii), at base root number −1 and with the required splitting set, gives `∃ D₀, NegativeFilter ℓ Sold T hstar (−D₀) ∧ C.Lstar (−D₀) ≠ 0`. This supplies the reference only. |
| `oldSource_of_negative_reference` | From that initial filter, reference nonvanishing and the existing App E inputs, get `Nonempty (OldSource C S₀ B D₀)`. The proof applies `evenPhaseData_of_prints` followed by `oldSource_of_phase`, which computes the attained depth on the entire initial sieve. |
| `exists_selection_of_source` | Given `O : OldSource C S₀ B D₀` with a reference retained by the signed initial filter, obtain a `Selection` with reference index `D₀`, its filter membership, and old source exactly `O`. Its `k` is the negative integer from `exists_companionOldUnit O`; its `oldUnit` is that certificate. The first conclusion of `old_transport_inputs` gives `C.Lstar k ≠ 0` by (E.11). |
| `exists_selection_of_prints` | With the hypotheses below, `Nonempty (Selection C Sold T hstar)`. The construction fixes the reference and App E form before using the attained minimum to select the companion. |
| `Selection.leaf_and_oldUnit` | For a selection `A` and `hstar ≠ 0`, if `W.kfin = A.k`, `W.S = S`, `W.hstar = hstar` and `W.Lstar = C.Lstar`, then `CompanionLeaf W ∧ CompanionOldUnit A.old W.kfin`. Negativity, squarefreeness and local square units come from `A.filter`; the residue at two gives the two exceptions and the residue modulo four; the last union summand gives prime membership in `W.S`; the last summand of `B` gives coprimality to `hstar`; `A.central` supplies central nonvanishing. |
| `Selection.fresh_ramification` | For a number field `K` of degree two and `s : K` with `s^2 = A.k`, `discr K = A.k ∧ ∃ p ∈ ramifiedPrimes K, p ∉ Sold ∧ p ∉ T`. A prime factor exists because `k < 0` and `k ≠ −1`; it ramifies by the discriminant criterion. Every prime factor of `k` avoids `Sold` and `T`. |

The signed filter equivalence uses `D₀ ≡ d ≡ 7 mod 8` in the
dyadic class. At odd primes it cancels the nonzero square `−D₀`
from the product `(−d)(−D₀)`. The filter adapter, exact-level bridge, record, support
unions and interface equalities are on-the-spot (c). Applying the
already cited BFH clause (ii) a second time, for this reference in
the prescribed enlarged splitting set, is the on-the-spot
application (c) that supplies the implicit reference.

## Remaining hypotheses and owners

| Exact input | Owner |
| --- | --- |
| `0 < ℓ` and `RootNumber (Ecurve ℓ) (-1)`. The provider aligns the functional-equation level with `CST.newformLevel` using `ModularNewform`, then uses App E's `hcond_primeFactors`. | Curve and root number integrators (the existing base root number node). |
| The actual anchored `C : CentralNormalization (Ecurve ℓ)` and `EvenLowerBound (Ecurve ℓ) C` for (E.9); `ModularNewform`, `HasseConvergence`, `Nonvanishing.BFHNonvanishing`, `WaldspurgerNonvanishing`, `WaldspurgerCor2`, and `RamseyAlgebraicModel`. | Existing normalization, App E and analytic integrators. BCDT, continuation and the half-integral twist theorem are obtained from existing results. If the old source is already prepared with a retained reference, `exists_selection_of_source` does not take any of these analytic premises again. |
| Fixed `Sold T : Finset ℕ` of primes prior to the choice of `k`. For every old fixed label field `F`, require `ramifiedPrimes F ⊆ (↑Sold : Set ℕ)`; require `ramifiedPrimes ℚ(E[8]) ⊆ (↑T : Set ℕ)` for the actual torsion field. Include the prescribed odd support and witness primes in `Sold` (in particular the primes of `D.m₁` for the address handoff). Supply the actual quadratic field with its degree-two and square-root witnesses to `fresh_ramification`. | Odd support, label and torsion field integrators. The prime is constructed by the theorem; the remaining datum is coverage of the actual old fields by the supplied sets. |
| The already selected `hstar ≠ 0`; construct `W` with `W.hstar = hstar`, `W.Lstar = C.Lstar`, `W.kfin = A.k` and `W.S = finalSupport ℓ Sold T hstar A.k`. | Genus partner and RC wiring integrators. Use the companion choice before building the fields of `W` that depend on `k`. |
| A genuine transported source for `A.k` with support containing `S₀ ∪ B ∪ primes(|k|)`. | Address integrator: use `genuineEvenSource_for_labels` with prescribed old support `S₀ ∪ B`; that construction also includes the prime factors of `k` and the even label modulus. Use the same original `C` for the transported source (or call `genuineEvenSource_of_prints` directly with `C` and the same support union). Then `transported_lower_of_companion_old_unit` consumes the provider certificate. Density, seed construction, coefficient place, and preservation of the odd minimum remain with their existing owners. |

Neither `HoffsteinLuo` nor `BFHTwistSign` is a premise of the new
provider, including reference preparation. The reference uses the
existing `BFHNonvanishing` clause (ii), distinct from
`BFHTwistSign`. The previous
`CloudB3RC53.Companion.exists_companion` still takes both. Both remain
in `Nonvanishing.genusPartner` and `Wiring.exists_genusPartner`
for `h_*`, and in the rough companion route
(`Nonvanishing.roughCompanion`, `Wiring.f3Target_of`);
the even/five-prime nonvanishing and twist sign helpers also still use
their existing print inputs.

## Known issues

- The old source's sieve must use the support before choosing `k`.
  Using final `W.S` as the initial sieve would exclude every prime
  factor of `k` and hence exclude the chosen Fourier index.
- The `AuxInputs` source family is on a sibling branch and is absent
  at the assigned base. Its support is read from its input `W.S`,
  and its family requires a nonzero reference for the chosen type.
  The provider uses the corresponding App E construction directly,
  with the negative signed squareclass and initial sieve explicit.
- The existing Waldspurger nonvanishing print includes the manuscript's
  classical construction and two-power character condition. Its printed
  scope and locators remain UNVERIFIED as in
  [rc-even-reading](rc-even-reading.md); the provider uses the existing
  statement as given. BFH's printed form is also reused as given, without
  an independent literature check.
- The interface's order of choices for the odd minimum and the inherited
  shell support slip (tex 10393–10404) are outside this provider.

## Manuscript check

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 1825–1830 | OK | Use the same anchored original `C` for the old source and for the companion central value in `W`. |
| 2404–2410, 8254–8258 | OK | Keep the already fixed genus partner and exclude its prime factors in the initial sieve. |
| 2595–2598 | gap filled | Match the signed local square units and exclusions exactly with the unsigned Fourier filter; the class at two automatically excludes the exceptional fields. |
| 2598–2599, 7793–7796, 8250–8254 | gap filled | Appendix E needs a retained nonzero reference before the minimum exists. Use the cited BFH clause (ii) with the initial exclusions also in the splitting set. |
| 7780–7786 | OK | Reuse (E.9), including its upstream forward rank-zero argument, as `EvenLowerBound`. |
| 7791–7808, 8130–8145 | OK | The existing negative phase and (E.11) apply at the original reference; a unit's rational coefficient is nonzero, forcing the signed central numerator nonzero. |
| 8148–8155, 8193–8199 | OK | Fix the extra sieve before the integral minimum and use attainment. |
| 2599–2603 | gap filled | Use `disc K = k` and a prime factor of `|k|` outside the two fixed supports. Form the next support only after selecting `k`. |
| 2605–2612, 10519–10521 | unverified | Old odd lifts and minimum preservation belong to the separate odd-stage argument. |
| 10260–10262, 10288–10297 | OK | The same negative unit gives the positive Fourier index `|k|`; the transported support covers the old support and the factors of `k`. |
| 10298–10315 | OK | The provider supplies exactly the old minimum equality at `|k|` required by the imported transport proof. |
| 10393–10404 | error | The inherited “old support” shell split omits transported stationary primes if read as the pre-transport support. See the downstream seed report. |

## Verification

All six direct imports built with serial `lake build` before the
final `lake env lean -j1` check of `Provider.lean`, which passed
without diagnostics. `scratch/rc-companion-unit/Axioms.lean` passed
a separate `lake env lean -j1` run. For each of the ten theorems
listed above, `#print axioms` returned exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry` or added axiom.
