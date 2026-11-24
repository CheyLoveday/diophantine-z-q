# The genuine transported even reading and the fresh prime

The Branch 2 address adapter supplies `FreshPrime`, `EvenReading` and
`EvenFilter` to the existing `AddressDensityLeaf`. The two remaining even
inputs must refer to the same genuine source of sign +1 on the twist by
`k`, at reference index 1. A unit of its depth-zero reading gives (F.1)
with equality and `CeFinal = v₂ L_*`k``. No changes to the wiring or new
prints are needed. The proof branch starts at
`7b5e84d80db4189e5a11e47279ef0ed789399344`.

## Statements

The declarations below live in `ZInQ.Manuscript.RC.EvenReading`; the Lean
files are under `ZInQKernel/Contrib/OneProof/RC/EvenReading/`. Here
`n_U = ∏ q ∈ U, q` and `C` is the original normalization.

| Declaration | Statement and supplied conjunct |
| --- | --- |
| `transportedNormalization` (definition with proved anchor) | From `k < 0` and `C : CentralNormalization E`, constructs a normalization on the twist by `k`, with `L_*'(h) = C.Lstar (h*k)` and the two periods swapped and divided by the square root of the absolute value of `k`. The anchor uses the double twist identity and the signs of `h` and `h*k`. Supports `EvenReading`. |
| `exists_evenSupport` | Given an entire continuation `F` of `L(E,s)` with `F 1 ≠ 0` and a finite set `T` of primes, there is a finite set of primes `S` containing `T`, 2, and the prime factors of each level in `RootNumberAt E N w`. Supports the `hcond` input to Appendix E for `EvenReading`. |
| `genuineEvenSource_of_prints` | Given the five inputs listed below, `0 < ℓ`, `C`, `hk : k < 0`, `C.Lstar k ≠ 0` and a finite set `T` of primes, there is a support `S` containing `T` and a `GenuineEvenSource C hk S`. This records level support, `EvenPhaseData` for the transported normalization at sign +1 and reference index 1, the exact `S0Filter S 1` and Appendix E phase, and rational coefficients satisfying (E.11) on that filter. Supplies the source for `EvenReading`. |
| `freshPrime_of_support` | In Branch 2 with `CompanionLeaf W`, if every prime of `m₁` lies in `Sold` and every prime in `Sold` avoids `k`, then there is a prime `q₀` dividing `k` and not dividing `m₁`. Supplies `FreshPrime`. |
| `omegaN_prod_primes` | For a finite set `U` of primes, `ω(n_U) = U.card`, by `Nat.primeFactors_prod`. Supports `EvenReading`. |
| `revGen_eq_one` | For a finite set `U` of primes with `RevGen S r U = 1`, the product `n_U` is in `S0Filter S 1`, `r n_U ≠ 0` and `v₂(r n_U) = U.card`. The reading is `coeffReading` of the rational coefficients embedded in the two-adics, at depth zero on this exact filter. Supports `EvenReading` and `EvenFilter`. |
| `genuineEvenSource_of_companion` | Specializes the printed construction to Branch 2, using `CompanionLeaf` for the sign and reference nonvanishing, and `LstarNormalized W.toRCData` for `C.Lstar = W.Lstar`. Returns that normalization, a support extending the prescribed set, and a genuine source there. Supports `EvenReading`. |
| `lstar_eq_of_revGen` | Given an aligned genuine source with `W.Lstar k ≠ 0`, at a finite set of primes reading one, `W.Lstar (n_U*k) ≠ 0` and `v₂(W.Lstar (n_U*k)) = 2 * U.card + v₂(W.Lstar k)`. This is (F.1) at depth zero; `EvenReading` needs only the upper bound. |
| `evenReading_of_genuineEven` | In Branch 2, an aligned `GenuineEvenSource` and `CompanionLeaf W` supply `EvenReading W D (RevGen S G.r)` with constant `v₂(W.Lstar k)`. |
| `evenFilter_of_genuineEven` | If the primes of `m₂` lie in `S`, then `EvenFilter W D (RevGen S r)`. Goodness gives coprimality and the filter gives the dyadic and odd square conditions; `AppE.isSquare_zmod_of_local` applies Hensel and CRT. |
| `genuineEvenSource_for_labels` | From a finite old support of primes, constructs the companion source with `S` containing the old support and the prime divisors of `k` and `m₂`. Provides the source required for the even discharge theorems and the variant. |
| `addressDensityLeaf_of_genuineEven` | With `CompanionLeaf W` and the Branch 2 hypothesis, `AddressDensityLeafGenuineEven W` implies `AddressDensityLeaf W`. The existing `addressLeaf_of_densityLeaf_branch` consumes the result with its existing premises. |

The support at tex 2600–2601 contains the ramification of **all the old
fixed label extensions and of the torsion field**, and precedes both the
inclusion of the companion primes and the moving theta prime. `LabelData`
describes `m₁` as the old odd modulus but does not carry the needed upper
bound on its prime support. The smallest added label clause is
`∀ p : ℕ, p.Prime → p ∣ D.m₁ → p ∈ Sold`, from the old label construction
at tex 2015–2029, 2600–2608. Companion avoidance is
`∀ p ∈ Sold, ¬ (p : ℤ) ∣ W.kfin`, the final conjunct of
`CloudB3RC53.Companion.exists_companion` specialized to the selected `k`.
`companionLeaf_of` does not keep it. This is where the cloud root must
retain it. Since `k` is negative and is not −1, its absolute value has
a prime divisor. The companion's squarefree and discriminant conditions
identify these divisors as ramified primes; the existing `FreshPrime`
only asks for the divisibility and avoidance. It does not ask for the
field intersection consequence at tex 2605–2608.

## Remaining inputs and owners

The variant quantifies over the actual label data and a genuine source with
the support and normalization just described. The outstanding address
obligations at those witnesses are:

| Input | Owner and scope |
| --- | --- |
| `LabelData W`, old support coverage and companion avoidance | Address and companion integrators. These specify finite label moduli, filters and exclusions. They say nothing about density models, reading units or seeds. Avoidance is already available at the companion choice. |
| `LstarNormalized W.toRCData` and `CompanionLeaf W` in Branch 2, with `0 < ℓ` for the construction | Central values (RC11), companion provider, and ambient `Adm ℓ`. These concern fixed periods and one nonzero reference twist. They make no claim about addresses. The adapter takes the companion separately; the variant stores the resulting normalization with its equality. |
| `OddDensityModels W D` | Odd density model owners. This gives stage models at each cutoff on the ultrafilter; it gives no even model, seed or label filter. |
| `OddFilter W D` | Intrinsic odd label/filter owner. Only conditions on admitted indices at `m₁ * ℓ₀`. |
| `PreparedFilter W D` | Prepared label/filter owner. Only the implication into `W.prepared` from the prescribed local types. |
| `EvenDensityModels W D (RevGen S G.r)` | Even density model owner. Only the budgeted trace models of the selected source. The modulus and the source's finite exclusions have to be coordinated when constructing these models. |
| `KSplitSeed W D (RevGen S G.r)` | App G seed / half-integral trace owner. Only the specified seed condition, with the very same reading; no seed or trace operator is constructed here. |

Each remaining conjunct is a smaller obligation than the full address
leaf at the given witnesses. This is a reduction in obligations, not a
logical claim that the bare existential `AddressDensityLeaf` implies
the genuine variant: the latter additionally pins down the provenance
of its reading. The downstream consumer still uses its existing
`PreDataSpec`, `PreparedSpec`, `W.δo ∈ W.depthSet` and Branch 2 premise.
With `h : ¬ W.OddEmptyUnit → AddressDensityLeafGenuineEven W`, its last
argument is `fun hU => addressDensityLeaf_of_genuineEven hcomp hU (h hU)`.

The **exact** existing Prop inputs of the source builder are
`PrintsAnalytic.WaldspurgerNonvanishing` and
`PrintsAnalytic.WaldspurgerCor2` (RC8/App E),
`AppE.RamseyAlgebraicModel` (App E),
`PoleS12.BCDTThmA` (shared modularity), and
`PrintsAnalytic.HasseConvergence` (RC8 analytic glue, Hasse bound and
absolute convergence). Each supplies an ingredient of the analytic
source only, and none asks for an address. `HalfIntegralTwist` is
discharged by `HalfIntegral.halfIntegralTwist`. The adapter takes the
constructed source with the proof of its coefficient identities; it
does not ask for the prints again. Deciding where to supply the five
Props in `RCLeaves` or `Prints` is left to the cloud root.

## Known issues

- `WaldspurgerNonvanishing` in the tree packages the cited nonvanishing
  together with the manuscript's classical scalar-character construction,
  level support and two-power order. The latter conditions are the
  manuscript's extra steps, not a claim about the literal printed theorem.
  The Waldspurger locators and the scope of the tree's printed Corollary 2
  remain UNVERIFIED against the original. The imported file records that
  the latter was checked against Purkait's quotation. The Ramsey locators
  and printed-form specialization also remain UNVERIFIED. Both existing
  statements are reused verbatim.
- The companion builder supplies nonvanishing and local avoidance; it does
  not show that this very `k` is an old-source unit (see its module
  docstring). The manuscript's global transported lower bound at tex
  10300–10314 uses that additional old-unit property. Here the proved
  conclusion is (F.1) for the prescribed depth-zero reading: whenever it
  reads one, the claimed equality follows. This does not independently
  certify the lower bound at all retained indices or a nonempty `K`-split
  unit. The lower bound, stated on the actual source, would be
  `∀ n, S0Filter S 1 n → G.r n ≠ 0 → (omegaN n : ℤ) ≤ padicValRat 2 (G.r n)`.
  It would identify zero as the least depth, since the normalized
  reference coefficient at 1 has valuation zero. No extra leaf is
  added for either assertion.

## Manuscript check

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 2015–2029 | gap filled | Record the inclusion of the prime divisors of `m₁` in the old fixed label support. |
| 2044–2046, 2068–2089 | OK | Read the coefficient at the positive product of distinct primes; the symbol reads one exactly at the indicated valuation on the filter. Its prime count and cast to the two-adics are on-the-spot formal bridges, provenance (c). |
| 2595–2601, 2605–2608 | gap filled | Retain the companion choice's avoidance and use that the absolute value of `k` exceeds 1 to find a prime divisor outside the old support (on-the-spot, provenance (c)). The subsequent field intersection is outside the adapter. |
| 7792–7817 | gap filled | Supply the support of every functional equation for the transported twist by uniqueness on the nonzero continuation; finite-support bookkeeping is on-the-spot, provenance (c). |
| 7829–7944 | unverified | Use the existing Waldspurger nonvanishing statement with its classical construction and character order. Its literature locators have not been checked here. |
| 7968–8028, 8041–8103 | unverified | Use the existing Waldspurger comparison and Ramsey statements in the Appendix E proof. The half-integral twist is already proved in the tree. |
| 8136–8146 | OK | Use the tree's (E.11), including its identity at a zero rational coefficient. |
| 10079–10094 | OK | Valuate the rational square identity at a nonzero coefficient. The valuation of the phase is removed by using the rational coefficient; the constant is fixed. |
| 10276–10286 | OK | Keep `k` fixed and the old support separate from the companion primes. |
| 10288–10295, 10306–10314 | gap filled | Prove the period scaling and sign swap in the anchor (on-the-spot, provenance (c)) and the signed argument `h*k`, without identifying the two source phases. |
| 10300–10305, 10312–10314 | unverified | The whole-filter lower bound uses the selected `k` being an old-source unit. This premise is absent from the current companion interface and is not used for (F.1) at a depth-zero reading. |
| 10320–10322 | OK | The depth-zero unit gives equality and hence the advertised uniform bound. |
| 10591–10594 | gap filled | Turn the local square conditions into a square modulo `m₂` by Hensel at prime powers and CRT, reusing the existing Appendix E lemma (on-the-spot application, provenance (c)). |

## Verification

`Normalization.lean`, `Source.lean`, `Leaf.lean` and `DensityLeaf.lean`
passed `lake env lean -j1` one at a time, without warnings. Existing
dependency artifacts were reused. The check file
`scratch/rc-even-reading/Axioms.lean` also passed. Every item below
reported exactly `propext`, `Classical.choice` and `Quot.sound`:

- `transportedNormalization`, `exists_evenSupport`, `GenuineEvenSource`,
  `RevGen`, `genuineEvenSource_of_prints`.
- `freshPrime_of_support`, `omegaN_prod_primes`, `revGen_eq_one`,
  `genuineEvenSource_of_companion`, `lstar_eq_of_revGen`,
  `evenReading_of_genuineEven`.
- `evenFilter_of_genuineEven`, `genuineEvenSource_for_labels`,
  `AddressDensityLeafGenuineEven`, `addressDensityLeaf_of_genuineEven`.
