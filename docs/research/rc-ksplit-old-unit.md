**Scoped stop.** The missing datum is that the already fixed companion
`W.kfin` reads one on the original negative even source at its original
attained minimum. The current companion theorem proves a nonzero central
value and the local conditions. It does not prove that the same `k` is
an old unit. With the single certificate `CompanionOldUnit O W.kfin`,
the new bridge supplies `hOldk`, `hUnit`, `hOld` and `hOldLow` to
`KSplitSeed.transported_lower_of_old_unit`, obtaining
`ω(n) ≤ v₂(G.r n)` at every retained nonzero coefficient of the actual
`GenuineEvenSource` for `W.kfin`. No separate square or lower bound
comparison is needed.

The old source is the App E form for the **original** curve and sign
`−1`, with a positive reference `D₀` retained by its fixed initial
sieve. Its normalization is `a_old(d) = g[d] / g[D₀]`; write
`a_old(d) = z_d r_old(d)`. Both old square identities use the common
nonzero reference `Lref = C.Lstar (-(D₀ : ℤ))`. The Fourier indices are
`d_k = k.natAbs` and `d_k * n`; their signed twists are `k` and
`n * k`. Appendix E's `EvenPhaseData.minimum_sieved` calls
`minimum_on`, which uses `EvenPhaseData.E11` on that very phase data.
It returns the rational parts of these normalized coefficients and the
least depth on the original retained set. The new source is sign `+1`
on the twist by `k` and uses reference 1 and denominator `C.Lstar k`
via `EvenReading.transportedNormalization`. The three identities
therefore compare the same signed central values of the original curve.
The phase factors are kept with their respective sources.

The old filter is `S0Filter S₀ D₀` with the initial coprimality sieve
`B`. There are squareclass tests at `S₀`; the extra primes in `B`
only impose coprimality. The chosen companion has to lie in this filter
(tex 2595–2599, 10296–10297). Avoidance of the old primes and torsion
ramification in tex 2596–2601 gives the coprimality part when those primes
are in the fixed exclusion set; `oldRetained_of_companion_avoidance`
turns its signed divisibility test into the sieve test at `d_k`.
The old type must be the type prescribed for the separate negative
symbol. For example a reference and companion square at 2 as **signed**
twists have unsigned indices congruent to 7 modulo 8. One must compare
their classes, rather than test either unsigned index for congruence to
1. Any additional class tests at `S₀` beyond the primes of `2N` must
also match this source. The new filter excludes the primes of
`S₀ ∪ B` and of `d_k` (tex 10292–10295). Thus a new index `n` is
coprime to `d_k`, is a square unit at `S₀`, and avoids `B`.
Multiplication keeps squarefreeness, the original local classes and the
sieve. This puts `d_k n` in the domain of both (E.11) and the original
minimum bound.

The `AuxInputs` modules named in the brief are on the sibling
`origin/wip/rc-aux-inputs`, absent from the assigned base. They wrap
the same `EvenPhaseData.minimum_on`. To use a selected
`AuxInputs.EvenSource` at `B = ∅`, use its `phaseData`, `r`,
`δ`, `coeff`, `attained` and `lower` fields, identifying its
nonzero reference with `C.Lstar` using the shared normalization.
`AuxInputs.s0Filter_iff_type` identifies its type filter with
`S0Filter S₀ D₀` at the reference's type. There is no new choice of
form, coefficient or depth in this projection. If using a unit of its
realized graph symbol, `EvenSource.symbol_primeFactors` supplies the
scalar reading via its fixed-set factorization on the same source.
The bridge here imports the common App E proof on the assigned base.

## Declarations

All declarations are in `ZInQ.Manuscript.RC.KSplitOldUnit`.

| Declaration | Statement and consumer |
| --- | --- |
| `mul_old_filter` | If `d` has the old filter conditions relative to `D₀`, and `n` is positive squarefree, coprime to `d` and in the unit squareclasses of 1 at the old prime support, then `d*n` has the old filter conditions. Includes the residue modulo 8. Used for `hOld` and `hOldLow`. |
| `coprime_of_new_support` | A nonzero `d` and an `n` avoiding a support containing `d.primeFactors` are coprime. Used in the same alignment. |
| `oldSource_of_phase` | Given the fixed sign-minus-one `P`, a nonzero reference retained by `B`, and the existing Waldspurger, continuation and (E.9) inputs, obtain `O : OldSource C S₀ B D₀` with `O.phase = P`. Its fields give (E.11), attainment and the lower bound on the old retained set. Source for `hOldk`, `hOld`, and `hOldLow`. |
| `oldRetained_of_companion_avoidance` | `S0Filter S₀ D₀ k.natAbs` and `∀ p ∈ B, ¬ (p : ℤ) ∣ k` give `oldRetained S₀ B D₀ k.natAbs`. The old-filter side of the selection certificate. |
| `oldRetained_mul_of_new_filter` | With `S₀ ⊆ S`, `B ⊆ S`, `d.primeFactors ⊆ S` and every member of `S` prime, an old retained `d` and a new retained `n` have old retained product `d*n`. Supplies retention for `hOld` and `hOldLow`. |
| `companionOldUnit_iff` | `CompanionOldUnit O k` iff `d_k` is old retained, `O.r d_k ≠ 0` and `padicValRat 2 (O.r d_k) = (omegaN d_k : ℤ) + O.depth`. Supplies `hUnit` and both retention and nonvanishing at the companion. |
| `exists_companionOldUnit` | For the fixed old source `O`, some negative `k` reads one on that source, by its attained minimum. This uses its *initial* filter; it does not certify later exclusions or an independently selected companion. |
| `old_transport_inputs` | For a negative `k` with `CompanionOldUnit O k` and the indicated support inclusions, obtain `C.Lstar k ≠ 0`, `hOldk`, `hUnit`, `hOld` and `hOldLow` for `old := O.r`, `Lref := C.Lstar (-(D₀ : ℤ))`, `δ := O.depth`. Both comparisons follow by evaluating the same (E.11); the lower bound is the fixed minimum applied at `d_k*n`. |
| `transported_lower_of_companion_old_unit` | For `G : GenuineEvenSource C hk S` with `hk : W.kfin < 0`, `S₀ ⊆ S`, `B ⊆ S`, `W.kfin.natAbs.primeFactors ⊆ S` and `CompanionOldUnit O W.kfin`, obtain `∀ n, S0Filter S 1 n → G.r n ≠ 0 → (omegaN n : ℤ) ≤ padicValRat 2 (G.r n)`. Applies the existing transport theorem to the actual even reading. |

`OldSource` bundles proved App E outputs at a specified reference,
initial sieve and form. The record, the pointwise name
`CompanionOldUnit`, and the support plumbing are on-the-spot packaging
(c). The reading itself is the existing
`Symbols.coeffSymbol (fun d => (O.r d : ℚ_[2])) O.depth
(oldRetained S₀ B D₀) k.natAbs = 1`. No printed leaves are added.

## Exact remaining hypotheses and owners

| Input | Owner and size |
| --- | --- |
| `CompanionOldUnit O W.kfin` on the actual selected old source. Once the old filter membership and nonzero reference twist at `k` are established, it is precisely the equality `v₂ r_old(d_k) − ω(d_k) = δ_e`. | Companion integrator and lead, tex 2595–2599, 10260, 10312–10314. Retain the reading from the manuscript's choice of a unit. One option before constructing final `W` is to choose from the attained minimum of a separate negative source whose initial filter already enforces all the fixed exclusions and classes. The provider must check those conditions on that filter and use that very choice when building `W`. No inference of equality from nonvanishing is available. |
| An actual `O : OldSource C S₀ B D₀` for that negative symbol, and an actual `G : GenuineEvenSource C hk S` for `W.kfin`, with the same original `C` (equal to `W.Lstar` for the address adapter). | App E / source and address integrators. Use the existing phase producer and (E.11), nonzero old reference, continuation and (E.9) premises through `oldSource_of_phase`; or project the fixed `AuxInputs` source as above. The new source is already built by `genuineEvenSource_of_prints` or `genuineEvenSource_for_labels`. All print statements and the (E.9) route are upstream. |
| `S₀ ⊆ S`, `B ⊆ S`, and `W.kfin.natAbs.primeFactors ⊆ S`. | Address support integrator, tex 10292–10297. In `genuineEvenSource_for_labels`, use a prescribed old support that covers `S₀ ∪ B`; that builder also includes the factors of `k`. Extra old label/torsion support can be included as required by the address layer. |

The added certificate is **not** a logically strictly weaker version of
the current bare `CompanionTarget`. That target concerns the sign,
squarefreeness, exceptions, support, local square tests, coprimality to
`h_*` and analytic rank zero. It does not specify a form or minimum.
Conversely the pointwise certificate even has the same truth value at
`k` and `-k`, and asserts nothing about `h_*` or final support
membership. It is strictly narrower in scope than the manuscript's
full companion choice; supplementing today's target by it is a
strengthening of the recorded data. Together with the actual old (E.11)
and sign it already implies `C.Lstar k ≠ 0`.

For the selection route using attainment, the existing nonvanishing
construction can supply the reference, provided it is in the chosen
initial filter. In the signed class of 1 at 2, the unsigned index is
7 modulo 8, so the attaining twist excludes `−1` and `−3` and has a
prime factor. If the initial sieve contains the fixed ramification
exclusions, that factor is outside them. This is a choice of the
companion from the prepared source; it does not replace a fixed
companion after the transported source has been built.

Once these inputs are supplied, `revGen_empty` gives attainment at
index 1, so zero is the least depth of the same transported reading.
`evenCoeff_squarefree` identifies `G.r` as the rational part of the
normalized, sieved Fourier coefficient on this filter.
The nonempty split seed still needs the singleton divisions, coefficient
place and trace/determinant data in `rc-ksplit-seed`. Their owners are
the even budget, even place, and actual constituent and field
integrators, respectively. The old-unit bridge adds no density or
address hypotheses. As with the existing transport theorem, the Lean
statement uses `padicValRat` only on nonzero coefficients; the manuscript
bound at a zero coefficient uses valuation `+∞`.

For the phase-based construction the exact analytic inputs are
`PrintsAnalytic.WaldspurgerCor2`, ellipticity of `Ecurve ℓ`,
`∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist (Ecurve ℓ) h) F`,
and `EvenLowerBound (Ecurve ℓ) C` from (E.9). The old reference is
`C.Lstar (-(D₀ : ℤ)) ≠ 0` with `∀ p ∈ B, ¬ p ∣ D₀`.
The existing phase producer also uses the existing
`WaldspurgerNonvanishing`, `RamseyAlgebraicModel`, `BCDTThmA` and
`HasseConvergence`, and the proved half integral twist theorem. App E
and the existing glue own these inputs. They are already consumed if
the integrator supplies the actual old and new sources.

## Known issues

- `CloudB3RC53.Companion.exists_companion` chooses a nonvanishing twist
  and supplies avoidance, as its departure note records.
  `companionLeaf_of` drops the avoidance predicate for the old support,
  and neither result identifies the chosen twist with an old minimum.
  A new normalization at `d_k` alone would not repair this: it would
  set one coefficient to 1 without forcing it to attain the minimum.
- The old support cannot be the post-companion `W.S`: the latter
  contains every prime factor of `k`, and `k < 0`, `k ≠ -1` imply
  it has a prime factor. This would exclude `d_k` from the old filter.
  Use the pre-companion support when instantiating the old source,
  including when using `AuxInputs.sourceFamily_of_prints` (whose
  source support is its input record's `W.S`). The `CompanionLeaf`
  order-of-choices departure also concerns the odd minimum, and is
  outside this proof.
- The existing Waldspurger inputs and the App E phase construction are
  reused as stated. Their printed locators and printed-form scope remain
  UNVERIFIED independently, as documented by `rc-even-reading`. This
  proof does not extend those inputs or the upstream (E.9) proof.
- The preexisting support slip at tex 10393–10404 is recorded in
  `rc-ksplit-seed`; the transported lower bound does not use that shell
  split.

## Manuscript check

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 1825–1828 | OK | One original normalization `C` throughout, including the transported normalization's pullback. |
| 2016–2029, 2068–2089 | OK | Later selection tests do not redefine the old source. Its unit is the existing exact coefficient reading at fixed depth. |
| 2584–2593, 2605–2612, 10519–10521 | unverified | These concern the odd branch and invariance of its minimum; no odd comparison is used for the even unit. |
| 2595–2603, 10260–10262 | unverified | The text chooses a unit with the stated exclusions. The present companion provider does not establish this reading at its chosen `k`; retain the selection certificate. |
| 7793–7819, 8148–8155 | OK | Fix the old reference and squareclasses; a fixed initial coprimality sieve preserves the rational comparison at retained indices. |
| 8130–8145 | OK | The imported (E.11) removes the phase and gives the square identity, including zero. |
| 8193–8199, 10079–10093 | OK | The imported minimum theorem fixes the depth on the original retained set before further exclusions; an attained coefficient reads one. |
| 10288–10295 | OK | The coefficient at `d` tests `−d`; the new source on `E^k` uses `+1`, reference 1 and the larger unit filter. |
| 10296–10297 | gap filled | Starting with old retention of `d_k`, exclusion of its prime factors and square-unit multiplication at the old support preserve the full old filter at `d_k*n`. |
| 10298–10311 | OK | The two old (E.11) identities and the new one give the valuation difference on nonzero coefficients. The comparisons use one common old denominator. |
| 10312–10315 | gap filled | The fixed old minimum gives the inequality at `d_k*n`; the pointwise old unit gives equality at `d_k`. The latter still has to be supplied at the selected companion. |

## Verification

`Alignment.lean`, `Source.lean`, `Comparison.lean` and `Transport.lean`
each passed `lake env lean -j1` against the base imports, with one Lean
job at a time and host limits checked before each run. The separate
scratch checks `AxiomsAlignment.lean`, `AxiomsComparison.lean` and
`Axioms.lean` report exactly `[propext, Classical.choice, Quot.sound]`
for each of the nine theorems in the declaration table.
