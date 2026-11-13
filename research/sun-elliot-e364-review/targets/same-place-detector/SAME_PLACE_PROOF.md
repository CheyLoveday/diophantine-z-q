# Lamport-style proof of `samePlaceDetector`

**Proposed owner:** Local-arithmetic workstream; next agent.

## Assumptions kept visible

Use the repaired `DetectorKit`, whose rational valuations are conditional on
zero, with nonzero `R`, every precision order `k_i ≥ 1`, nonzero product `W`,
nonzero trace `Θ = Tr(W⁻¹)`, odd `α = v_p(R)` and the inherited no-negative-odd
pole rule for `B = R/Θ²`. `hW` and `hTheta` are semantic guards, not replacements
for these conditions.

## Auxiliary estimates already proved

The factor theorem supplies `v(f_i) = min 0 b_i`.
The failed-place product theorem, with `hk`, says that if every place has a
failed precision test, then `v(W) ≤ -α` there. Independently, without any failed
place, finite-product induction gives `v(W) ≤ 0` at every place because every
factor value is at most zero.

The kit's normalized unramified trace rule applies to any finite integer `a`:

```
 (∀ P, a ≤ v(W⁻¹))  ⇒  a ≤ v_p(Tr(W⁻¹)).
```

## Step 1: negative scalar valuation contradicts the pole rule

Suppose `α < 0`. Since `v(W) ≤ 0` and `W ≠ 0`, all places satisfy
`0 ≤ v(W⁻¹) = -v(W)`. Take `a = 0` in the trace bound. Thus `τ = v(Θ) ≥ 0`.
Consequently `value(B) = α - 2τ < 0`. Since `α` is odd and `2τ` is even, this
is a negative odd valuation. The pole rule forbids it. Therefore `0 < α`: an odd
integer cannot be zero, and negative has just been excluded.

## Step 2: a common place with every precision

Assume for contradiction that every place `P` has some index `i` with
`v(D_i) < k_i`. Invoke `failedEverywhere_product_bound` with `hk` and the proved
factor identity to obtain `v_P(W) ≤ -α` for every `P`.

Because `W ≠ 0`, its inverse valuation is `-v_P(W)`, hence at least `α`.
Apply the finite-integer trace bound with `a = α`. Thus
```
  τ = v_p(Tr(W⁻¹)) ≥ α.
```

`detectorB` is well-defined because `R` and `Θ` are nonzero, and
`padicValRat.div` with `padicValRat.pow` gives `value(B) = α - 2τ`.
By Step 1, `α ≥ 1`; hence `α - 2τ ≤ -α < 0`. This is negative and odd (the sum
of odd `α` and even `-2τ` is odd), again contradicting the pole rule.

Therefore some place `P` violates the assumed failure. In other words,

```
  ∃ P, ∀ i, k_i ≤ v_P(D_i).
```

As required, this is one place with **all** precisions, not an independently
selected place for each `i`. Return this witness together with `0 < α`.

## Scope note

This concludes the single-group (`G = 1`) algebraic detector target of the draft.
It does not instantiate Sun's actual Selmer objects, number-field trace,
unramified primes, pole predicate, or final Diophantine theorem. The reset of
`G` in Sun's lemma and the true number-field adapter are separate obligations.

## Executed result

Lean 4.35.0 with `-t0 -j1 -Ddebug.skipKernelTC=false` accepts all three
declarations **without proof holes**. Each of `detectorFactor_valuation`,
`failedEverywhere_product_bound` and `samePlaceDetector` has only
`propext`, `Classical.choice`, and `Quot.sound`. The finished module includes
`p_prime : p.Prime` explicitly, uses `padicValRat.div` and
`padicValRat.pow`, and proves the inverse comparisons `0 ≤ v(W⁻¹)` and
`α ≤ v(W⁻¹)` by lifting the nonzero product's finite integer valuation instead
of treating `WithTop ℤ` as a generic additive group.
