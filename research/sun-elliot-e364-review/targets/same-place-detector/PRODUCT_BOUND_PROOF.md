# Lamport-style proof of `failedEverywhere_product_bound`

**Proposed owner:** Local-arithmetic workstream; next agent.

## Guard discovered before the argument

The auxiliary statement needs `hk : ∀ i, 1 ≤ k i`. The parent theorem already
carries it. Without it, take odd `α = 3`, `k = 0`, and `D` with valuation -1.
The displayed failure `v(D) < k` holds, while the nonconstant valuation is
`α + 2(v(D) - kα) = 1`. Its factor value is therefore `min(0,1) = 0`, not at most
`-α = -3`. This is not a counterexample to Sun, where every `k_i ≥ 1`.

Similarly, an odd scalar can be negative. The proof handles that case without
assuming an artificial positivity premise: all factor values are nonpositive,
hence the product value is at most zero, which is enough when `-α > 0`.

## Formula and finite products

Put `α = v_p(R)` and `v = kit.val P`. For detector index `i`, define
`b_i = α + 2(v(D_i) - k_i α)`. The factor identity proved previously gives
`v(f_i) = min 0 b_i`. By induction on finite products using `map_one` and
`map_mul`, `v(∏ f_i) = ∑ v(f_i)`.

**Every factor value is nonpositive:** `min 0 b_i ≤ 0` with no sign assumption
on `b_i`. Their sum is therefore nonpositive.

## Step 1: the `k_i = 0` gap is fixed by `k_i ≥ 1`

At a failed place choose `i` with `v(D_i) < k_i`. If `k_i` were zero and `α` were
positive, this would only give a positive bound on some factors, not a bound by
`-α`. The retained `hk` prevents this case.

## Step 2: negative scalar valuation

If `α < 0`, simply combine product-value nonpositivity with `-α > 0`. No failed
place is needed. This is deliberately separate instead of silently dividing by
`α` or manipulating `WithTop ℤ` as though it were an ordered field.

## Step 3: positive scalar valuation

Now assume `α > 0`. Let a failed place choose `i` with `v(D_i) < k_i`. Since
`k_i` is finite, `v(D_i)` is finite too; lift it to an integer `d` and derive
`d < k_i`. With `k_i ≥ 1` and `α ≥ 1`,

```
 d + (1 - k_i)α ≤ (k_i - 1)(1 - α) ≤ 0.
```

Hence

```
 b_i = α + 2(d - k_i α) ≤ -α.
```

The factor at that failed index therefore has value at most `-α`. All the
others are at most zero. Decompose the finite sum at `i`:

```
 value(W) = value(f_i) + ∑_{j ≠ i} value(f_j) ≤ -α.
```

This is exactly why a failed factor cannot be offset by other factors: factor
valuations are capped above by zero, they are never strictly positive.

## Implementation notes

- `addValuation_prod` isolates the finite-product induction.
- `Finset.add_sum_erase` isolates one failed index without a choice of maximal
  place or any max-plus bookkeeping.
- A typed coercion lemma transports the finite inequality back into `WithTop ℤ`.
- The zero scalar case is impossible because `α` is odd. The negative and
  positive branches cover the only other possibilities.
- This is not the parent detector theorem. Finding one common place out of a
  bad global assignment still requires the trace rescaling and the proper pole
  application, rather than this auxiliary inequality alone.

## Executed result

Lean 4.35.0 accepts both `detectorFactor_valuation` and
`failedEverywhere_product_bound` with **no `sorryAx`**, and their axiom reports
are `propext`, `Classical.choice`, and `Quot.sound`. The final
single-group obligation `samePlaceDetector` is proved in
`SAME_PLACE_PROOF.md`; the genuine trace/place application and its pole
packaging remain separate. The explicit `hk` premise appears in the formal
statement, rather than being hidden in the parent citation.
