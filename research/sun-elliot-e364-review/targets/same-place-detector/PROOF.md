# Lamport-style proof of `detectorFactor_valuation`

**Proposed owner:** Local-arithmetic workstream; next agent.

## Original statement is false

Take `R = -1`, `k = 0`, and `D = 1`. Then

```
 detectorFactor R D k i = 1 + (-1) * (1 / (-1)^0)^2 = 0.
```

Every additive valuation sends zero to `⊤`. At the same time,
`padicValRat p (-1) = 0`, `v(1) = 0`, and `localTermValue = 0`, hence
`min 0 localTermValue = 0`. The asserted valuation equality says `⊤ = 0`.

This is not a missing library lemma. The missing source-level premise is
`Odd (padicValRat p R)`. It is present in `samePlaceDetector` and in Sun's
Lemma 3.1. Adding `R ≠ 0` alone would not fix this counterexample.
The retained regression is `DetectorFactorCountermodels.lean`.

## Corrected statement

Assume the same `DetectorKit` as in `Draft.lean`, and add

```
hα : Odd (padicValRat kit.p R).
```

The corrected conclusion, for every place `P` and index `i`, is

```
 kit.val P (detectorFactor R D k i) = min 0 (localTermValue kit R D k P i).
```

## Notation

Fix `P` and `i`. Put
`v = kit.val P`, `α = padicValRat kit.p R`, `j = k i`, `q = detectorQuotient R D k i`,
and `t = (scalar R : F) * q^2`. The factor is `1 + t`, and the target
nonconstant value is `b = α + 2(v(D i) - j α)`.

## Proof

**Step 1. Nonzero scalar and zero-safe compatibility.**
`hα` implies `α ≠ 0`, hence `R ≠ 0`, since by definition
`padicValRat p 0 = 0` and zero is even. The compatibility field now requires
`val(q) = ↑padicValRat p q` only when `q ≠ 0`; at zero it separately requires
`val(0) = ⊤`. This avoids the independent inconsistency between
`AddValuation.map_zero` and `padicValRat.zero`.

**Step 2. Quotient value.**
`AddValuation.map_div`, `AddValuation.map_pow` and
`DetectorKit.val_algebraMap` give

```
 v(q) = v(D i) - j α.
```

**Step 3. Nonconstant value.**
`AddValuation.map_mul`, `AddValuation.map_pow`, Step 2 and
`DetectorKit.val_algebraMap` give

```
 v(t) = α + 2(v(D i) - j α) = b.
```

**Step 4. Zero test expression.**
If `D i = 0`, then `q = 0`, hence `t = 0` and `1 + t = 1`. Additive valuation of
one is zero. Also `v(D i) = ⊤`, so `b = ⊤` in the canonical `WithTop ℤ`
convention, and `min 0 ⊤ = 0`.

**Step 5. Finite and odd nonconstant value.**
Suppose `D i ≠ 0`. `AddValuation.ne_top_iff` gives a finite integer `d` with
`v(D i) = d`. By Steps 2 and 3,
`b = (α + 2(d - j α) : ℤ)` after coercion into `WithTop ℤ`.
Since `α` is odd and `2(d - j α)` is even, `b` is an odd integer, in particular
nonzero. Hence `v(t) = b ≠ 0`.

**Step 6. No cancellation.**
`AddValuation.map_one` gives `v(1) = 0`. Since `v(t) ≠ v(1)`,
`AddValuation.map_add_of_distinct_val` yields

```
 v(1 + t) = min (v 1) (v t) = min 0 b.
```

Step 4 proves the zero-expression case; Steps 2, 3, 5 and 6 prove the
nonzero-expression case.

## Safety audit of this interface

- The odd-valuation premise is not artificial: it is already present in the
  parent target and is exactly what excludes the cancellation countermodel.
- Zero `D i` is handled before claiming that `b` is an odd integer; treating
  `⊤` as odd would be meaningless.
- No nonnegativity of `b` is assumed: the nonconstant term can have negative
  odd valuation. Negative and positive factors both have nonpositive factor
  valuation, as required for the subsequent product bound.
- No proof of the parent detector follows merely from this factor identity.
  The later argument also needs the trace lower bound and maximum-over-places.

## Executed result

Lean 4.35.0 with `-t0 -j1 -Ddebug.skipKernelTC=false` accepts
`detectorFactor_valuation` with **no `sorryAx`**. The declaration's axiom
report is `propext`, `Classical.choice`, and `Quot.sound`. Its Lamport-style
continuation `failedEverywhere_product_bound` also has no `sorryAx`, and
`samePlaceDetector` is proved in `SAME_PLACE_PROOF.md` as well. All three `G=1`
declarations are now closed.
`DetectorKitLegacy.lean` proves the independent old trace/scalar zero bugs, and
`DetectorFactorCountermodels.lean` proves the original unguarded factor claim
false at `R=-1,k=0,D=1`.
