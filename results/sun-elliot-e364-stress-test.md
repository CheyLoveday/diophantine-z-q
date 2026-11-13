# Adversarial mathematics stress test: Sun / Glazer / E364 interfaces

## Bottom line

The hostile pass changed the state of the project rather than just replaying
old receipts:

1. **A genuine inconsistency was found in my first detector adapter.**
2. **The E364 powerfulness/unit-defect bridge was independently proved in
   Lean and promoted into production.**
3. **Lab sources confirm the powerful-triple source conventions, but do not yet
   provide the marked elliptic-point identification.**
4. **The proposed global interpolation/height transfer remains unproved.** The
   fits are descriptive; there is still no fixed-curve orbit, source-qualified
   family constants, or global contradiction.

There is **no counterexample to Sun's theorem, the Diophantine theorem, or Erdős
364 here**. Likewise, there is no claim that the global proof strategies have
been verified or that an E364 exclusion exists.

## Commanded evidence boundary

Work was local and direct, with no Ultramath/subagent fan-out, manuscript edit,
PR change, commit or remote write. The other local repositories were inspected
read-only; no external service or scientific search was launched. `AC-code`'s
instructions explicitly separate retained evidence from new experiment
authority, and no such experiment was run there.

## 1. Confirmed defect and repair: detector trace rescaling

### Legacy inconsistency

The first `DetectorKit.trace_lower_bound` had the shape

```lean
∀ (x : F) (a : WithTop ℤ),
  (∀ P, a ≤ val P x) → a ≤ (padicValRat p (trace x) : WithTop ℤ)
```

Take `x=0` and `a=⊤`. The left inequality holds at every place. The trace is
zero, and because `padicValRat p 0 = 0`, the legacy conclusion demands `⊤ ≤ 0`.
Hence **no such adapter exists on a nonempty place type**.

The regression file
`research/sun-elliot-e364-review/targets/stress/DetectorKitLegacy.lean` proves
`legacy_traceLowerBound_inconsistent`. Its compiler output shows exit 0 and only
`propext`, `Classical.choice`, and `Quot.sound`. This is an exact countermodel
to the old interface, not a counterexample to Sun's arithmetic or the detector.

### Repair

The draft now quantifies only over finite `a : ℤ` when applying trace
rescaling. It elaborates again with the three deliberately open proof
obligations, and reports `sorryAx` in its own isolated receipt:

- `detectorFactor_valuation`;
- `failedEverywhere_product_bound`;
- `samePlaceDetector`.

The first adapter field was repaired, but there was a second zero-sentinel
issue: normalized scalar compatibility must be conditional on `q=0`, since
`AddValuation 0 = ⊤` while `padicValRat p 0 = 0`. Both old inconsistencies remain
compiled in `targets/stress/DetectorKitLegacy.lean`.

The subsequent **detector factor theorem is now proved**, not merely
scaffolded. The old unguarded factor statement was independently false at
`R=-1,k=0,D=1`: the factor is zero, hence its valuation is `⊤`, while the
`min` expression is zero. The corrected theorem adds the source's
`Odd (padicValRat p R)` premise, splits zero from nonzero `D`, proves the
quotient value and the finite odd nonconstant value, and applies
`AddValuation.map_add_of_distinct_val`. The Lamport derivation is
`targets/same-place-detector/PROOF.md`; `detectorFactor_valuation` reports only
`propext`, `Classical.choice`, and `Quot.sound`. The remaining theorem-level
imports of unramified trace/place data are separate from the factor algebra.

### Continuation: failed-place product bound is proved too

The next obligation, `failedEverywhere_product_bound`, is now proved with no
`sorryAx`. Its Lamport derivation is in
`targets/same-place-detector/PRODUCT_BOUND_PROOF.md`. An additional guard had
to be imported from the parent theorem: every `k_i ≥ 1`.

For positive `α`, a failed coordinate is lifted to an integer `d`, and
`d < k_i` together with `α ≥ 1`, `k_i ≥ 1` gives
`d + (1-k_i)α ≤ 0`, hence `b_i ≤ -α`. Every other factor value is capped by
zero. The finite product valuation is mapped to a finite sum and decomposed at
the failed coordinate using `Finset.add_sum_erase`. For negative `α`, the same
nonpositive-factor bound is already enough because `-α > 0`; at `α = 0`, the
odd hypothesis is contradictory. The implementation keeps those regimes apart
rather than dividing by the scalar.

### Completion: one place with every precision

`samePlaceDetector` is now proved as well, with no `sorryAx`. The last Lamport
proof is in `targets/same-place-detector/SAME_PLACE_PROOF.md`.

For `α < 0`, the product's nonpositive value makes `v(W⁻¹) ≥ 0`, hence
`τ ≥ 0` and `α - 2τ` negative odd, contrary to the pole rule. Thus `α > 0`.
Assuming every place has a failure gives `v(W) ≤ -α` for all places; therefore
`α ≤ v(W⁻¹)` and the finite-integer trace rescaling gives `τ ≥ α`. In turn,
`value(B) = α - 2τ < 0` and is odd, giving the same contradiction. Negating the
failure predicate gives one place with **every** required precision, not
independently chosen places.

The final `p_prime : p.Prime` witness is explicit in `DetectorKit`. The proofs
evaluate the rational division and powers using `padicValRat.div` and
`padicValRat.pow`, and handle inversion by lifting the nonzero product's finite
integer valuation rather than pretending `WithTop ℤ` is an ordinary additive
group.

All three `G = 1` declarations are now closed algebraically and use only
`propext`, `Classical.choice`, and `Quot.sound`. Authentic trace/place
instantiation and the `G > 1` disjunction remain distinct future work.

## 2. New exact E364 result: powerfulness and unit defect

The independent `PowerfulBridge.lean` stress build exposed what the full proof
actually needs:

- If `T = D*s²` with `D` squarefree, the valuation equation splits as
  `v_p(T) = v_p(D) + 2 v_p(s)`. Consequently `D ∣ s` exactly excludes prime
  exponent one in `T` (apart from zero).
- Splitting that product condition back to individual factors requires
  coprimality: `2` fails no-exponent-one, while `2*2=4` passes it.
- The three consecutive source factors have pairwise-coprime hypotheses, so
  they inherit the product condition when all three terms divide their maximal
  consecutive gcds appropriately.

The promoted production declarations are:

- `powerful_terms_iff_D_dvd_s`;
- `powerful_terms_iff_defect_eq_one`;
- `powerful_terms_iff_twoD_dvd_two_s`.

They compiled without proof holes and their axiom reports contain only the
ordinary foundational axioms. This discharges the powerfulness and **unit**
defect target. It does **not** close:

- `defect_eq_prod_valuation_one`, identifying that unit defect with the product
  of primes whose total exponent is exactly one; or
- `markedKummerProfile_eq`, retaining the ordered squarefree-kernel class.

The main seven-module verification now has 28 audited declarations with only
`propext`, `Quot.sound`, and `Classical.choice`. The original six-module result
was not silently retained as evidence for the new code.

## 3. What the two other repositories establish—and what they do not

### Local E364 Lab

Ten foundational Lab modules, including the dependencies for
`PowerfulValuation`, `TripleNormalForm` and `TraceDepth`, compiled **read-only**,
into fresh outputs with Lean 4.35.0 and kernel checking enabled. Native playback
succeeded; this was not a whole-repo or independent external-kernel replay.

Direct source inspection confirms:

- the powerful triple starts at `N-1`, leaving the even `N` used in the review
  as its middle term;
- those terms must start in residue `3 mod 4`, equivalent to `N ≡ 0 mod 4`;
- consecutive terms, and in the appropriate normal forms their kernels, are
  pairwise coprime;
- adjacent and overlapping trace-depth data provide exact powerfulness
  equivalences and retain the shared middle term via their endpoints.

That supports the marked-source/joint-structure framing precisely. It is not a
proof of the elliptic marked-point identification or of the defect/Kummer
claims in this packet.

The specific historical document and object ids in the attachment
(`e364_congruent_attack_20261108.md`, `d1815fc...`, and the recorded SPROUT
head) were **not present in this checkout**. No direct read of those objects or
their later E364 attack is claimed.

### AC-code / SPROUT carrier

The local AC-code project exposes a formal SPROUT **carrier** package about
Andrews–Curtis traces, Fox spans, integer/unimodular matrices and restricted
route escape. Its own frozen spec explicitly leaves Alexander/group and
Hall/free-group bridges open.

That is not evidence of the E364 source matrix, Kummer population, healer
primes or simultaneous same-place assignment. It would be an unsafe name-based
bridge to integrate those two namespaces or to use its compilation results as
E364 evidence. No AC-code search or experiment was run.

## 4. Adversarial bounded computation and interpolation

The stress script expanded the exact scan to **100,000 even midpoints** through
`N = 200,000`, evaluating **624,635 odd-prime support events** and the full
squareclass/denominator identities at each midpoint. No powerful triple arose
in that bounded range. This is **bounded evidence only**, with no asymptotic
consequence and no E364 exclusion.

### Why the coprime hypothesis matters

The exact countercontrol is:

- `v₂(4) = 2`, so `NoExponentOne 4` holds;
- `v₂(2) = 1`, so `NoExponentOne 2` fails.

Therefore product powerfulness alone cannot infer powerfulness of arbitrary
factors. The actual pairwise-coprime source conditions are necessary, not
boilerplate.

### Why the denominator alone cannot carry the marked source

The bounded collision diagnostics found `B₂ = 2s = 2` for distinct sources
including:

| $N$ | Ordered squarefree kernels $(b_-,b_0,b_+)$ |
|---:|---|
| 2 | `(1, 2, 3)` |
| 6 | `(5, 6, 7)` |
| 14 | `(13, 14, 15)` |

Their bare denominator base is identical while the ordered kernel data and
midpoints differ. An unmarked doubled-denominator image discards information a
source-qualified argument needs. This is a concrete forgetting mechanism, not
a statement that no future curve invariant could recover it.

### Height interpolations

Exact rational Weil heights of the doubled ordinates were fitted against
`log N` on the first 500 even midpoints and tested only on later inputs through
`N = 200,000`. Results:

| Quantity | Intercept | `$log N$` coefficient | Train RMSE | Holdout RMSE | Holdout `$R^2$ |
|---|---:|---:|---:|---:|---:|
| $h(x(2P_N))$ | 0.045418 | 3.992580 | 0.019565 | 0.038541 | 0.9998918 |
| $h(y(2P_N))$ | -0.086429 | 6.014095 | 0.030468 | 0.073077 | 0.9998271 |

The fit is compatible with the expected polynomial-in-ordinate growth. It does
not identify a fixed carrier or fixed cyclic index, estimate any rank-dependent
constant uniformly in `D`, or give the required upper/lower height comparison
for surviving marked sources. **Good held-out fits are not a global height
theorem.** This route does not currently contradict, prove or delimit E364.

## 5. Remaining load-bearing targets

- Instantiate the actual number-field trace and prime places, prove their
  compatibility with `DetectorKit`, and generalize the completed algebraic
  `G = 1` detector to the finite-family `G > 1` disjunction.
- Finish `defect_eq_prod_valuation_one` and `markedKummerProfile_eq`, exporting
  the ordered source exactly, not merely its denominator image.
- Prove a `MarkedSource` bridge from the Lab's trace-depth/normal-form data to
  `N,D,s,kernels,P_N,2P_N`; only after that can joint local constraints be
  composed without losing source identity.
- Supply a family-uniform height/growth theorem or another complete source
  obstruction before invoking a global E364 exclusion.
- Keep the existing Selmer/Poitou–Tate, determinant-coordinate and universal
  arithmetic clearing gates visible. Nothing in this pass closes them.

No global interpolation theorem was asserted merely because the numeric fits
work well; no dropout of Kummer marking was excused by the fact that the local
elliptic equations are correct.
