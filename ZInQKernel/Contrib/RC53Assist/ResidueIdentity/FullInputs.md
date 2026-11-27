# Full transported residue pairing

## What is supplied

`FullTransport.lean` proves the complete local structure identity, including
its zero/two component. It imports the earlier checked arithmetic reduction
without changing that source.

For `X : RetainedLocalArithmetic U C D`, the new input
`h02 : RetainedZeroTwo X` identifies the retained zero/two matrix with the
original transported zero/two cochain cup. It does not identify it with a
prescribed residue table.

The principal theorem is:

```lean
theorem RetainedLocalArithmetic.hloc (h02 : RetainedZeroTwo X)
    (hU : (U : Filter ℕ) ≤ cofinite) (P : Ideal Lambda) [P.IsPrime] :
    localPairingOfMat (D.locK P) =
      transportedPairing (X.ε₀At P) (X.ε₂At P) (X.εAt P) 1 (X.JAt P)
```

The actual normalizations are:

```lean
X.ε₀At P = -X.εAt P
X.ε₂At P = X.εAt P
σ = 1
```

Both new scalars are proved nonzero. `hloc_at_conj` concludes with exactly
`conjMatrix Cn W hW P`; `hloc_at_rational_curve` uses the existing
`conjMatrix_eq_conjMatrixK` dictionary for the rational curve and its base
change. These are the full `ILStageStep.hloc` field types, not only the
general `hb11`/`h20` contract.

No value of `ILStageStep` with all its other fields, and no complete
height-one arithmetic family, is claimed.

Manuscript locations: `diophantine_zq.tex` 2723–2727, 2762–2767, 2798–2805,
3090–3096, 4385–4451, 4860–4863, and 5027–5043.

## The actual zero/two calculation

`contCup_zerotwo_eq` identifies the actual zero/two cup with the coefficient
map determined by the actual zero-cochain value. The existing normalized
coordinate is natural for this coefficient map on every two-cocycle.

`LocalArithmeticData.transport_coordinate_two` proves on every actual
local two-cocycle:

```lean
X.cM (X.transport 2 z) = X.tameScale • X.j (X.cM z)
```

It is proved by comparing `z` with the positive uniformizer cup of `cM z`.
Their difference is an actual coboundary. The actual conjugation cochain
map preserves this coboundary, and the normalized coordinate kills it.
The fundamental cup transforms by the original character pullback and
coefficient conjugation. No local pairing identity occurs in this argument.

The resulting actual local zero/two cup is:

```lean
X.cup02 x y = (X.tameScale * X.ε) * determinantForm x (X.J *ᵥ y)
```

The two/zero cup remains the earlier proved formula:

```lean
X.cup20 x y = X.ε * determinantForm x (X.J *ᵥ y)
```

Their finite matrices are taken through the retained inner limit. The
original derivative congruence gives `tameScale∞ = -1`. Thus the zero/two
normalization is `-ε`, and the two/zero normalization is `ε`. The earlier
proved one/one formula has `σ = 1`. Equality of the three fields proves the
full local pairing structure equality.

`RetainedZeroTwo.of_splitStages` derives the additional realization input
from the existing `hlift` and the original zero/two cochain trace comparison:

```lean
tr i (0, (Q i).cupL.P 0 2 2 rfl x y) = (X.stage i).cup02 x y
```

The right side is the original transported actual cup, not the requested
residue identity. This is the zero/two specialization of the original trace
transport exported by `exists_relativeSplitPair_trace_duality` once the
original coefficient and conjugation cochain dictionaries are matched.

## Genuine arithmetic inputs constructed

`GenuineInputs.lean` supplies the following constructors and arithmetic
implications on the actual local objects.

### Derivative action

`localAction_trivial_of_frobenius` uses the actual unramified factorization
of a moving label and density of Frobenius powers to prove trivial action
of the full local Galois group from exact trivial Frobenius action.

`actualStage_frobenius_trivial` applies the existing genuine finite-level
map `finLev` to the actual derivative congruence on the Tate lattice.
`actualStage_local_action_trivial` then proves trivial action on:

```lean
ResMod (locMap K S (L.label.q i))
  (Mcoef K S (B⁄K) i (alphaLev i α))
```

The finite character's open kernel is proved by `alphaLev_openKernel`.
These results do not assume trivial local action on `M_i`.

This label corollary applies to a supplied continuous coefficient character
on a fixed support. It does not identify every varying-conductor manuscript
stage with the reduction of one fixed character. The generic unramified
Frobenius implication is also available for arbitrary actual finite-stage
modules.

### Extra root precision and tame generators

`fixedRoots_of_residue_congruence` proves that residue cardinality one
modulo `n` fixes the `n`-th roots of unity under the full local Galois group.
It uses actual arithmetic Frobenius, its cyclotomic power formula, inertia
fixation, and their topological generation of the local Galois group.

`label_residue_extra_precision` derives the necessary local residue
congruence from the exact inert-prime integer condition:

```lean
(2 * (2 ^ i)) ∣ L.primes.ell i + 1
```

`orientation_kummer_doubleLift` constructs a continuous additive
uniformizer-character lift for every already chosen orientation. It takes
a square root of the existing uniformizer root; the original root and
inertia generator are retained. Exact two-power order is proved for the
larger Kummer value, and the logarithm reduces exactly. The arithmetic
unramified character lift is the existing `exists_unramified_doubleLift`.

The integer extra-precision condition is a genuine (H12) arithmetic input.
The current compatible-label record supplies its own stage precision, not
a new next-precision assertion; this file does not infer the extra bit from
a weaker stored congruence.

### Scalar twist action and original local trace

`local_cyclotomic_eq_one` compares the actual decomposition embedding and
the original global root frame. `actualScalar_local_action_trivial` proves
trivial action on the actual localized `Tate1 (Acoef i) hμ` from fixed local
roots; this coefficient module is not replaced by an unrelated trivial
representation.

`retractCoordinate_spec` constructs a local degree-two coordinate on a
coefficient direct summand of the rank-two actual module. Consequently the
scalar twist coordinate is constructed from the same rank-two coordinate
and coefficient frame. Both exactness and positive normalization are
proved. `retractCoordinate_brauerFormula` proves the actual Brauer-invariant
formula on every two-cocycle for the constructed coordinate.

`ActualLocalCore.scalar_brauerFormula` applies this to the actual scalar
coefficient module with its canonical residue-module dictionary.
`ActualLocalCore.τ` is its actual scalar Brauer trace;
`ActualLocalCore.trace_spec` proves boundary vanishing and surjectivity on
two-cocycles, without a separately postulated scalar trace.

An already selected original local trace can be kept instead:
`ActualLocalCore.originalTrace_factor` proves its exact unit factor relative
to the constructed arithmetic trace on every two-cocycle.
`toArithmeticWithOriginalTrace` retains it and constructs all other local
coordinate, character-lift, and retraction data.

### The normalized local retraction

`exists_actualLocalCore` uses the existing
`exists_stageOrientedLocalRetraction` producer and retains its actual
coefficient basis, primitive-root dictionary, normalized coordinate,
Brauer formula, and exact cochain retraction.

`exists_actualLocalCore_of_label_precision` constructs this core from the
actual compatible arithmetic label and these remaining local hypotheses:

```lean
h2 : (2 : 𝓞 K) ∉ (L.label.q i).asIdeal
hdiv : (2 * (2 ^ i)) ∣ L.primes.ell i + 1
hfin : ∀ n, Module.Finite (ResidueField (Acoef i))
  (residualCohomologyAt Cq n)
hdim : ∀ n, Module.finrank (ResidueField (Acoef i))
  (residualCohomologyAt Cq n) = splitLocalRank n
```

Here `Cq` is the actual continuous local cochain complex, and the split
residual ranks are `2,4,2` in degrees `0,1,2`, and zero elsewhere.

The core is not an assumption of any residue pairing table.

## Local conjugation pullback reduced to root equations

`RootPullback.lean` constructs the algebraic conjugation homomorphism from
an algebraic representative `a` restricting to the coefficient-field
automorphism `κ`. It proves the Kummer pullback formula from:

```lean
ha : ∀ x : F, a (algebraMap F (AlgebraicClosure F) x) =
  algebraMap F (AlgebraicClosure F) (κ x)
hfix : a β = β
hcyc : ∀ ζ : AlgebraicClosure F, ζ ^ n = 1 → a ζ = ζ ^ r
```

The resulting exact logarithm formula is:

```lean
kummerLog hβ hβ0 hprim (conjugateHom a κ ha g) =
  (r : ZMod n) * kummerLog hβ hβ0 hprim g
```

`coefficient_kummerLog_conjugate` gives its full coefficient-ring version.
Thus the tame-character input can be supplied from actual algebraic root
fixation and cyclotomic power facts. No cup-product pairing is a hypothesis
of these statements.

This file does not identify an arbitrary algebraic representative with the
already prescribed local rational Frobenius, prove continuity of that
identification, or silently align an arbitrary produced uniformizer root
with a prescribed representative. Those are still arithmetic dictionary
facts to instantiate. The unramified pullback and the correct inverse
residue-size orientation must be retained as well.

## The remaining boundary, precisely

To construct the actual retained record and install full `hloc` on the
height-one main path, the following still must be matched.

1. The actual stage characters and supports must be identified with the
   finite coefficient systems of the intended derivative family. The
   fixed-character label corollary is not asserted for an unidentified
   varying-conductor family.
2. Oddness and the exact larger integer precision of (H12) must be supplied
   for each actual derivative prime. Independent local residual finiteness
   and the `2,4,2` rank table are still inputs to the normalized retraction
   producer.
3. The local representative must be identified with the intended rational
   Frobenius/conjugation action and the produced uniformizer/root frame.
   Its unramified and tame pullback must have the displayed scale. The root
   power reduction is proved; the actual representative/root dictionary is
   not presumed.
4. The produced finite coefficient frame must be identified with the
   retained Tate frame. This supplies `J_lift`; the rational-curve fibre
   comparison with `conjMatrix` is already proved from the integral matrix
   identification.
5. The retained matrices must be the original cochain trace cups in all
   three bidegrees. The existing `hlift` and the original trace transport
   provide the stated route; their actual paired-stage coefficient and
   conjugation comparisons still need matching. No equality with a
   prescribed `ε e₂` table remains among the inputs.
6. The scalar normalizations and tame scales must use the retained lifts,
   with their derivative congruences. The original local trace may be kept
   with its proved unit scaling instead of replaced by a canonical trace.
   Compatibility with the original compact all-place trace is not inferred
   from an arbitrary `H³` isomorphism.

Detection, global retained duality, and finite/singular side isomorphisms
are unchanged inputs of the complete stage-step construction. The full
residue identity itself is now a theorem once these original arithmetic
realization data are matched.
