# Retained residue pairing: arithmetic reduction

## Result and scope

`Arithmetic.lean` proves the general `hb11`/`h20` route for the retained local
pairing. It does not assume either the requested residue identity or
perfectness of the desired split local pairing.

The principal exports are:

- `RetainedLocalArithmetic.residue_inputs`;
- `RetainedLocalArithmetic.certificate`;
- `RetainedLocalArithmetic.certificate_at_conj`;
- `RetainedLocalArithmetic.certificate_at_rational_curve`;
- `RetainedLocalArithmetic.toStepData`.

This is a conditional arithmetic reduction, not an unconditional construction
of every derivative-prime datum and not a discharge of the full
`ILStageStep.hloc` structure equality. The general route needs only the
one/one residue identity and the two/zero adjoint. No assertion about the
zero/two component is used.

Manuscript locations: `diophantine_zq.tex` 2723–2727, 2762–2767, 2798–2805,
3090–3096, 4385–4451, 4860–4863, and 5027–5070.

## The calculation that replaces the residue-table hypothesis

At a finite coefficient stage let `u` be the arithmetic unramified character,
`κ` the uniformizer character, and `cM`, `cN` the normalized degree-two
coordinates for the rank-two module and scalar twist. Both coordinates use
the same orientation.

1. The mixed product `(g,h) ↦ u(g)κ(h)m` has coordinate `m`.
2. Its reversed product has coordinate `-m`. The primitive is the pointwise
   product `(g ↦ u(g)κ(g)m)`; its differential is the negative sum of the two
   mixed products.
3. A continuous additive character lifted to `ZMod (2*n)` has a coboundary
   square after reduction to exponent `n`. The primitive uses
   `choose(χ(g).val, 2)`. Its cross term is the product of the two reduced
   character values. There is no division by two in the coefficient ring.
4. Consequently both self-axis cup terms vanish at the retained precision,
   including the singular self-cup at two-power coefficients. This is not
   inferred from residual alternatingness.
5. Every original local trace killing coboundaries factors on every actual
   two-cocycle through the normalized scalar coordinate. Its multiplier is
   its value on the oriented fundamental cup. Surjectivity on two-cocycles
   makes that multiplier a unit.
6. Alternation and bilinearity of the original coefficient Weil pairing give
   its rank-two determinant formula. Original coefficient perfectness makes
   its basis multiplier a unit.
7. If the actual local pullback preserves `u` and scales `κ` by `s`, while its
   coefficient action has matrix `J`, the trace of the actual transported
   one/one cup is

   ```text
   ε * (s * e₂(xF, J yS) - e₂(xS, J yF)).
   ```

   The trace of the actual two/zero cup is

   ```text
   ε * e₂(x, J y).
   ```

   Here `ε` is the product of the original trace multiplier and original
   coefficient Weil multiplier, not an assumed local pairing table.

The relevant statements are `contCup_normalized_formula`,
`coefficientMap_coordinate`, `trace_cycle_formula`, `traceScale_isUnit`,
`coefficientWeil_coordinates`, `weilScale_isUnit`, and
`LocalArithmeticData.cup11_formula`/`cup20_formula`.

Passing the finite matrices through the retained limit is proved entrywise.
The retained congruence `s_i + 1 ∈ stageIdeal i` gives `s∞ = -1`. The actual
Tate identities `J² = 1` and `det J = -1` give
`e₂(x,Jy) = e₂(y,Jx)`. Thus the result is exactly

```lean
∀ x y, (localPairingOfMat (D.locK P)).b11 x y =
  -(switchPairing (X.εAt P) 1 (X.JAt P) y x)
```

and

```lean
Function.Bijective (localPairingOfMat (D.locK P)).b20
```

The normalization `X.εAt P` is nonzero because the retained normalization
is lifted as units with their inverses. Mere nonzero finite values are not
used to infer nonvanishing of a limit.

## Actual objects, not an unrelated split example

`actualLocalArithmetic` instantiates the data on:

```lean
G := Gloc K q
M := ResMod (locMap K S q) (Mcoef K S W i α)
N := ResMod (locMap K S q) (Tate1 (Acoef i) hμ)
```

It fixes the coefficient pairing to `weilA W hμ (Acoef i)` and the coefficient
conjugation to `conjBC Cn W hW (Acoef i)`. It computes the conjugation matrix
in the prescribed coefficient frame. Alternation and perfectness of this
actual Weil pairing are proved here from the existing torsion Weil pairing;
they are not constructor hypotheses.

`actualCup_eq_native` identifies the same-module presentation of the cup
with the original cup against `Mcoef ... (charInv α)` after the coefficient
map. Its hypotheses concern trivial derivative actions on the two actual
coefficient systems, not the desired local table.

For curves over the rationals, `certificate_at_rational_curve` uses the
existing `conjMatrix_eq_conjMatrixK` theorem. Its matrix identification input
is

```lean
X.J = (conjMatrixK B Cn).map (algebraMap ℤ_[2] Lambda)
```

and its conclusion uses exactly `conjMatrix Cn (B⁄K) hW P`.

## Precisely typed inputs still to instantiate

The full types, quantifier order, instances, and axiom reports are in the
statement audits. The remaining input groups are the following.

### Local derivative actions and coordinates

The actual rank-two and scalar-twist actions must be trivial at the retained
stage:

```lean
∀ (g : Gloc K q) (m : actualM W i α q), g • m = m
∀ (g : Gloc K q) (m : actualN i q hμ), g • m = m
```

The original inverse coefficient system must also have trivial local action
when applying `actualCup_eq_native`.

The same orientation `Dt` must be retained for the degree-one evaluations,
the two normalized degree-two coordinates, and the specified local
retraction. The coordinate inputs are `LocalDegreeTwoCoordinate cM/cN` and
`LocalDegreeTwoNormalized cM/cN u κ`. The rank-two coordinate and specified
retraction are the objects produced by
`exists_stageCoordinate_with_brauer` and
`exists_stageOrientedLocalRetraction` in `NormalizedPairing.lean`. The scalar
coordinate is the corresponding finite-coefficient extension of the scalar
Brauer invariant. Independent local residual finiteness and dimensions are
inputs of that existing retraction producer, not local pairing identities.

A separately chosen Frobenius lift or root frame is not silently identified
with `Dt`.

### Additional two-power root precision

The two characters must have continuous additive lifts to twice the retained
exponent. For the arithmetic unramified character this is proved
unconditionally in `Characters.lean` by
`exists_unramified_doubleLift`.

For the uniformizer character, `exists_kummer_doubleLift` reduces the lift to
these actual algebraic facts, with `n = 2^i`, `F = q.adicCompletion K`, and
`a` the chosen uniformizer:

```lean
hγ : γ ^ (2*n) = algebraMap F (AlgebraicClosure F) a
hγ0 : γ ≠ 0
hζ : IsPrimitiveRoot (kummerVal γ σ) (2*n)
hμ : ∀ (g : Gal(AlgebraicClosure F/F)) (ζ : AlgebraicClosure F),
  ζ ^ (2*n) = 1 → g ζ = ζ
```

The retained root is `γ^2`. Its Kummer logarithm is proved to be exactly the
reduction of the double-exponent logarithm. These are root and Galois-action
facts, with no cup-product or residue-table assertion in their hypotheses.
The larger fixed-root statement, and compatibility with the actual label,
must come from the extra precision in (H12) and the local root construction.
Fixed roots only at exponent `n` are not substituted for this stronger fact.

### Actual local conjugation and trace

The actual local representative `θ` must obey the character pullback facts:

```lean
∀ g, Dt.unramified (θ g) = Dt.unramified g
∀ g, algebraMap (ZMod (2^i)) (Acoef i) (Dt.kummer (θ g)) =
  s * algebraMap (ZMod (2^i)) (Acoef i) (Dt.kummer g)
```

The original local trace `τ` must kill coboundaries and be onto on actual
two-cocycles:

```lean
∀ a, τ (((contCochains R G N).d 1 2).hom a) = 0
∀ r : R, ∃ z, ((contCochains R G N).d 2 3).hom z = 0 ∧ τ z = r
```

These are original local-invariant facts. No equality of the trace of a Weil
cup with a prescribed determinant form is assumed. Its unit scaling is
extracted and proved here.

### Retained source identification

`RetainedLocalArithmetic.of_splitStages` takes the exact existing local lift
shape:

```lean
∀ i, i ≠ 0 → ∀ a b,
  (D.loc a b i).map (stageMap i) = stageLocMat (Q i) (tr i) a b
```

and the original cochain trace comparisons:

```lean
tr i (0, (Q i).cupL.P 1 1 2 rfl x y) = (Y i).cup11 x y
tr i (0, (Q i).cupL.P 2 0 2 rfl x y) = (Y i).cup20 x y
```

Their right sides are actual transported cochain cups, not prescribed
`ε e₂` forms. The original trace transport is the formula exported by
`exists_relativeSplitPair_trace_duality`; the original Weil and second-system
cochain dictionaries must be matched to it. The new constructor proves the
retained matrix realization fields from these comparisons and `hlift`.

The scalar normalization and tame scale need their retained lifts, and the
finite coefficient conjugation matrices need the actual Tate-basis lift.
The retained derivative congruence is

```lean
∀ᶠ i in (U : Filter ℕ), s i + 1 ∈ stageIdeal i
```

These inputs identify the original arithmetic diagram and its retained
precision. None is the requested residue pairing identity.

## Integration route and boundary of the result

1. Retain the actual normalized coordinate/retraction witnesses and root
   orientation from the local arithmetic producer.
2. Instantiate `actualLocalArithmetic` with the actual derivative action,
   double-exponent characters, original local trace, and local pullback.
3. Use `of_splitStages` with the existing `hlift` and original cochain trace
   transport.
4. Use `residue_inputs` to supply `hb11` and `h20`, then `certificate` or
   `certificate_at_rational_curve` for the general retained certificate.
5. Use `toStepData` for `InnerLimitStepData`; detection and finite/singular
   side isomorphisms remain the same independent inputs.

No existing source is edited. No full `ILStageStep` value, zero/two residue
component, final arithmetic family, or unconditional proof of Theorem 5.3 is
claimed. The actual derivative-label and original paired-stage witnesses
listed above still need to be instantiated. The contribution removes the
local residue table and its perfectness from that remaining input list.
