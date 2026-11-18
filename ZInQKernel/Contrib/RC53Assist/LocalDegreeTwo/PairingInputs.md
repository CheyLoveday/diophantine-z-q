# Normalized local coordinates and the retained split-stage pairing

## Scope

`NormalizedPairing.lean` is a standalone expanded edition. It includes the earlier
coordinate declarations and the pairing transport, so it should be imported in place
of the earlier coordinate and transport modules, not alongside them. The earlier
`Normalized.lean`, its statement audit, and its requirements document are unmodified.

The supplied producer is `exists_stagePairing_trace`. Its local complex is the actual
continuous cochain complex at the derivative prime, with the actual localized module
`ResMod (locMap K S q) (Mcoef K S W i α)`. The source global complex is the old-condition
Selmer complex on the enlarged support; old places are absorbed before replacing the
single retained local complex. The output has exactly the same-condition
`splitSelData` type consumed by `exists_retained_of_stageInputs`. The consumer-shaped
entry point forgets the arithmetic witnesses. Use `exists_stageOrientedLocalRetraction`
and `exists_relativeSplitPair_trace_duality` together when the coordinate, primitive-root
dictionary, contraction, and local trace formula must be retained.

This is a conditional arithmetic producer, not an unconditional instance of all of
the manuscript's stage data. The independent inputs still needed for that instance
are stated below. No split pairing, split trace, local retract, or final split global
duality is assumed by the producer.

## Arithmetic coordinate: strengthened entry points

The Kummer--Brauer injectivity elimination was found in an independent review.
`compKummerToBr_injective` proves it by Hilbert 90 when the coefficient exponent is a
unit in the local field. In a characteristic-zero completion this condition is
automatic. Both `exists_stageCoordinate_without_hKB` and the stronger
`exists_stageCoordinate_with_brauer` have no Kummer--Brauer injectivity hypothesis.
The older conditional declarations are retained for compatibility.

The stronger entry point returns the primitive-root dictionary `η`, the orientation
`D`, and the coordinate `c₂`, with:

- `LocalDegreeTwoCoordinate c₂`;
- `LocalDegreeTwoNormalized c₂ u κ`, where `u` is the arithmetic unramified character
  and `κ` is the exact Kummer logarithm of `D.root`;
- `StageBrauerCoordinateFormula W i α q η hμ htriv c₂`;
- the equality identifying `η(1)` with `kummerVal D.root D.inertia`.

The invariant formula holds on every actual continuous two-cocycle, not merely on
the fundamental class. For every residue-linear coefficient functional `f`, it is

```lean
ZMod.toRatAddCircle n (f (c₂ z)) =
  invMap F (kummerToBr n
    (scalarKummerEquiv η hμs (kerToH2 ⟨scalarCochain f z, hzScalar⟩)))
```

Here `F = q.adicCompletion K`, `n = 2 ^ i`, and `hzScalar` is proved from the cocycle
identity of `z` and the trivial derivative action. The public generic definition is
`BrauerCoordinateFormula`; the stage definition supplies the canonical residue-module
and local-action dictionaries.

The normalized mixed cup has invariant `1 / 2^i`, with the unramified character first.
There is no unexplained unit multiplying this arithmetic coordinate.

`acoef_eq_stageA` proves the ring identity by reflexivity. There is no remaining ring
identification between `Acoef i` and `ZInQ.Manuscript.RC.Limits.StageA i`.

## The same orientation in degrees one and two

`stageOrientation_tameCoord_surjective` realizes every pair of degree-one coefficient
values using exactly `D.frobenius` and `D.inertia`. It constructs continuous cocycles
from the same two additive characters:

```lean
F g = u g • x + κ g • y
```

The character values are `(1, 0)` at `D.frobenius` and `(0, 1)` at `D.inertia`.
`exists_stageSplitProjection` uses the no-injectivity corollary directly to construct
the projection. `exists_stageOrientedLocalRetraction` uses the stronger invariant
entry point. Both use this same choice of `D`.

The projection components are exactly:

```lean
p₀ = e.toLinearMap.comp (evalZero A M)
p₁ = (e.prodCongr e).toLinearMap.comp
  ((evalOne A M D.frobenius).prod (evalOne A M D.inertia))
p₂ = e.toLinearMap.comp c₂
```

The coefficients are zero outside degrees zero, one, and two. Trivial action proves
`p₁ d₀ = 0`, and the coordinate proves `p₂ d₁ = 0`.

This does not silently impose a previously selected Frobenius lift or primitive root.
If a fixed global dictionary is required, the prescribed-dictionary local interface
`normalizedCoefficientCoordinate_spec` remains available. Otherwise the consumer
must retain the returned `D` and `η`. A comparison with a prescribed label lift must
be proved, not asserted.

## The local retract is constructed

`exists_orientedLocalRetraction` obtains the graded finite free model from the proved
inner-limit construction. Surjectivity on cocycles, together with the independent
residual ranks, makes the model-to-coordinate comparison degreewise bijective.
Relabeling the model gives a cochain isomorphism; `specifiedCoordinateRetraction`
then changes the projection to the exact maps above.

The contraction correction is

```lean
h' = h - i ∘ p ∘ h
```

and all identities are proved: `p i = 1`, `1 - i p = d h' + h' d`, `h'^2 = 0`,
`h' i = 0`, and `p h' = 0`. An unspecified cohomology equivalence is not being used
as a substitute for the paired cochain transport.

At the actual stage, nilpotence of the coefficient maximal ideal is proved by the
existing coefficient-ring theorem. Flatness of actual local cochains is proved from
the rank-two full coefficient basis and compactness of the actual local Galois group.
These are not additional arithmetic hypotheses of `exists_stagePairing_trace`.

## Pairing, same-condition isotropy, and trace

`RetainedPlaceInput` supplies only the original retained-place cup, its localization
compatibility, and its actual same-condition isotropy data. The old paired diagram
supplies the global cup. The relative global cup is the proved cup on the old Selmer
complex, with target the old compact scalar cone.

The local replacement uses the tensor-contraction homotopy

```lean
H(x, y) = P(h x, y) + (-1)^a P(i p x, h y)
```

and proves its full bilinear coboundary identity. The cup target is a homotopy
pullback, so compatibility with localization is exact on cochains. The retained
isotropy homotopy becomes the original primitive minus `H(ι u, ι v)`. It is not
replaced by strict/relaxed orthogonality.

`relativeTargetFlatten` turns the relative compact scalar tuple `((e, zOld), zq)`
into `(e, (zOld, zq))`. The relative trace is the original all-place trace composed
with this chain map. `relativeTrace_kills` proves its boundary identity.
`replacementTrace` then pulls it through the local replacement, and
`replacementTrace_kills` proves the exact `htr` required by the consumer.

The relative pairing producer `exists_relativeSplitPair_trace_duality` returns the
exact local trace formula

```lean
tr (0, Q.cupL.P a b 2 h u v) =
  trAll (0, 0, Pq.P a b 2 h
    (R.retract.i.f a a rfl u) (R.retract.i.f b b rfl v))
```

Thus the local matrix is the trace of the actual transported original cup, not a
chosen perfect pairing on vector spaces of the same size.

## Global-duality transport

`globalComparisonHomotopy` explicitly compares the split global-duality map with
the original map pulled back along the compact comparison. The compact comparison
is a proved normalized retract. Its dual is a proved retract as well.
`replacementGlobal_quasiIso` therefore transports original global duality; it does
not assume the final split quasi-isomorphism.

For the one-place relative source, `relativeGlobal_map_eq` identifies its global
duality map with the all-place Selmer duality map under the proved relaxed section
and strict flattening. `relativeGlobal_quasiIso` derives it from original all-place
global duality and independent local orthogonality at the old conditions. The
auxiliary strict/relaxed factors are used only for this global-duality proof. The
retained same-condition isotropy is still the separate `RetainedPlaceInput`.

`exists_actualStageSource_trace_duality` uses `exists_stageTrace` and
`stageGlobalDuality` on the actual Weil-paired stage coefficient systems. The
second-system cochain comparison preserves the actual condition image and has
proved compact quasi-isomorphy when its global and local maps are bijective.
Passing this native source to the partitioned presentation requires the actual
support, coefficient, and conjugation cochain comparisons.

## Exact inputs that remain for the arithmetic instance

### 1. Derivative action and fixed roots

Besides the odd-prime and full-torsion inputs, the coordinate still needs:

```lean
htriv : ∀ (g : Gloc K q)
  (m : ResMod (locMap K S q) (Mcoef K S W i α)), g • m = m

hμ : ∀ (g : Gal(AlgebraicClosure (q.adicCompletion K)/q.adicCompletion K))
  (ζ : AlgebraicClosure (q.adicCompletion K)),
  ζ ^ (2 ^ i) = 1 → g ζ = ζ
```

They must be derived from the actual derivative label and the coefficient reduction
with its twist. Neither is a degree-two coordinate or its normalization.

### 2. Residual local cohomology

Let `Cq := actualStageLocalCx W i α q`. The actual-stage producer takes:

```lean
hfin : ∀ n, Module.Finite (IsLocalRing.ResidueField (Acoef i))
  (residualCohomologyAt Cq n)

hdim : ∀ n, Module.finrank (IsLocalRing.ResidueField (Acoef i))
  (residualCohomologyAt Cq n) = splitLocalRank n
```

`splitLocalRank` is `2, 4, 2` in degrees `0, 1, 2`, and zero elsewhere. These are
independent local finiteness and residual-dimension facts. They do not specify a
coordinate, an orientation, a pairing, or the final duality map.

### 3. Actual paired source and retained condition

The old paired diagram and the retained cochain data have types:

```lean
Dold : SelData A
Qold : SelPairData Dold Dold
rq : GHom Dold.G Cq
sq : GHom Qold.E Tq
ιq : GHom Uq Cq
Pq : GPair Cq Cq Tq
V : RetainedPlaceInput Dold Qold Cq Tq Uq rq sq ιq Pq
```

`Pq` must be the actual Weil cup after the prescribed conjugation/coefficient
transport. `V.compat` is the exact restriction-of-cup identity. `V.hU` and
`V.isotropy` are the original same-condition self-cup primitive and its full
Leibniz identity. The record's exact types are printed in the statement audit.
`retainedInput_of_conditionCupZero` constructs it with zero primitive when the
actual condition cup table is zero on cochains.

This is not supplied by the normalized mixed cup alone. The finite and singular
self-cups, the reversed mixed cup, and the degree-zero/degree-two adjoints must be
retained in the actual arithmetic data. At two-power precision a route for the
singular self-cup uses the additional arithmetic fact

```lean
∃ z : q.adicCompletion K, z ^ (2 ^ i) = -1
```

Fixed `2^i`-th roots alone do not assert this stronger fact. The derivative label's
extra residue precision and Hensel argument may supply it.

A fully relaxed same-condition datum is not a workaround.
`fullDegreeOne_selfPair_obstruction` proves that, when condition cocycles surject
onto the full local degree-one space, a nonzero mixed trace cup is incompatible
with same-condition isotropy, even with a nonzero primitive.

### 4. Original trace and independent global/local duality

For the partitioned original scalar target the inputs are:

```lean
trAll : (coneCx (allTargetRes Dold Qold Tq sq)).X 3 →ₗ[A] A
htrAll : ∀ z,
  trAll ((coneCx (allTargetRes Dold Qold Tq sq)).d 2 3 rfl z) = 0

hG : QuasiIso (GHom.toCC (globalDualityMap Qall trAll htrAll))
hL : QuasiIso (GHom.toCC (localDualityMap Qall trAll htrAll))
```

Here `Qall := allPlacePair Dold Qold Cq Tq Uq rq sq ιq Pq V` has the original
global complex and the full old-plus-retained local complex. It is not the final
one-place split datum. Its global statement is the native `stageGlobalDuality`
statement after the actual cochain comparisons. Its local statement is independent
old-condition orthogonality, with the added relaxed/strict factor contractible.
The relative Selmer-duality argument then proves the final global-duality statement.

### 5. Identification with the manuscript's retained local form

The producer exports the actual source trace cup. Identifying it with the specific
retained `ε e₂(x, J y)` form still needs the actual Weil/conjugation dictionary and
normalization of the original trace against the returned primitive-root dictionary.
An arbitrary `H³` trace isomorphism does not by itself fix its unit scaling.

An exact cochain comparison can be stated as follows. Let `Bret` be the prescribed
retained bilinear table, and let `p` be the returned local projection:

```lean
Bret : ∀ (a b : ℤ), a + b = 2 →
  (splitLocalComplex A).X a →ₗ[A] (splitLocalComplex A).X b →ₗ[A] A

hB : ∀ (a b : ℤ) (h : a + b = 2)
  (x : Cq.X a) (y : Cq.X b),
  Cq.d a (a + 1) rfl x = 0 → Cq.d b (b + 1) rfl y = 0 →
  trAll (0, 0, Pq.P a b 2 h x y) =
    Bret a b h (p.f a a rfl x) (p.f b b rfl y)
```

`Bret` must be the actual retained table from the Weil pairing and `J`, not an
arbitrary perfect form. This comparison is on original local cocycles and does not
assume a split Selmer pairing or its global duality. It is not proved here.

## Verification and delivery

All source declarations are checked with the prescribed single-file command.
No earlier source file is modified, and no commit or repository update is made.
The expanded source contains no proof gaps, new axioms, evaluation commands,
macros, syntax, or notation declarations. Its maximum heartbeat setting is
600000, and every line is at most 100 characters.

`PairingStatementAudit.txt` contains 123 source theorem statements and 225
public declarations and input projections, with 225 axiom reports. The axiom
union is exactly `propext`, `Classical.choice`, and `Quot.sound`; two declarations
are axiom-free. No pretty-printed statement is truncated. The audit uses scratch
declarations only; no diagnostic commands remain in the source edition. The detailed source and audit are the deliverable, not an
unconditional claim that the remaining arithmetic inputs have been supplied.
