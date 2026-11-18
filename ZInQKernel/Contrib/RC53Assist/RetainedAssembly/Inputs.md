# Retained inner-limit assembly

Manuscript: `diophantine_zq.tex`, lines 4391–4451 and 4976–5135.

## Entry points and scope

The namespace is `ZInQ.Contrib.RC53Assist.RetainedAssembly`.

The principal statement is:

```lean
theorem assemble_inner_limit (p : ArithmeticPrints K)
    (hK : IsTotallyComplex K) (hS₀ : S₀.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (a : ArithmeticInputs F O R width)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (Cn : ActualConj K S₀) (hW : W.map (Cn.κ : K →+* K) = W) :
    Nonempty (AssembledLimit a U hU Cn hW)
```

The implicit setting consists of a number field `K`, an elliptic curve `W`,
`HasFullTwoTorsion K S₀ W`, characters
`α : ∀ i, GKS K S₀ →* (Acoef i)ˣ` with open kernels, an actual stage family `F`,
original old-duality data `O`, a fixed-support reference family `R`, and a natural
number `width`.

`AssembledLimit` contains the produced stage projections, pairings and traces;
a retained complex `C`; retained pairing/localization `D`; retained inverse maps
and homotopies `E`; `C.low = 0`; `C.high = 3`; a produced uniform rank bound;
actual residual-rank identities on one ultrafilter-large set; the exact local
matrix lifts at every positive stage; and conditional fibre certificates on
**that same** `C` and `D`.

`exists_certificate_actual_stages` directly instantiates
`exists_certificate_of_stageInputs`. The principal statement directly
instantiates `exists_retained_of_stageInputs` and derives its certificates from
the returned retained homotopy-inverse data, so its certificate does not use a
second retained complex.

`detect_on_assembled_finite_fibre` instantiates
`produce_arithmetic_detection` on the finite side of the produced diagram.
It produces the partner, actual kernel sequence, nonidentity representatives
on an ultrafilter-large set, and detecting determinant. A determinant is not
an input.

This is a **conditional arithmetic assembly**, not an unconditional arithmetic
instance and not the completion of Theorem 5.3.

## Actual stage choices

Write, exactly as in the source:

```lean
Sᵢ := F.support i = insert (F.q i) S₀
γᵢ := F.character i = characterAfterSupport (F.inclusion i) i (α i)
Mᵢ := F.coefficient i = Mcoef K Sᵢ W i γᵢ
Dᵢ := F.datum i
Gᵢ := F.globalCx i = selCx Dᵢ
Cqᵢ := F.localCx i = actualStageLocalCx W i γᵢ (F.q i)
kᵢ := IsLocalRing.ResidueField (Acoef i)
```

`Dᵢ` is the actual `selData` with global group `GKS K Sᵢ`, coefficient module
`Mᵢ`, and local-condition index `Places K S₀`. Its local complexes and restrictions
use `locMap K Sᵢ v.1`. Only the **old** local conditions are absorbed. The new
place is not inserted a second time in the compact cone.

The retained restriction is fixed, not arbitrary:

```lean
F.restriction i : GHom Dᵢ.G Cqᵢ
```

It is `natHom (resCochains (locMap K Sᵢ (F.q i)))`. The split localization is

```lean
ghomComp (ghomComp (projG Dᵢ) (F.restriction i)) projectionᵢ
```

The native local coefficient type is exactly

```lean
ResMod (locMap K Sᵢ (F.q i)) (Mcoef K Sᵢ W i γᵢ)
```

Thus the normalized pairing supplier is applied directly at its native type.
No arithmetic transport of the different `ILStageStepActual` local coefficient
module is implemented here. `Acoef i` and `StageA i` are definitionally equal;
there is no ring-identification input.

At stage zero, the zero ring supplies the flatness and quasi-isomorphism. The
pairing has zero scalar target and zero trace. No positive-stage arithmetic
input is requested at zero.

## Printed arithmetic statements

The exact type of the printed input is `ArithmeticPrints K`. Its fields are:

```lean
localFinite         : MilneLocalFiniteness
globalFinite        : MilneGlobalFiniteness
globalDimension     : MilneADT_I_4_10_totallyComplex
localDimension      : MilneLocalDimensionTwo
localKummer         : MilneLocalTateDualityKummerCharZero
localDuality        : NekovarProp524 K
globalDuality       : NekovarProp543T K
unramifiedDuality   : NekovarProp756 K
traces              : NekovarFiniteTraces K
```

These are explicit propositions defined in the existing source, not new axioms.
The trace packet supplies the original boundary-killing trace and its degree-three
isomorphism. The original global duality is obtained from the generic finite
Nekovář statement with the actual coefficient pairing, coefficient finiteness,
full-torsion perfection and cyclotomic twist supplied. Local orthogonality is
assembled place by place. None of the final split traces or duality maps is
assumed.

## Remaining producer inputs, in one place

The only non-setting input record of `assemble_inner_limit` is

```lean
a : ArithmeticInputs F O R width
```

It has exactly three fields:

```lean
oldFlat         : F.NontrivialOldFlat
residualSupport : ResidualSupportControl F R width
stage           : ∀ i [NeZero i], StageArithmeticInput F O i
```

Their exact expansions follow.

### 1. Old-condition term flatness

```lean
∀ i [NeZero i] (v : Places K S₀),
  F.old i v ≠ fullAt K (F.support i) (Acoef i) (F.coefficient i)
    ⟨v.1, Or.inr v.2⟩ →
  F.old i v ≠ zeroAt K (F.support i) (Acoef i) (F.coefficient i)
    ⟨v.1, Or.inr v.2⟩ →
  ∀ n : ℤ, Module.Flat (Acoef i) ((F.old i v).U.X n)
```

The full and zero cases are supplied. `StageFlat.flat_selmerCochains` requires
free local-condition terms; it does not prove term flatness of arbitrary Kummer
or old finite/singular conditions. Nilpotence converts the remaining term-flatness
input to freeness before applying that theorem.

### 2. Varying-support residual comparison

`ResidualSupportControl F R width` has exactly:

```lean
map : ∀ i [NeZero i] (n : ℤ),
  residualCohomologyAt (F.globalCx i) n →ₗ[kᵢ]
    residualCohomologyAt (R.globalCx i) n ×
      (Fin (extraRank width n) → kᵢ)

injective : ∀ i [NeZero i] (n : ℤ), Function.Injective (map i n)
```

Here `extraRank width n` is `width` in degrees zero through three and zero
elsewhere. The reference complex is the exact standard-old complex

```lean
selCx (actualSelData (fun _ h => h) W i (α i)
  (fun v _ => standardOldAt K S₀ (Acoef i)
    (MinS (fun _ h => h) W i (α i)) v
    (R.label i v) (R.curve v) (R.level i)
    (R.iota i v) (R.equivariant i v)))
```

Its residual finiteness is supplied by
`actualStageSelmer_residualCohomologyFinite`, with the full, zero and Kummer
condition inputs discharged. Its range and uniform bound are supplied by
`standardOld_producerBounds`.

The comparison proves actual residual finiteness, actual range `[0,3]`, and a
bound equal to the reference bound plus `width`. Neither `hres`, `hbdd`, nor `hB`
is an extra producer hypothesis.

**Why a comparison remains:** the three supplied family-bound entry points have
one fixed Selmer support. Their complexes are not the old-place-only Selmer
complex on `S₀ ∪ {qᵢ}` with varying `qᵢ`. Passing a different fixed support for
each stage does not give one uniform bound. The standard-old supplier also
uses `MinS`, whereas the actual stage here uses the native enlarged-support
`Mcoef`. No bound uniform over all active supports is asserted.

### 3. Positive-stage original arithmetic data

For every `i` with `[NeZero i]`, `StageArithmeticInput F O i` contains:

```lean
oldPair           : SelPairData Dᵢ Dᵢ
scalarLocal       : GCx (Acoef i)
retainedCondition : GCx (Acoef i)
scalarRestriction : GHom oldPair.E scalarLocal
condition         : GHom retainedCondition Cqᵢ
localCup          : GPair Cqᵢ Cqᵢ scalarLocal
retained          : RetainedPlaceInput Dᵢ oldPair Cqᵢ
  scalarLocal retainedCondition (F.restriction i)
  scalarRestriction condition localCup
originalIsotropy  : O.Isotropy i
otherOld          : O.OtherOldComplements i
otherDerivatives  : O.OtherDerivativeComplements i
originalComparison : OriginalDiagramComparison Qallᵢ Nᵢ
```

The last two paired diagrams are exactly:

```lean
Qallᵢ := allPlacePair Dᵢ oldPair Cqᵢ scalarLocal retainedCondition
  (F.restriction i) scalarRestriction condition localCup retained
Nᵢ := O.pair i originalIsotropy
```

`Nᵢ` is the original `galoisPairDataT` of the actual inflated Weil coefficient
systems, with the actual selected original old conditions and actual old
derivative conditions. The auxiliary new-place conditions are full on the first
side and zero on the second. The original old conditions may include both
primitive full/zero orientations. They are not forced to the different
all-full/all-zero prototype.

The retained-place record has the exact original cup compatibility and isotropy:

```lean
compat : ∀ a b c (h : a + b = c) (x : Dᵢ.G.X a) (y : Dᵢ.G.X b),
  scalarRestriction.f c c rfl (oldPair.cupG.P a b c h x y) =
    localCup.P a b c h ((F.restriction i).f a a rfl x)
      ((F.restriction i).f b b rfl y)

hU : ∀ a b c : ℤ, a + b = c + 1 →
  retainedCondition.X a →ₗ[Acoef i]
    retainedCondition.X b →ₗ[Acoef i] scalarLocal.X c

isotropy : ∀ a a₁ b b₁ c c₁ (h : a + b = c + 1)
  (ha : a + 1 = a₁) (hb : b + 1 = b₁) (hc : c + 1 = c₁)
  (u : retainedCondition.X a) (v : retainedCondition.X b),
  scalarLocal.d c c₁ hc (hU a b c h u v) +
    hU a₁ b c₁ (by omega) (retainedCondition.d a a₁ ha u) v +
    sgn a • hU a b₁ c₁ (by omega) u (retainedCondition.d b b₁ hb v) =
      localCup.P a b c₁ (by omega)
        (condition.f a a rfl u) (condition.f b b rfl v)
```

This same-condition isotropy is independent of strict/relaxed orthogonality.
No fully relaxed same-condition substitution is made. In the singular-plane
case, the additional finite precision in the derivative label must supply the
actual singular self-cup primitive. One possible arithmetic route uses

```lean
∃ z : (F.q i).adicCompletion K, z ^ (2 ^ i) = -1
```

The `fixedRoots` field does not assert this stronger fact. The producer assumes
the exact `retained.isotropy` identity, not this particular route to constructing
it.

#### Remaining original complement cases

`O.OtherOldComplements i` is required **only** where `¬ O.KnownOldPair i v`.
`KnownOldPair` covers the canonical arithmetic Kummer/full/unramified pair,
full/zero, zero/full, and the actual strict/relaxed truncation pair. Full/zero
is supplied; zero/full is proved by a local adjoint-cone chase; canonical old
conditions and strict/relaxed truncations use the established suppliers.

For an unmatched old pair, the exact type is:

```lean
∀ (L : FiniteLocalTraces (F.support i) (Acoef i)
    (InflMod (F.inclusion i) (Tate1 (Acoef i) (O.roots i))))
  (v : Places K (F.support i)), ¬ O.KnownOldPair i v →
  ∀ (J : LocalTruncIsotropy (O.oldA i v).i (O.oldB i v).i
      (orthGaloisPair K (O.coefficientPair i)
        (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i)) v)),
    QuasiIso (GHom.toCC (orthLocalMap (O.oldA i v).i (O.oldB i v).i
      (orthGaloisPair K (O.coefficientPair i)
        (actLBeta_smul (F.inclusion i) W i (α i) (O.roots i)) v)
      J (L.trv v) (L.htrv₁ v)))
```

`O.OtherDerivativeComplements i` has that same per-place comparison type for
`O.derivativeA i v hv` and `O.derivativeB i v hv`, but only under

```lean
hv : v ∈ O.derivatives i
O.derivativeA i v hv ≠ derivativeStrictAt v ∨
  O.derivativeB i v hv ≠ derivativeRelaxedAt v
```

**Why this can remain:** `VerifiedOrthogonality` proves the specific
strict/relaxed derivative truncation pair, including `D⁰`. It does not identify
arbitrary previously retained finite/singular plane conditions with that pair.
Those actual conditions are retained unchanged. For exact strict/relaxed data,
the remaining predicate is vacuous and the verified theorem is used.

#### The one named original diagram transport

`OriginalDiagramComparison Qallᵢ Nᵢ` contains five actual cochain maps. Its
four `SelData` parameters are exactly:

```lean
Daᵢ := allRelaxData Dᵢ Cqᵢ (F.restriction i)
Dbᵢ := allStrictData Dᵢ Cqᵢ (F.restriction i)
Naᵢ := galoisSelData K (F.support i) (Acoef i)
  (MinS (F.inclusion i) W i (α i)) (O.conditionsA i)
Nbᵢ := galoisSelData K (F.support i) (Acoef i)
  (MinS (F.inclusion i) W i (charInv (α i))) (O.conditionsB i)

scalar    : GHom (coneCx Qallᵢ.resE) (coneCx Nᵢ.resE)
global    : GHom Daᵢ.G Naᵢ.G
compact   : GHom (compactCx Dbᵢ) (compactCx Nbᵢ)
localCone : GHom (locCx Daᵢ) (locCx Naᵢ)
condition : GHom Dbᵢ.U Nbᵢ.U
```

The last four maps have bijective components in every integer degree. For every
original trace `tr` killing boundaries, the two exact squares are:

```lean
GHom.toCC (globalDualityMap Qallᵢ (pullScalarTrace Qallᵢ Nᵢ scalar tr)
  (pullScalarTrace_kills Qallᵢ Nᵢ scalar tr htr)) =
GHom.toCC (ghomComp (ghomComp global (globalDualityMap Nᵢ tr htr))
  (dualHom compact 3))

GHom.toCC (localDualityMap Qallᵢ (pullScalarTrace Qallᵢ Nᵢ scalar tr)
  (pullScalarTrace_kills Qallᵢ Nᵢ scalar tr htr)) =
GHom.toCC (ghomComp (ghomComp localCone (localDualityMap Nᵢ tr htr))
  (dualHom condition 3))
```

`pullScalarTrace` is `tr.comp (scalar.f 3 3 rfl)`. Its boundary identity is
proved. The original duality squares and component isomorphisms prove both
all-place duality obligations required by the normalized pairing supplier.
No original-duality conclusion is simply renamed as a transport input.

**Why a transport remains:** the original printed and old-orthogonality suppliers
use the inflated `MinS` coefficient systems, inverse characters, selected original
conditions, and truncated scalar targets. The normalized one-place producer uses
native `Mcoef` on the enlarged support and the same-condition partitioned old
paired diagram. These are not definitionally the same diagrams. The arithmetic
coefficient, conjugation, condition and scalar-cone comparisons are one named
input; they are not implemented here.

#### Derivative action, roots and residual dimensions

The other positive-stage fields are exactly:

```lean
trivialAction : ∀ (g : Gloc K (F.q i))
  (m : ResMod (locMap K (F.support i) (F.q i)) (F.coefficient i)), g • m = m

fixedRoots : ∀ (g : Gal(AlgebraicClosure ((F.q i).adicCompletion K)/
    (F.q i).adicCompletion K)) (ζ : AlgebraicClosure ((F.q i).adicCompletion K)),
  ζ ^ (2 ^ i) = 1 → g ζ = ζ

localDimensions : ∀ n : ℤ, Module.finrank (ResidueField (Acoef i))
  (residualCohomologyAt (F.localCx i) n) = splitLocalRank n
```

`splitLocalRank` is `2,4,2` in degrees `0,1,2`, and zero elsewhere. The independent
local residual finiteness requirement of `exists_stagePairing_trace` is supplied
by `localCx_residualCohomologyFinite` and
`finite_residualCohomologyAt_of`; it is not retained as an extra field.

## Remaining concrete fibre and switch identifications

The produced certificate is conditional on the exact remaining local-form input:

```lean
ε₂ ≠ 0
ε ≠ 0
σ ≠ 0
localPairingOfMat (L.D.locK P) =
  transportedPairing ε₀ ε₂ ε σ (conjMatrix Cn W hW P)
```

The original Weil/conjugation dictionary and original trace normalization against
the returned tame primitive-root coordinate must supply this equality. A trace
isomorphism alone does not fix its unit scaling.

For detection on the produced finite fibre `Q := L.finiteFibre P`, the exact
independent inputs are:

```lean
coeff  : InducedCoefficientDictionary S₀ e χ E Cn U P
scalar : ArithmeticCommonScalar S₀ e χ E P B
span   : CoefficientSpanWitness P
V      : RetainedEvaluation (S := S₀) (e := e) (α := χ) (E := E)
  (U := U) (P := P) n Q
```

The first-cohomology finite-dimensionality required by the supplier is proved.
The nonzero prescribed class, dimension greater than one, height-one prime
`P ≠ (2)`, rational degree-two field setting, and finite auxiliary fields are the
supplier's stated case and setting assumptions.

Detection constructs a prime label. It does not prove that this new label is the
already prescribed stage family or that its evaluations equal the retained
localization. With the returned kernel `h`, put

```lean
H := arithmeticKernelFamily E S₀ e χ h
X := basisArithmeticLabel S₀ hS₀ e χ E Cn V.original H
  (fun i => T i ⊔ B i) excl hdegree
```

A precise remaining localization bridge, if this label is used for that retained
switch, is:

```lean
∀ x : LinearMap.ker (Q.d 1 2 rfl),
  (L.D.resLimit hU P).f 1 1 rfl x.val.1 =
    (basisValue P U V.original X.label.frob (V.coordinates x.val), 0)
```

The arithmetic label matching, this localization bridge, and the finite/singular
side-to-two-term-stage equivalences are not proved here. Consequently no completed
switch step or height-one regularity theorem is claimed.

## Verification files

`StatementAudit.txt` gives the exported statements, input records and their
projections, and the scratch axiom reports. `Verification.txt` records the final
single-file check and source discipline checks. The scratch diagnostic commands
are not part of `Assembly.lean`.
