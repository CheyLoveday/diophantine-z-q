# Pullback coefficient: proofs and remaining comparison

## Result

This is a kernel-checked conditional reduction, not an unconditional proof of
`PullbackCoefficientConstantGlue`.

The concrete invariant differential is proved locally regular in the Kähler sense at
**every place**, over any field. On the affine chart the two partial derivatives generate
the unit ideal, giving a regular expression in `dx` and `dy`. At infinity, with
`z = -x/y` and `s = -1/y`, the proof gives

`ω = q⁻¹ dz`, with `q = 1 - a₁z - a₂z² - 2a₃s - 2a₄zs - 3a₆s²` and `v∞(q) = 1`.

The other proved ingredients are the regularity of Weil cotrace along rational isogenies,
the vanishing of the divisor of a nonzero regular Weil differential in genus one, and the
constancy of a function taking such a differential to another regular differential.
Together these give both the exact constant-coefficient target and the full algebraic
isogeny-scalar target from the single generic input described below. No elliptic-specific
regularity assertion is a remaining input.

## Files and verification

All paths are relative to the repository root. The files are under
`ZInQKernel/Contrib/RC53Assist/PullbackScalar/`.

- `Reduction.lean`: 36,053 bytes, 624 lines; 18 theorems and 12 definitions.
  SHA256: `5c9c4a2b486fca465a4b231a8288c17fb2c8dafaee74061940a59bb9e6757a15`.
- `AuditOutput.txt`: 13,370 bytes. This is the successful scratch type and axiom output.
  SHA256: `6da46964306d22c8700aaa61cf8cb3e6a27614a87072f05213c5f503a6ad6c53`.
- `AuditAttempt1.txt`: 17,474 bytes. This preserves the first audit attempt, which failed
  only because its scratch pretty-printer setting `pp.width` was unsupported. The setting
  was removed; the proof source was not changed for that correction.
  SHA256: `524f900d685ec0e7bd09d90ff21360675946bf867acfd2fe76ea4bef12215200`.

The compiler reports Lean 4.35.0, release commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The existing manifest pins Mathlib to
`56a005855ea17e0b0958f73ec801ae140b0a1679` (`v4.35.0`).

With the prescribed toolchain on `PATH`, the final source was checked from the repository
root using:

```sh
LEAN_NUM_THREADS=6 taskset -c 128-143 nice -n 10 lake env lean \
  ZInQKernel/Contrib/RC53Assist/PullbackScalar/Reduction.lean
```

The final source check exited 0, with no errors or warnings. The audit was performed on a
scratch copy whose initial 36,053 bytes were verified byte-identical to the final source.
Only diagnostic commands followed that prefix. The corrected audit exited 0 with no errors
or warnings. Its output contains separate axiom reports for all 18 theorems and all 12
definitions; every report is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The final proof source has no diagnostic commands, prohibited proof declarations, or
execution constructs. Its heartbeat ceiling is 800,000. All 30 declarations have classified
and located docstrings. Temporary Lean exploration and audit copies are not proof
deliverables and were removed after the results were recorded.

Only newly created contribution files were changed. There were no commits, checkouts,
dependency updates, package builds, or changes to pre-existing sources. No independent
review or integration is claimed.

## What remains, precisely

The unresolved statement is `RationalResidueComparisonFact`, whose complete definition is:

```lean
def RationalResidueComparisonFact : Prop :=
  ∃ C : ComparisonFamily, CotraceCompatibility C ∧ LocalExactRegularity C
```

It asserts the existence of a **generic differential comparison**, not any statement
about an elliptic curve, an isogeny coefficient, or a rational pullback scalar. Its clauses
are the following exact definitions from the proof source.

```lean
abbrev KaehlerWeilComparison (K : Type) [Field K] [Algebra ℚ K]
    (hK : IsFunctionField ℚ K) : Type :=
  letI := weilDifferentialSpaceModule hK
  KaehlerDifferential ℚ K ≃ₗ[K] ↥(weilDifferentialSpace ℚ K)

def ComparisonFamily : Type 1 :=
  ∀ (K : Type) [Field K] [Algebra ℚ K] (hK : IsFunctionField ℚ K)
    (_hex : IsIntegrallyClosedIn ℚ K), KaehlerWeilComparison K hK

def CotraceCompatibility (C : ComparisonFamily) : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    [Algebra K L] [IsScalarTower ℚ K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (hK : IsFunctionField ℚ K) (hL : IsFunctionField ℚ L)
    (hexK : IsIntegrallyClosedIn ℚ K) (hexL : IsIntegrallyClosedIn ℚ L)
    (η : KaehlerDifferential ℚ K),
    C L hL hexL (KaehlerDifferential.map ℚ ℚ K L η) =
      weilDifferentialCotrace ℚ L hK hL (C K hK hexK η)

def LocalExactRegularity (C : ComparisonFamily) : Prop :=
  ∀ (K : Type) [Field K] [Algebra ℚ K] (hK : IsFunctionField ℚ K)
    (hex : IsIntegrallyClosedIn ℚ K) (P : Place ℚ K) (f g : K),
    f ∈ P.integers → g ∈ P.integers →
      repartitionDualComponent
        (C K hK hex (KaehlerDifferential.D ℚ K f) :
          Module.Dual ℚ ↥(repartitionSpace ℚ K)) P g = 0
```

Thus the exact tasks left are to construct the function-field-linear Kähler–Weil
comparison, prove its agreement with the existing cotrace for finite separable extensions,
and prove its local integral exact-differential vanishing law. In residue terminology the
last law is `Res_P(g df) = 0` for `f,g ∈ O_P`. The law is required for arbitrary function
fields and arbitrary places, including non-rational places.

The regularity of the concrete elliptic differential is **not** another task left:
`Local.invariant_mem_localKaehlerSpace` proves the local Kähler statement, and
`invariantRegularity_of_localExactRegularity` derives its regular Weil image from the
generic local comparison law. The divisor and exact-constant-field arguments after that
are proved using the existing library.

The comparison clauses are infrastructure requirements, not a verbatim literature print.
Silverman, *The Arithmetic of Elliptic Curves*, second edition, II.4 and III.5 identify the
rational differential, pullback, and invariant-differential conventions. No book page or
literal printed-statement correspondence is certified here, and no printed theorem is
installed as a formal assertion. In particular the conclusion about rational isogeny
scalars is not introduced as an input under another name.

A bare linear equivalence between two one-dimensional function-field spaces is not enough:
it still has to satisfy both the cotrace and local regularity clauses. This contribution
constructs no witness of `RationalResidueComparisonFact`, so the original glue remains
conditional on that generic comparison. The clean axiom reports do not change that status.

## Exact theorem signatures and scratch axiom reports

The signatures below are copied from the final proof source, with proof bodies omitted.
The namespace is `ZInQ.Contrib.RC53Assist.PullbackScalar`. The open namespaces are
`TauCeti`, `WeierstrassCurve.Affine`, and
`ZInQ.Contrib.CloudB3RC53.ModularWeil`. The raw compiler type output and individual axiom
reports are also preserved in `AuditOutput.txt`.

For the first two signatures the ambient binders are:

```lean
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
```

### 1. `regular_weilDivisor_eq_zero`

```lean
theorem regular_weilDivisor_eq_zero (hK : IsFunctionField k K)
    (hex : IsIntegrallyClosedIn k K) (hg : genus k K = 1)
    {ω : Module.Dual k ↥(repartitionSpace k K)}
    (hmem : ω ∈ weilDifferentialSpace k K) (hω : ω ≠ 0)
    (hreg : ω ∈ weilDifferentialFiltration (0 : Divisor k K)) :
    weilDifferentialDivisor hK hex hmem hω = 0
```

Scratch axioms: `[propext, Classical.choice, Quot.sound]`.

### 2. `constant_of_regular_weil_multiple`

```lean
theorem constant_of_regular_weil_multiple (hK : IsFunctionField k K)
    (hex : IsIntegrallyClosedIn k K) (hg : genus k K = 1)
    {ω : Module.Dual k ↥(repartitionSpace k K)}
    (hreg : ω ∈ weilDifferentialFiltration (0 : Divisor k K)) (hω : ω ≠ 0)
    (c : K) (hc : repartitionDualMul hK c ω ∈
      weilDifferentialFiltration (0 : Divisor k K)) :
    c ∈ Set.range (algebraMap k K)
```

Scratch axioms: `[propext, Classical.choice, Quot.sound]`.

The remaining non-`Local` signatures have all their binders displayed.

### 3. `comparison_smul`

```lean
theorem comparison_smul (K : Type) [Field K] [Algebra ℚ K]
    (hK : IsFunctionField ℚ K) (e : KaehlerWeilComparison K hK)
    (c : K) (η : KaehlerDifferential ℚ K) :
    (e (c • η) : Module.Dual ℚ ↥(repartitionSpace ℚ K)) =
      repartitionDualMul hK c (e η : Module.Dual ℚ ↥(repartitionSpace ℚ K))
```

Scratch axioms: `[propext, Classical.choice, Quot.sound]`.

### 4. `weilPullback_regular`

```lean
theorem weilPullback_regular {W₁ W₂ : WeierstrassCurve.Affine ℚ}
    [W₁.IsElliptic] [W₂.IsElliptic] (β : TauCeti.Isogeny W₁ W₂)
    (ω : ↥(weilDifferentialSpace ℚ W₂.FunctionField))
    (hω : (ω : Module.Dual ℚ ↥(repartitionSpace ℚ W₂.FunctionField)) ∈
      weilDifferentialFiltration (0 : Divisor ℚ W₂.FunctionField)) :
    (weilPullback β ω : Module.Dual ℚ ↥(repartitionSpace ℚ W₁.FunctionField)) ∈
      weilDifferentialFiltration (0 : Divisor ℚ W₁.FunctionField)
```

Scratch axioms: `[propext, Classical.choice, Quot.sound]`.

### 5. `comparison_pullback`

```lean
theorem comparison_pullback (C : ComparisonFamily) (hC : CotraceCompatibility C)
    {W₁ W₂ : WeierstrassCurve.Affine ℚ} [W₁.IsElliptic] [W₂.IsElliptic]
    (β : TauCeti.Isogeny W₁ W₂) (η : KaehlerDifferential ℚ W₂.FunctionField) :
    curveComparison C W₁ (β.pullbackDifferential η) =
      weilPullback β (curveComparison C W₂ η)
```

Scratch axioms: `[propext, Classical.choice, Quot.sound]`.

### 6. `pullbackCoefficientConstantGlue_of_comparison`

```lean
theorem pullbackCoefficientConstantGlue_of_comparison (C : ComparisonFamily)
    (hC : CotraceCompatibility C) (hω : InvariantRegularity C) :
    PullbackCoefficientConstantGlue
```

Scratch axioms: `[propext, Classical.choice, Quot.sound]`.

For signatures 7–14 the namespace is additionally `Local`, with ambient binders:

```lean
variable {k : Type*} [Field k]
```

The local definitions used in these signatures are:

```lean
def parameterAtInfinity (W : WeierstrassCurve.Affine k) : W.FunctionField :=
  -genericX W / genericY W

def auxiliaryAtInfinity (W : WeierstrassCurve.Affine k) : W.FunctionField :=
  -(genericY W)⁻¹

def differentialUnitAtInfinity (W : WeierstrassCurve.Affine k) : W.FunctionField :=
  1 - (algebraMap k W.FunctionField W.a₁ * parameterAtInfinity W +
    algebraMap k W.FunctionField W.a₂ * parameterAtInfinity W ^ 2 +
    algebraMap k W.FunctionField (2 * W.a₃) * auxiliaryAtInfinity W +
    algebraMap k W.FunctionField (2 * W.a₄) * parameterAtInfinity W * auxiliaryAtInfinity W +
    algebraMap k W.FunctionField (3 * W.a₆) * auxiliaryAtInfinity W ^ 2)

def localKaehlerSpace {K : Type*} [Field K] [Algebra k K] (P : Place k K) :
    Submodule k (KaehlerDifferential k K) :=
  Submodule.span k {η | ∃ a f : K, a ∈ P.integers ∧ f ∈ P.integers ∧
    a • KaehlerDifferential.D k K f = η}
```

### 7. `Local.coordinate_partials_bezout`

```lean
theorem coordinate_partials_bezout (W : WeierstrassCurve.Affine k) [W.IsElliptic] :
    ∃ a b : W.CoordinateRing,
      a * CoordinateRing.mk W W.polynomialX + b * CoordinateRing.mk W W.polynomialY = 1
```

Scratch axioms: `[propext, Classical.choice, Quot.sound]`.

### 8. `Local.denominator_mul_derivativeY`

```lean
theorem denominator_mul_derivativeY (W : WeierstrassCurve.Affine k) [W.IsElliptic] :
    invariantDifferentialDenom W *
        derivativeOfSeparating (transcendental_genericX W) (genericY W) =
      -algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W W.polynomialX)
```

Scratch axioms: `[propext, Classical.choice, Quot.sound]`.

### 9. `Local.invariant_affine_expression`

```lean
theorem invariant_affine_expression (W : WeierstrassCurve.Affine k) [W.IsElliptic]
    {a b : W.CoordinateRing}
    (hab : a * CoordinateRing.mk W W.polynomialX +
      b * CoordinateRing.mk W W.polynomialY = 1) :
    invariantDifferential W =
      algebraMap W.CoordinateRing W.FunctionField b •
        KaehlerDifferential.D k W.FunctionField (genericX W) +
      (-algebraMap W.CoordinateRing W.FunctionField a) •
        KaehlerDifferential.D k W.FunctionField (genericY W)
```

Scratch axioms: `[propext, Classical.choice, Quot.sound]`.

### 10. `Local.valuation_parameterAtInfinity`

```lean
theorem valuation_parameterAtInfinity (W : WeierstrassCurve.Affine k) :
    W.infinityPlace (parameterAtInfinity W) = WithZero.exp (-1 : ℤ)
```

Scratch axioms: `[propext, Classical.choice, Quot.sound]`.

### 11. `Local.valuation_auxiliaryAtInfinity`

```lean
theorem valuation_auxiliaryAtInfinity (W : WeierstrassCurve.Affine k) :
    W.infinityPlace (auxiliaryAtInfinity W) = WithZero.exp (-3 : ℤ)
```

Scratch axioms: `[propext, Classical.choice, Quot.sound]`.

### 12. `Local.valuation_differentialUnitAtInfinity`

```lean
theorem valuation_differentialUnitAtInfinity (W : WeierstrassCurve.Affine k) :
    W.infinityPlace (differentialUnitAtInfinity W) = 1
```

Scratch axioms: `[propext, Classical.choice, Quot.sound]`.

### 13. `Local.invariant_infinity_expression`

```lean
theorem invariant_infinity_expression (W : WeierstrassCurve.Affine k) [W.IsElliptic] :
    invariantDifferential W = (differentialUnitAtInfinity W)⁻¹ •
      KaehlerDifferential.D k W.FunctionField (parameterAtInfinity W)
```

Scratch axioms: `[propext, Classical.choice, Quot.sound]`.

### 14. `Local.invariant_mem_localKaehlerSpace`

```lean
theorem invariant_mem_localKaehlerSpace (W : WeierstrassCurve.Affine k) [W.IsElliptic]
    (P : Place k W.FunctionField) : invariantDifferential W ∈ localKaehlerSpace P
```

Scratch axioms: `[propext, Classical.choice, Quot.sound]`.

### 15. `comparison_regular_of_local`

```lean
theorem comparison_regular_of_local (C : ComparisonFamily) (hL : LocalExactRegularity C)
    (K : Type) [Field K] [Algebra ℚ K] (hK : IsFunctionField ℚ K)
    (hex : IsIntegrallyClosedIn ℚ K) (η : KaehlerDifferential ℚ K)
    (hη : ∀ P : Place ℚ K, η ∈ Local.localKaehlerSpace P) :
    (C K hK hex η : Module.Dual ℚ ↥(repartitionSpace ℚ K)) ∈
      weilDifferentialFiltration (0 : Divisor ℚ K)
```

Scratch axioms: `[propext, Classical.choice, Quot.sound]`.

### 16. `invariantRegularity_of_localExactRegularity`

```lean
theorem invariantRegularity_of_localExactRegularity (C : ComparisonFamily)
    (hL : LocalExactRegularity C) : InvariantRegularity C
```

Scratch axioms: `[propext, Classical.choice, Quot.sound]`.

### 17. `pullbackCoefficientConstantGlue_of_residueComparison`

```lean
theorem pullbackCoefficientConstantGlue_of_residueComparison (h : RationalResidueComparisonFact) :
    PullbackCoefficientConstantGlue
```

Scratch axioms: `[propext, Classical.choice, Quot.sound]`.

### 18. `isogenyScalarRationalGlue_of_residueComparison`

```lean
theorem isogenyScalarRationalGlue_of_residueComparison (h : RationalResidueComparisonFact) :
    IsogenyScalarRationalGlue
```

Scratch axioms: `[propext, Classical.choice, Quot.sound]`.

## Exact existing target and the intermediate regularity condition

These definitions are included to make the conditional conclusions unambiguous; the
existing targets were not changed.

```lean
def PullbackCoefficientConstantGlue : Prop :=
  ∀ (E₁ E₂ : WeierstrassCurve ℚ) [E₁.IsElliptic] [E₂.IsElliptic]
    (β : TauCeti.Isogeny E₁.toAffine E₂.toAffine) (c : E₁.toAffine.FunctionField),
    c • invariantDifferential E₁.toAffine =
        β.pullbackDifferential (invariantDifferential E₂.toAffine) →
      c ∈ Set.range (algebraMap ℚ E₁.toAffine.FunctionField)

def IsogenyScalarRationalGlue : Prop :=
  ∀ E₁ E₂ : WeierstrassCurve ℚ, E₁.IsElliptic → E₂.IsElliptic →
    ∀ β : TauCeti.Isogeny E₁.toAffine E₂.toAffine, ∃ r : ℚ, r ≠ 0 ∧ IsPullbackScalar β r

def curveComparison (C : ComparisonFamily) (W : WeierstrassCurve.Affine ℚ)
    [W.IsElliptic] : KaehlerWeilComparison W.FunctionField W.isFunctionField :=
  C W.FunctionField W.isFunctionField (isIntegrallyClosedIn_functionField W)

def InvariantRegularity (C : ComparisonFamily) : Prop :=
  ∀ (W : WeierstrassCurve.Affine ℚ) [W.IsElliptic],
    (curveComparison C W (invariantDifferential W) :
      Module.Dual ℚ ↥(repartitionSpace ℚ W.FunctionField)) ∈
        weilDifferentialFiltration (0 : Divisor ℚ W.FunctionField)
```

`InvariantRegularity` is derived by theorem 16. The final theorem 17 takes only the generic
residue comparison fact, not `InvariantRegularity` as an additional hypothesis.
