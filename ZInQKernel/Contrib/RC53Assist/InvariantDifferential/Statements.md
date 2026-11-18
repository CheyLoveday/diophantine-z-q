# Exact declaration statements

The statements below are copied verbatim from the final source headers. Active declaration contexts are included; Lean includes only the variables and instances actually required by each declaration. The accompanying compiler type reports expose the elaborated quantifiers. Proof-argument abbreviations in those reports are printing abbreviations, not added hypotheses.

Every explicit theorem and definition was audited, including private helpers. The coordinate structure and its five projections were audited as well. Every report contains only `propext`, `Classical.choice`, and `Quot.sound`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.rational_canonical (private)

Source: `DivisorZero.lean`:57. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
```

### Exact statement

```lean
private theorem rational_canonical (k : Type*) [Field k] :
    (Place.orderSystem (IsFunctionField.ratFunc k)).divisorClass
        ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k)) =
      canonicalClass (IsFunctionField.ratFunc k) isIntegrallyClosedIn_ratFunc
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.exists_normalized_rational (private)

Source: `DivisorZero.lean`:70. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
```

### Exact statement

```lean
private theorem exists_normalized_rational (k : Type*) [Field k] :
    ∃ ω : Module.Dual k ↥(repartitionSpace k (RatFunc k)),
      ω ∈ weilDifferentialSpace k (RatFunc k) ∧
      IsGreatest {D : Divisor k (RatFunc k) | ω ∈ weilDifferentialFiltration D}
        ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k)) ∧
      repartitionDualComponent ω (Place.infty k) (RatFunc.X : RatFunc k)⁻¹ = -1
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.rationalDifferential (private)

Source: `DivisorZero.lean`:109. Kind: DEF.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
```

### Exact statement

```lean
private def rationalDifferential (k : Type*) [Field k] :
    Module.Dual k ↥(repartitionSpace k (RatFunc k))
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.rationalDifferential_mem (private)

Source: `DivisorZero.lean`:115. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
```

### Exact statement

```lean
private theorem rationalDifferential_mem (k : Type*) [Field k] :
    rationalDifferential k ∈ weilDifferentialSpace k (RatFunc k)
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.rationalDifferential_greatest (private)

Source: `DivisorZero.lean`:121. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
```

### Exact statement

```lean
private theorem rationalDifferential_greatest (k : Type*) [Field k] :
    IsGreatest {D : Divisor k (RatFunc k) |
        rationalDifferential k ∈ weilDifferentialFiltration D}
      ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k))
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.rationalDifferential_normalization (private)

Source: `DivisorZero.lean`:130. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
```

### Exact statement

```lean
private theorem rationalDifferential_normalization (k : Type*) [Field k] :
    repartitionDualComponent (rationalDifferential k) (Place.infty k)
      (RatFunc.X : RatFunc k)⁻¹ = -1
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.rationalDifferential_ne_zero (private)

Source: `DivisorZero.lean`:137. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
```

### Exact statement

```lean
private theorem rationalDifferential_ne_zero (k : Type*) [Field k] :
    rationalDifferential k ≠ 0
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.rationalDifferential_divisor (private)

Source: `DivisorZero.lean`:147. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
```

### Exact statement

```lean
private theorem rationalDifferential_divisor (k : Type*) [Field k] :
    weilDifferentialDivisor (IsFunctionField.ratFunc k) isIntegrallyClosedIn_ratFunc
        (rationalDifferential_mem k) (rationalDifferential_ne_zero k) =
      (-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k)
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.differentialOfSeparating

Source: `DivisorZero.lean`:162. Kind: DEF.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
```

### Exact statement

```lean
def differentialOfSeparating (hF : IsFunctionField k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    ↥(weilDifferentialSpace k F)
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.differentialOfSeparating_ne_zero

Source: `DivisorZero.lean`:174. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
```

### Exact statement

```lean
theorem differentialOfSeparating_ne_zero (hF : IsFunctionField k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    differentialOfSeparating hF hx ≠ 0
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.differentialBasis (private)

Source: `DivisorZero.lean`:187. Kind: DEF.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
```

### Exact statement

```lean
private def differentialBasis (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    Basis Unit F ↥(weilDifferentialSpace k F)
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.differentialBasis_apply (private)

Source: `DivisorZero.lean`:197. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
```

### Exact statement

```lean
private theorem differentialBasis_apply (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] (i : Unit) :
    letI := weilDifferentialSpaceModule hF
    differentialBasis hF hex hx i = differentialOfSeparating hF hx
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.comparison

Source: `DivisorZero.lean`:209. Kind: DEF.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
```

### Exact statement

```lean
def comparison (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    KaehlerDifferential k F ≃ₗ[F] ↥(weilDifferentialSpace k F)
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.comparison_D_self

Source: `DivisorZero.lean`:219. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
```

### Exact statement

```lean
theorem comparison_D_self (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    comparison hF hex hx (D k F x) = differentialOfSeparating hF hx
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.comparison_D

Source: `DivisorZero.lean`:230. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
```

### Exact statement

```lean
theorem comparison_D (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] (y : F) :
    letI := weilDifferentialSpaceModule hF
    comparison hF hex hx (D k F y) =
      derivativeOfSeparating hx y • differentialOfSeparating hF hx
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.differentialOfSeparating_divisor

Source: `DivisorZero.lean`:241. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
```

### Exact statement

```lean
theorem differentialOfSeparating_divisor (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] :
    letI := ratFuncAlgebraOfTranscendental hx
    letI := isScalarTower_ratFuncAlgebraOfTranscendental hx
    letI := isFunctionField_iff_functionField.mp hF
    letI := isSeparable_ratFuncAlgebraOfTranscendental hx
    weilDifferentialDivisor hF hex (differentialOfSeparating hF hx).2
        (by simpa using differentialOfSeparating_ne_zero hF hx) =
      (-2 : ℤ) • Divisor.poles hF (Units.mk0 x hx.ne_zero) +
        Divisor.different k F (IsFunctionField.ratFunc k)
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.different_le_derivative (private)

Source: `DivisorZero.lean`:275. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
```

### Exact statement

```lean
private theorem different_le_derivative
    {k' F' : Type*} [Field k'] [Field F'] [Algebra k k'] [Algebra k' F']
    [Algebra F F'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    {P' : Place k' F'} {y : F'} (hgen : F⟮y⟯ = ⊤) {ψ : F[X]}
    (hψ : ψ.Monic) (hcoeff : ∀ i, ψ.coeff i ∈ (P'.restrict k F).integers)
    (hy : aeval y ψ = 0) (hψ' : aeval y (derivative ψ) ≠ 0) :
    (Place.differentExponent k F P' : ℤ) ≤ P'.ord (aeval y (derivative ψ))
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.different_le_quadratic (private)

Source: `DivisorZero.lean`:311. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
```

### Exact statement

```lean
private theorem different_le_quadratic
    {k' F' : Type*} [Field k'] [Field F'] [Algebra k k'] [Algebra k' F']
    [Algebra F F'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    {P' : Place k' F'} {u v : F} (hu : algebraMap F F' u ∈ P'.integers)
    (hv : algebraMap F F' v ∈ P'.integers) {z : F'} (hgen : F⟮z⟯ = ⊤)
    (hz : z ^ 2 + algebraMap F F' u * z - algebraMap F F' v = 0)
    (hne : 2 * z + algebraMap F F' u ≠ 0) :
    (Place.differentExponent k F P' : ℤ) ≤ P'.ord (2 * z + algebraMap F F' u)
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.polynomial_ratFunc_tower (private)

Source: `DivisorZero.lean`:344. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
open WeierstrassCurve.Affine
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
variable (W : WeierstrassCurve.Affine k)
```

### Exact statement

```lean
private theorem polynomial_ratFunc_tower :
    letI := ratFuncAlgebraOfTranscendental (transcendental_genericX W)
    IsScalarTower k[X] (RatFunc k) W.FunctionField
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.coordinate_equation (private)

Source: `DivisorZero.lean`:356. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
open WeierstrassCurve.Affine
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
variable (W : WeierstrassCurve.Affine k)
```

### Exact statement

```lean
private theorem coordinate_equation :
    genericY W ^ 2 + algebraMap k W.FunctionField W.a₁ * genericX W * genericY W +
        algebraMap k W.FunctionField W.a₃ * genericY W =
      genericX W ^ 3 + algebraMap k W.FunctionField W.a₂ * genericX W ^ 2 +
        algebraMap k W.FunctionField W.a₄ * genericX W + algebraMap k W.FunctionField W.a₆
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.weierstrass_different_bound (private)

Source: `DivisorZero.lean`:370. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
open WeierstrassCurve.Affine
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
variable (W : WeierstrassCurve.Affine k)
variable [W.IsElliptic]
```

### Exact statement

```lean
private theorem weierstrass_different_bound (P : Place k W.FunctionField) :
    letI := ratFuncAlgebraOfTranscendental (transcendental_genericX W)
    letI := isScalarTower_ratFuncAlgebraOfTranscendental (transcendental_genericX W)
    letI := isFunctionField_iff_functionField.mp W.isFunctionField
    letI := isSeparable_ratFuncAlgebraOfTranscendental (transcendental_genericX W)
    (Place.differentExponent k (RatFunc k) P : ℤ) ≤
      P.ord (invariantDifferentialDenom W) + 2 * (-P.ord (genericX W) ⊔ 0)
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.invariantWeilDifferential

Source: `DivisorZero.lean`:467. Kind: DEF.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
open WeierstrassCurve.Affine
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
variable (W : WeierstrassCurve.Affine k)
variable [W.IsElliptic]
```

### Exact statement

```lean
def invariantWeilDifferential : ↥(weilDifferentialSpace k W.FunctionField)
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.invariantWeilDifferential_formula

Source: `DivisorZero.lean`:476. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
open WeierstrassCurve.Affine
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
variable (W : WeierstrassCurve.Affine k)
variable [W.IsElliptic]
```

### Exact statement

```lean
theorem invariantWeilDifferential_formula :
    letI := weilDifferentialSpaceModule W.isFunctionField
    invariantWeilDifferential W =
      (invariantDifferentialDenom W)⁻¹ •
        differentialOfSeparating W.isFunctionField (transcendental_genericX W)
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.invariantWeilDifferential_ne_zero

Source: `DivisorZero.lean`:487. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
open WeierstrassCurve.Affine
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
variable (W : WeierstrassCurve.Affine k)
variable [W.IsElliptic]
```

### Exact statement

```lean
theorem invariantWeilDifferential_ne_zero :
    (invariantWeilDifferential W : Module.Dual k ↥(repartitionSpace k W.FunctionField)) ≠ 0
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.invariantWeilDifferential_divisor

Source: `DivisorZero.lean`:498. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
open WeierstrassCurve.Affine
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
variable (W : WeierstrassCurve.Affine k)
variable [W.IsElliptic]
```

### Exact statement

```lean
theorem invariantWeilDifferential_divisor :
    weilDifferentialDivisor W.isFunctionField (isIntegrallyClosedIn_functionField W)
        (invariantWeilDifferential W).2 (invariantWeilDifferential_ne_zero W) = 0
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.invariantWeilDifferential_mem_holomorphic

Source: `DivisorZero.lean`:528. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
open WeierstrassCurve.Affine
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
variable (W : WeierstrassCurve.Affine k)
variable [W.IsElliptic]
```

### Exact statement

```lean
theorem invariantWeilDifferential_mem_holomorphic :
    (invariantWeilDifferential W : Module.Dual k ↥(repartitionSpace k W.FunctionField)) ∈
      weilDifferentialFiltration (0 : Divisor k W.FunctionField)
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.holomorphicWeilDifferentials_eq_span

Source: `DivisorZero.lean`:538. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
open WeierstrassCurve.Affine
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
variable (W : WeierstrassCurve.Affine k)
variable [W.IsElliptic]
```

### Exact statement

```lean
theorem holomorphicWeilDifferentials_eq_span :
    weilDifferentialFiltration (0 : Divisor k W.FunctionField) =
      Submodule.span k {(invariantWeilDifferential W :
        Module.Dual k ↥(repartitionSpace k W.FunctionField))}
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.existsUnique_smul_invariantWeilDifferential

Source: `DivisorZero.lean`:556. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
open WeierstrassCurve.Affine
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
variable (W : WeierstrassCurve.Affine k)
variable [W.IsElliptic]
```

### Exact statement

```lean
theorem existsUnique_smul_invariantWeilDifferential
    (η : ↥(weilDifferentialFiltration (0 : Divisor k W.FunctionField))) :
    ∃! c : k, c • (invariantWeilDifferential W :
      Module.Dual k ↥(repartitionSpace k W.FunctionField)) = η
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.invariantWeilDifferential_order

Source: `DivisorZero.lean`:571. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
open WeierstrassCurve.Affine
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
variable (W : WeierstrassCurve.Affine k)
variable [W.IsElliptic]
```

### Exact statement

```lean
theorem invariantWeilDifferential_order (P : Place k W.FunctionField) :
    weilDifferentialOrder W.isFunctionField (isIntegrallyClosedIn_functionField W)
        (invariantWeilDifferential W).2 (invariantWeilDifferential_ne_zero W) P = 0
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.comparison_mem_holomorphic_iff

Source: `DivisorZero.lean`:580. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField
open WeierstrassCurve.Affine
variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}
variable (W : WeierstrassCurve.Affine k)
variable [W.IsElliptic]
```

### Exact statement

```lean
theorem comparison_mem_holomorphic_iff (η : KaehlerDifferential k W.FunctionField) :
    letI := weilDifferentialSpaceModule W.isFunctionField
    (comparison W.isFunctionField (isIntegrallyClosedIn_functionField W)
        (transcendental_genericX W) η : Module.Dual k ↥(repartitionSpace k W.FunctionField)) ∈
      weilDifferentialFiltration (0 : Divisor k W.FunctionField) ↔
        ∃! c : k, c • invariantDifferential W = η
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.WeierstrassCoordinates

Source: `WeierstrassModel.lean`:54. Kind: STRUCTURE.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
```

### Exact statement

```lean
structure WeierstrassCoordinates (P : Place k F) (W : WeierstrassCurve k) (x y : F) : Prop where
  /-- FIELD. The first coordinate has order `-2` at the base place.
  Locator: Silverman, Proposition III.3.1, the choice from `L(2O)`. -/
  ord_x : P.ord x = -2
  /-- FIELD. The first coordinate is regular away from the base place.
  Locator: Silverman, Proposition III.3.1, membership in `L(2O)`. -/
  ord_x_nonneg : ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord x
  /-- FIELD. The second coordinate has order `-3` at the base place.
  Locator: Silverman, Proposition III.3.1, the choice from `L(3O)`. -/
  ord_y : P.ord y = -3
  /-- FIELD. The second coordinate is regular away from the base place.
  Locator: Silverman, Proposition III.3.1, membership in `L(3O)`. -/
  ord_y_nonneg : ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord y
  /-- FIELD. The two coordinates satisfy the equation of the curve over the function field.
  Locator: Silverman, Proposition III.3.1, the relation in `L(6O)`. -/
  equation : (W.baseChange F).toAffine.Equation x y
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.WeierstrassCoordinates.x_ne_zero

Source: `WeierstrassModel.lean`:79. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}
  (h : WeierstrassCoordinates P W x y)
include h
```

### Exact statement

```lean
theorem x_ne_zero : x ≠ 0
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.WeierstrassCoordinates.y_ne_zero

Source: `WeierstrassModel.lean`:83. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}
  (h : WeierstrassCoordinates P W x y)
include h
```

### Exact statement

```lean
theorem y_ne_zero : y ≠ 0
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.WeierstrassCoordinates.transcendental_x

Source: `WeierstrassModel.lean`:87. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}
  (h : WeierstrassCoordinates P W x y)
include h
```

### Exact statement

```lean
theorem transcendental_x : Transcendental k x
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.WeierstrassCoordinates.transcendental_y

Source: `WeierstrassModel.lean`:92. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}
  (h : WeierstrassCoordinates P W x y)
include h
```

### Exact statement

```lean
theorem transcendental_y : Transcendental k y
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.WeierstrassCoordinates.poles_x

Source: `WeierstrassModel.lean`:97. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}
  (h : WeierstrassCoordinates P W x y)
include h
```

### Exact statement

```lean
theorem poles_x (hF : IsFunctionField k F) :
    Divisor.poles hF (Units.mk0 x h.x_ne_zero) = (2 : ℤ) • WeilDivisor.ofPoint P
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.WeierstrassCoordinates.poles_y

Source: `WeierstrassModel.lean`:103. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}
  (h : WeierstrassCoordinates P W x y)
include h
```

### Exact statement

```lean
theorem poles_y (hF : IsFunctionField k F) :
    Divisor.poles hF (Units.mk0 y h.y_ne_zero) = (3 : ℤ) • WeilDivisor.ofPoint P
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.WeierstrassCoordinates.finrank_adjoin_x_eq_two

Source: `WeierstrassModel.lean`:110. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}
  (h : WeierstrassCoordinates P W x y)
include h
```

### Exact statement

```lean
theorem finrank_adjoin_x_eq_two (hF : IsFunctionField k F) (hP : P.degree = 1) :
    Module.finrank k⟮x⟯ F = 2
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.WeierstrassCoordinates.finrank_adjoin_y_eq_three

Source: `WeierstrassModel.lean`:118. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}
  (h : WeierstrassCoordinates P W x y)
include h
```

### Exact statement

```lean
theorem finrank_adjoin_y_eq_three (hF : IsFunctionField k F) (hP : P.degree = 1) :
    Module.finrank k⟮y⟯ F = 3
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.WeierstrassCoordinates.adjoin_eq_top

Source: `WeierstrassModel.lean`:126. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}
  (h : WeierstrassCoordinates P W x y)
include h
```

### Exact statement

```lean
theorem adjoin_eq_top (hF : IsFunctionField k F) (hP : P.degree = 1) : k⟮x, y⟯ = ⊤
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.exists_cubic_relation (private)

Source: `WeierstrassModel.lean`:146. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
```

### Exact statement

```lean
private theorem exists_cubic_relation (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) {P : Place k F} (hP : P.degree = 1)
    {x y : F} (hx0 : x ≠ 0) (hxP : P.ord x = -2) (hxQ : ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord x)
    (hy0 : y ≠ 0) (hyP : P.ord y = -3) (hyQ : ∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord y) :
    ∃ c : Fin 6 → k, c 5 ≠ 0 ∧ ∑ i, c i • ![1, x, y, x ^ 2, x * y, x ^ 3] i = y ^ 2
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.exists_weierstrassCoordinates_of_genus_eq_one

Source: `WeierstrassModel.lean`:209. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
```

### Exact statement

```lean
theorem exists_weierstrassCoordinates_of_genus_eq_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) {P : Place k F} (hP : P.degree = 1) :
    ∃ (W : WeierstrassCurve k) (x y : F), WeierstrassCoordinates P W x y
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.genus_zero_of_single_generator (private)

Source: `WeierstrassModel.lean`:240. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
```

### Exact statement

```lean
private theorem genus_zero_of_single_generator {x : F} (hx : Transcendental k x)
    (htop : k⟮x⟯ = (⊤ : IntermediateField k F)) : genus k F = 0
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.WeierstrassCoordinates.singular_slope_generates

Source: `WeierstrassModel.lean`:276. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}
  (h : WeierstrassCoordinates P W x y)
include h
```

### Exact statement

```lean
theorem singular_slope_generates (hF : IsFunctionField k F) (hP : P.degree = 1)
    {x₀ y₀ : k} (hs : W.toAffine.IsSingular x₀ y₀) :
    k⟮(y - algebraMap k F y₀) / (x - algebraMap k F x₀)⟯ = ⊤
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.WeierstrassCoordinates.singular_slope_transcendental

Source: `WeierstrassModel.lean`:313. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}
  (h : WeierstrassCoordinates P W x y)
include h
```

### Exact statement

```lean
theorem singular_slope_transcendental (hF : IsFunctionField k F) (hP : P.degree = 1)
    {x₀ y₀ : k} (hs : W.toAffine.IsSingular x₀ y₀) :
    Transcendental k ((y - algebraMap k F y₀) / (x - algebraMap k F x₀))
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.WeierstrassCoordinates.genus_zero_of_singular

Source: `WeierstrassModel.lean`:326. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}
  (h : WeierstrassCoordinates P W x y)
include h
```

### Exact statement

```lean
theorem genus_zero_of_singular (hF : IsFunctionField k F) (hP : P.degree = 1)
    {x₀ y₀ : k} (hs : W.toAffine.IsSingular x₀ y₀) : genus k F = 0
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.WeierstrassCoordinates.isElliptic

Source: `WeierstrassModel.lean`:334. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}
  (h : WeierstrassCoordinates P W x y)
include h
```

### Exact statement

```lean
theorem isElliptic [PerfectField k] (hF : IsFunctionField k F) (hP : P.degree = 1)
    (hg : genus k F ≠ 0) : W.IsElliptic
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.evaluation_injective (private)

Source: `WeierstrassModel.lean`:350. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {W : WeierstrassCurve.Affine k} {x y : F}
```

### Exact statement

```lean
private theorem evaluation_injective (h : (W⁄F).toAffine.Equation x y)
    (hx : Transcendental k x) : Function.Injective (Affine.CoordinateRing.evalAlgHom h)
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.weierstrassFieldLift

Source: `WeierstrassModel.lean`:358. Kind: DEF.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {W : WeierstrassCurve.Affine k} {x y : F}
```

### Exact statement

```lean
def weierstrassFieldLift (h : (W⁄F).toAffine.Equation x y)
    (hx : Transcendental k x) : W.FunctionField →ₐ[k] F
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.weierstrassFieldLift_algebraMap

Source: `WeierstrassModel.lean`:364. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {W : WeierstrassCurve.Affine k} {x y : F}
```

### Exact statement

```lean
theorem weierstrassFieldLift_algebraMap (h : (W⁄F).toAffine.Equation x y)
    (hx : Transcendental k x) (z : W.CoordinateRing) :
    weierstrassFieldLift h hx (algebraMap W.CoordinateRing W.FunctionField z) =
      Affine.CoordinateRing.evalAlgHom h z
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.weierstrassFieldLift_genericX

Source: `WeierstrassModel.lean`:372. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {W : WeierstrassCurve.Affine k} {x y : F}
```

### Exact statement

```lean
theorem weierstrassFieldLift_genericX (h : (W⁄F).toAffine.Equation x y)
    (hx : Transcendental k x) : weierstrassFieldLift h hx W.genericX = x
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.weierstrassFieldLift_genericY

Source: `WeierstrassModel.lean`:379. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {W : WeierstrassCurve.Affine k} {x y : F}
```

### Exact statement

```lean
theorem weierstrassFieldLift_genericY (h : (W⁄F).toAffine.Equation x y)
    (hx : Transcendental k x) : weierstrassFieldLift h hx W.genericY = y
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.weierstrassFieldLift_fieldRange

Source: `WeierstrassModel.lean`:386. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {W : WeierstrassCurve.Affine k} {x y : F}
```

### Exact statement

```lean
theorem weierstrassFieldLift_fieldRange (h : (W⁄F).toAffine.Equation x y)
    (hx : Transcendental k x) : (weierstrassFieldLift h hx).fieldRange = k⟮x, y⟯
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.weierstrassFieldEquiv

Source: `WeierstrassModel.lean`:394. Kind: DEF.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {W : WeierstrassCurve.Affine k} {x y : F}
```

### Exact statement

```lean
def weierstrassFieldEquiv (h : (W⁄F).toAffine.Equation x y)
    (hx : Transcendental k x) (hxy : k⟮x, y⟯ = ⊤) : W.FunctionField ≃ₐ[k] F
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.weierstrassFieldEquiv_genericX

Source: `WeierstrassModel.lean`:406. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {W : WeierstrassCurve.Affine k} {x y : F}
```

### Exact statement

```lean
theorem weierstrassFieldEquiv_genericX (h : (W⁄F).toAffine.Equation x y)
    (hx : Transcendental k x) (hxy : k⟮x, y⟯ = ⊤) :
    weierstrassFieldEquiv h hx hxy W.genericX = x
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.weierstrassFieldEquiv_genericY

Source: `WeierstrassModel.lean`:414. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {W : WeierstrassCurve.Affine k} {x y : F}
```

### Exact statement

```lean
theorem weierstrassFieldEquiv_genericY (h : (W⁄F).toAffine.Equation x y)
    (hx : Transcendental k x) (hxy : k⟮x, y⟯ = ⊤) :
    weierstrassFieldEquiv h hx hxy W.genericY = y
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.exists_weierstrassEquation_of_genus_eq_one

Source: `WeierstrassModel.lean`:425. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {W : WeierstrassCurve.Affine k} {x y : F}
```

### Exact statement

```lean
theorem exists_weierstrassEquation_of_genus_eq_one (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) {P : Place k F} (hP : P.degree = 1) :
    ∃ W : WeierstrassCurve.Affine k, Nonempty (W.FunctionField ≃ₐ[k] F)
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.exists_weierstrassModel_of_genus_eq_one

Source: `WeierstrassModel.lean`:436. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {W : WeierstrassCurve.Affine k} {x y : F}
```

### Exact statement

```lean
theorem exists_weierstrassModel_of_genus_eq_one [PerfectField k] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hg : genus k F = 1) {P : Place k F} (hP : P.degree = 1) :
    ∃ W : WeierstrassCurve.Affine k, W.IsElliptic ∧
      ∃ e : W.FunctionField ≃ₐ[k] F,
        P.ord (e W.genericX) = -2 ∧ P.ord (e W.genericY) = -3 ∧
        (∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord (e W.genericX)) ∧
        (∀ Q : Place k F, Q ≠ P → 0 ≤ Q.ord (e W.genericY))
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.exists_weierstrassModel

Source: `WeierstrassModel.lean`:454. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {W : WeierstrassCurve.Affine k} {x y : F}
```

### Exact statement

```lean
theorem exists_weierstrassModel [PerfectField k] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (he : IsEllipticFunctionField k F) :
    ∃ W : WeierstrassCurve.Affine k, W.IsElliptic ∧ Nonempty (W.FunctionField ≃ₐ[k] F)
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## ZInQ.Contrib.RC53Assist.InvariantDifferential.s2b_rational

Source: `WeierstrassModel.lean`:464. Kind: THEOREM.

### Active context

```lean
open TauCeti AlgebraicGeometry WeierstrassCurve Polynomial
open scoped IntermediateField
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {W : WeierstrassCurve.Affine k} {x y : F}
```

### Exact statement

```lean
theorem s2b_rational {L : Type*} [Field L] [Algebra ℚ L]
    (hL : IsFunctionField ℚ L) (hex : IsIntegrallyClosedIn ℚ L)
    (he : IsEllipticFunctionField ℚ L) :
    ∃ W : WeierstrassCurve.Affine ℚ, W.IsElliptic ∧ Nonempty (W.FunctionField ≃ₐ[ℚ] L)
```

Axioms: `[propext, Classical.choice, Quot.sound]`.
