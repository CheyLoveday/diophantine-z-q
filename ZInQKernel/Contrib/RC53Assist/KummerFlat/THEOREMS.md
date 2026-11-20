# Exact declarations and axiom audit

Namespace: `ZInQ.Contrib.RC53Assist.KummerFlat`.

All 28 theorems and all 47 declarations were checked in a standalone copy of `Counterexample.lean`. The copy differs only by appended `#check` and `#print axioms` commands. Compilation and the audit both exited successfully without diagnostics.

Each theorem below has its authored signature, interpreted in the section context of `Counterexample.lean`, followed by the complete compiler-displayed type and verbatim axiom output. The authored signature preserves numeric type annotations that the pretty-printer may omit; the displayed type includes the implicit section parameters.

The axiom union is exactly `{propext, Classical.choice, Quot.sound}`. `coefMod_smul_of_fixed` uses only `{propext, Quot.sound}`.

## Theorems

### `not_flat_of_annihilator`

Kind: theorem, proved. A nonzero module annihilated by a nonzero
scalar cannot be flat over a local ring with nilpotent maximal ideal.
This is the contrapositive of the freeness step at tex 4409–4412.

Authored signature:

```lean
theorem not_flat_of_annihilator [Nontrivial M]
    (hnil : IsNilpotent (maximalIdeal R)) (r : R) (hr : r ≠ 0)
    (hkill : ∀ x : M, r • x = 0) : ¬ Module.Flat R M
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.not_flat_of_annihilator {R : Type} [CommRing R] [IsLocalRing R] {M : Type}
  [AddCommGroup M] [Module R M] [Nontrivial M] (hnil : IsNilpotent (IsLocalRing.maximalIdeal R)) (r : R) (hr : r ≠ 0)
  (hkill : ∀ (x : M), r • x = 0) : ¬Module.Flat R M
'ZInQ.Contrib.RC53Assist.KummerFlat.not_flat_of_annihilator' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `stage_two_ne_zero`

Kind: theorem, proved. The scalar two is nonzero in the second
coefficient stage of tex 2725, although its square is zero.

Authored signature:

```lean
theorem stage_two_ne_zero : (2 : Acoef 2) ≠ 0
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.stage_two_ne_zero : 2 ≠ 0
'ZInQ.Contrib.RC53Assist.KummerFlat.stage_two_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `stage_not_flat_of_two_annihilator`

Kind: theorem, proved. A nonzero module killed by two is not flat
over the second coefficient stage; tex 2725 and 4409–4412.

Authored signature:

```lean
theorem stage_not_flat_of_two_annihilator
    {M : Type} [AddCommGroup M] [Module (Acoef 2) M] [Nontrivial M]
    (hkill : ∀ x : M, (2 : Acoef 2) • x = 0) :
    ¬ Module.Flat (Acoef 2) M
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.stage_not_flat_of_two_annihilator {M : Type} [AddCommGroup M]
  [Module (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef 2) M] [Nontrivial M] (hkill : ∀ (x : M), 2 • x = 0) :
  ¬Module.Flat (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef 2) M
'ZInQ.Contrib.RC53Assist.KummerFlat.stage_not_flat_of_two_annihilator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `contB1_not_flat_of_annihilator`

Kind: theorem, proved. If a nonzero scalar kills every difference
`g • x - x` and some such difference is nonzero, the actual continuous
coboundaries are not flat. The differential is the one at tex 3413–3418;
the flat-to-free criterion is tex 4409–4412.

Authored signature:

```lean
theorem contB1_not_flat_of_annihilator
    (hnil : IsNilpotent (maximalIdeal R)) (r : R) (hr : r ≠ 0)
    (hkill : ∀ (g : G) (x : M), r • (g • x - x) = 0)
    (hmove : ∃ (g : G) (x : M), g • x ≠ x) :
    ¬ Module.Flat R (contB1 R G M)
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.contB1_not_flat_of_annihilator {R : Type} [CommRing R] [IsLocalRing R] {G : Type}
  [Group G] [TopologicalSpace G] [ContinuousMul G] {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M]
  [SMulCommClass G R M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] [ContinuousSMul G M]
  (hnil : IsNilpotent (IsLocalRing.maximalIdeal R)) (r : R) (hr : r ≠ 0)
  (hkill : ∀ (g : G) (x : M), r • (g • x - x) = 0) (hmove : ∃ g x, g • x ≠ x) :
  ¬Module.Flat R ↥(ZInQ.Manuscript.RC.CoefModules.contB1 R G M)
'ZInQ.Contrib.RC53Assist.KummerFlat.contB1_not_flat_of_annihilator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `flat_cocycleCondition_of_ne_one`

Kind: theorem, proved. All terms of a cocycle condition except
possibly degree one are flat whenever the coefficient module is flat.
The zero and one terms are those of tex 3415–3417; continuous cochain
flatness is the finite-partition argument of tex 4412–4414.

Authored signature:

```lean
theorem flat_cocycleCondition_of_ne_one
    (Z : Submodule R (contCochain R G M 1))
    (hZ : ∀ z ∈ Z, contD R G M 1 z = 0)
    (n : ℤ) (hn : n ≠ 1) :
    Module.Flat R ((cocycleCondition Z hZ).X n)
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.flat_cocycleCondition_of_ne_one {R : Type} [CommRing R] {G : Type} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M]
  [SMulCommClass G R M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] [CompactSpace G]
  [Module.Flat R M] (Z : Submodule R ↥(ZInQ.Manuscript.RC.SelmerComplex.contCochain R G M 1))
  (hZ : ∀ z ∈ Z, (ZInQ.Manuscript.RC.CoefModules.contD R G M 1) z = 0) (n : ℤ) (hn : n ≠ 1) :
  Module.Flat R ↑((ZInQ.Manuscript.RC.CoefModules.cocycleCondition Z hZ).X n)
'ZInQ.Contrib.RC53Assist.KummerFlat.flat_cocycleCondition_of_ne_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `kummerZ'_zero`

Kind: theorem, proved. A zero torsion coefficient map has zero
extended Kummer span, with precisely the definition in tex 3430–3438.

Authored signature:

```lean
theorem kummerZ'_zero :
    kummerZ' R (0 : TorsAlg F B m →+ M) = ⊥
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.kummerZ'_zero {F : Type} [Field F] [CharZero F] [DecidableEq F]
  (B : WeierstrassCurve F) [B.IsElliptic] (m : ℕ) [NeZero m] {R : Type} [CommRing R] {M : Type} [AddCommGroup M]
  [Module R M] [DistribMulAction (Field.absoluteGaloisGroup F) M] [SMulCommClass (Field.absoluteGaloisGroup F) R M]
  [TopologicalSpace M] [DiscreteTopology M] : ZInQ.Manuscript.RC.CoefModules.kummerZ' R 0 = ⊥
'ZInQ.Contrib.RC53Assist.KummerFlat.kummerZ'_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `kummerConditionIn_zero_X_one`

Kind: theorem, proved. The degree-one term of the actual Kummer
condition for a zero coefficient map is the coboundary module, not a
free module on chosen cochains; tex 3415–3418 and 3430–3438.

Authored signature:

```lean
theorem kummerConditionIn_zero_X_one
    (hι : ∀ (g : Field.absoluteGaloisGroup F) (t : TorsAlg F B m),
      (0 : TorsAlg F B m →+ M) (g • t) = g • (0 : TorsAlg F B m →+ M) t) :
    (kummerConditionIn R (0 : TorsAlg F B m →+ M) hι).X 1 =
      ModuleCat.of R (contB1 R (Field.absoluteGaloisGroup F) M)
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.kummerConditionIn_zero_X_one {F : Type} [Field F] [CharZero F] [DecidableEq F]
  (B : WeierstrassCurve F) [B.IsElliptic] (m : ℕ) [NeZero m] {R : Type} [CommRing R] {M : Type} [AddCommGroup M]
  [Module R M] [DistribMulAction (Field.absoluteGaloisGroup F) M] [SMulCommClass (Field.absoluteGaloisGroup F) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup F) M]
  (hι : ∀ (g : Field.absoluteGaloisGroup F) (t : ZInQ.Manuscript.RC.CoefModules.TorsAlg F B m), 0 (g • t) = g • 0 t) :
  (ZInQ.Manuscript.RC.CoefModules.kummerConditionIn R 0 hι).X 1 =
    ↧↥(ZInQ.Manuscript.RC.CoefModules.contB1 R (Field.absoluteGaloisGroup F) M)
'ZInQ.Contrib.RC53Assist.KummerFlat.kummerConditionIn_zero_X_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `kummerConditionIn_zero_not_flat`

Kind: theorem, proved. The permitted zero coefficient map gives a
nonflat degree-one Kummer term when the action has a nonzero difference
annihilated by a nonzero scalar. This concerns the actual complex of
tex 3430–3438 and the model hypothesis of tex 4391–4414.

Authored signature:

```lean
theorem kummerConditionIn_zero_not_flat [IsLocalRing R]
    (hnil : IsNilpotent (maximalIdeal R)) (r : R) (hr : r ≠ 0)
    (hkill : ∀ (g : Field.absoluteGaloisGroup F) (x : M), r • (g • x - x) = 0)
    (hmove : ∃ (g : Field.absoluteGaloisGroup F) (x : M), g • x ≠ x)
    (hι : ∀ (g : Field.absoluteGaloisGroup F) (t : TorsAlg F B m),
      (0 : TorsAlg F B m →+ M) (g • t) = g • (0 : TorsAlg F B m →+ M) t) :
    ¬ Module.Flat R ((kummerConditionIn R (0 : TorsAlg F B m →+ M) hι).X 1)
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.kummerConditionIn_zero_not_flat {F : Type} [Field F] [CharZero F] [DecidableEq F]
  (B : WeierstrassCurve F) [B.IsElliptic] (m : ℕ) [NeZero m] {R : Type} [CommRing R] {M : Type} [AddCommGroup M]
  [Module R M] [DistribMulAction (Field.absoluteGaloisGroup F) M] [SMulCommClass (Field.absoluteGaloisGroup F) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup F) M] [IsLocalRing R]
  (hnil : IsNilpotent (IsLocalRing.maximalIdeal R)) (r : R) (hr : r ≠ 0)
  (hkill : ∀ (g : Field.absoluteGaloisGroup F) (x : M), r • (g • x - x) = 0) (hmove : ∃ g x, g • x ≠ x)
  (hι : ∀ (g : Field.absoluteGaloisGroup F) (t : ZInQ.Manuscript.RC.CoefModules.TorsAlg F B m), 0 (g • t) = g • 0 t) :
  ¬Module.Flat R ↑((ZInQ.Manuscript.RC.CoefModules.kummerConditionIn R 0 hι).X 1)
'ZInQ.Contrib.RC53Assist.KummerFlat.kummerConditionIn_zero_not_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `signModule_two_smul_difference`

Kind: theorem, proved. Every sign-action coboundary at the second
stage is killed by two; tex 2725–2726 and 3413–3418.

Authored signature:

```lean
theorem signModule_two_smul_difference (g : G) (x : SignModule χ) :
    (2 : Acoef 2) • (g • x - x) = 0
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.signModule_two_smul_difference {G : Type} [Group G] (χ : G →* ℤˣ) (g : G)
  (x : ZInQ.Contrib.RC53Assist.KummerFlat.SignModule χ) : 2 • (g • x - x) = 0
'ZInQ.Contrib.RC53Assist.KummerFlat.signModule_two_smul_difference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `signModule_action_nontrivial`

Kind: theorem, proved. A character taking the value minus one acts
nontrivially on the free rank-two stage module; tex 2725–2726 and 2791.

Authored signature:

```lean
theorem signModule_action_nontrivial (hχ : ∃ g : G, χ g = -1) :
    ∃ (g : G) (x : SignModule χ), g • x ≠ x
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.signModule_action_nontrivial {G : Type} [Group G] (χ : G →* ℤˣ)
  (hχ : ∃ g, χ g = -1) : ∃ g x, g • x ≠ x
'ZInQ.Contrib.RC53Assist.KummerFlat.signModule_action_nontrivial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `sqrt_image_sign`

Kind: theorem, proved. An automorphism sends a nonzero square root
to itself or its negative; tex 2726 and 2791.

Authored signature:

```lean
theorem sqrt_image_sign (g : Field.absoluteGaloisGroup F) :
    g.toAlgHom s = s ∨ g.toAlgHom s = -s
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.sqrt_image_sign {F : Type} [Field F] (s : AlgebraicClosure F) {a : F}
  (hs : s ^ 2 = (algebraMap F (AlgebraicClosure F)) a) (g : Field.absoluteGaloisGroup F) : ↑g s = s ∨ ↑g s = -s
'ZInQ.Contrib.RC53Assist.KummerFlat.sqrt_image_sign' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `sqrt_neg_ne_self`

Kind: theorem, proved. The two signs of a nonzero square root are
distinct in characteristic zero; tex 2726 and 2791.

Authored signature:

```lean
theorem sqrt_neg_ne_self : -s ≠ s
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.sqrt_neg_ne_self {F : Type} [Field F] [CharZero F] (s : AlgebraicClosure F)
  (hs0 : s ≠ 0) : -s ≠ s
'ZInQ.Contrib.RC53Assist.KummerFlat.sqrt_neg_ne_self' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `sqrtCharacter_has_negative`

Kind: theorem, proved. A nonsquare defines a nontrivial quadratic
character. The fixed-field characterization is the Galois descent used
in tex 3413–3417, with the character of tex 2726 and 2791.

Authored signature:

```lean
theorem sqrtCharacter_has_negative (ha : ¬ ∃ x : F, x ^ 2 = a) :
    ∃ g : Field.absoluteGaloisGroup F, sqrtCharacter s hs hs0 g = -1
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.sqrtCharacter_has_negative {F : Type} [Field F] [CharZero F] (s : AlgebraicClosure F)
  {a : F} (hs : s ^ 2 = (algebraMap F (AlgebraicClosure F)) a) (hs0 : s ≠ 0) (ha : ¬∃ x, x ^ 2 = a) :
  ∃ g, (ZInQ.Contrib.RC53Assist.KummerFlat.sqrtCharacter s hs hs0) g = -1
'ZInQ.Contrib.RC53Assist.KummerFlat.sqrtCharacter_has_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `padic_two_not_square`

Kind: theorem, proved. Two is not a square in the dyadic local
field: its valuation is odd. This supplies a concrete quadratic
character for the local conditions of tex 3413–3438.

Authored signature:

```lean
theorem padic_two_not_square : ¬ ∃ x : Padic 2, x ^ 2 = 2
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.padic_two_not_square : ¬∃ x, x ^ 2 = 2
'ZInQ.Contrib.RC53Assist.KummerFlat.padic_two_not_square' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `dyadicSqrtTwo_sq`

Kind: theorem, proved. The defining square-root equation of the
quadratic character; tex 2726 and 2791.

Authored signature:

```lean
theorem dyadicSqrtTwo_sq :
    dyadicSqrtTwo ^ 2 = algebraMap (Padic 2) (AlgebraicClosure (Padic 2)) 2
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.dyadicSqrtTwo_sq :
  ZInQ.Contrib.RC53Assist.KummerFlat.dyadicSqrtTwo ^ 2 = (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])) 2
'ZInQ.Contrib.RC53Assist.KummerFlat.dyadicSqrtTwo_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `dyadicSqrtTwo_ne_zero`

Kind: theorem, proved. The chosen square root is nonzero;
tex 2726 and 2791.

Authored signature:

```lean
theorem dyadicSqrtTwo_ne_zero : dyadicSqrtTwo ≠ 0
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.dyadicSqrtTwo_ne_zero : ZInQ.Contrib.RC53Assist.KummerFlat.dyadicSqrtTwo ≠ 0
'ZInQ.Contrib.RC53Assist.KummerFlat.dyadicSqrtTwo_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `dyadicSignCharacter_has_negative`

Kind: theorem, proved. The concrete dyadic character takes the value
minus one; tex 2726 and 2791.

Authored signature:

```lean
theorem dyadicSignCharacter_has_negative :
    ∃ g : Field.absoluteGaloisGroup (Padic 2), dyadicSignCharacter g = -1
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.dyadicSignCharacter_has_negative :
  ∃ g, ZInQ.Contrib.RC53Assist.KummerFlat.dyadicSignCharacter g = -1
'ZInQ.Contrib.RC53Assist.KummerFlat.dyadicSignCharacter_has_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `dyadicAmbientCochains_free`

Kind: theorem, proved. Every ambient continuous cochain module in
the concrete dyadic example is free over the second stage ring. Thus
the degree-one obstruction is not a failure of ambient cochain
flatness. This is the finite-partition method of tex 4409–4414.

Authored signature:

```lean
theorem dyadicAmbientCochains_free (n : ℕ) :
    Module.Free (Acoef 2)
      ((contCochains (Acoef 2) (Field.absoluteGaloisGroup (Padic 2))
        (SignModule dyadicSignCharacter)).X n)
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.dyadicAmbientCochains_free (n : ℕ) :
  Module.Free (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef 2)
    ↑((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef 2)
            (Field.absoluteGaloisGroup ℚ_[2])
            (ZInQ.Contrib.RC53Assist.KummerFlat.SignModule ZInQ.Contrib.RC53Assist.KummerFlat.dyadicSignCharacter)).X
        n)
'ZInQ.Contrib.RC53Assist.KummerFlat.dyadicAmbientCochains_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `dyadicZeroKummerCondition_not_flat`

Kind: theorem, proved. A concrete degree-one Kummer term over the
actual second stage ring is not flat, although its coefficient module
is free of rank two. No flatness or nonflatness premise is used;
tex 2725, 3430–3438, and 4391–4414.

Authored signature:

```lean
theorem dyadicZeroKummerCondition_not_flat :
    ¬ Module.Flat (Acoef 2) (dyadicZeroKummerCondition.X 1)
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.dyadicZeroKummerCondition_not_flat :
  ¬Module.Flat (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef 2)
      ↑(ZInQ.Contrib.RC53Assist.KummerFlat.dyadicZeroKummerCondition.X 1)
'ZInQ.Contrib.RC53Assist.KummerFlat.dyadicZeroKummerCondition_not_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `dyadicZeroKummerCondition_flat_off_one`

Kind: theorem, proved. The same concrete condition has flat terms
in every degree other than one; tex 3415–3417 and 4412–4414.

Authored signature:

```lean
theorem dyadicZeroKummerCondition_flat_off_one (n : ℤ) (hn : n ≠ 1) :
    Module.Flat (Acoef 2) (dyadicZeroKummerCondition.X n)
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.dyadicZeroKummerCondition_flat_off_one (n : ℤ) (hn : n ≠ 1) :
  Module.Flat (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef 2)
    ↑(ZInQ.Contrib.RC53Assist.KummerFlat.dyadicZeroKummerCondition.X n)
'ZInQ.Contrib.RC53Assist.KummerFlat.dyadicZeroKummerCondition_flat_off_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `standardOldAt_flat_off_one`

Kind: theorem, proved. Under the actual stage torsion hypothesis,
every standard old-condition term outside degree one is flat. This
uses the actual `MinS` coefficient module, not an abstract replacement;
tex 2725, 3415–3417, and 4391–4414.

Authored signature:

```lean
theorem standardOldAt_flat_off_one (i : ℕ) [NeZero i]
    (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]
    (hTor : FullTorsion K S₀ W (2 ^ i)) (v : Places K S)
    [DecidableEq (v.1.adicCompletion K)] (label : ℕ)
    (E : WeierstrassCurve (v.1.adicCompletion K)) [E.IsElliptic] (m : ℕ) [NeZero m]
    (ι : TorsAlg (v.1.adicCompletion K) E m →+
      ResMod (locMap K S v.1) (MinS hS W i α))
    (hι : ∀ (g : Gloc K v.1) t, ι (g • t) = g • ι t) (n : ℤ) (hn : n ≠ 1) :
    Module.Flat (Acoef i)
      ((standardOldAt K S (Acoef i) (MinS hS W i α) v label E m ι hι).U.X n)
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.standardOldAt_flat_off_one {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i]
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S₀ →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α] (hTor : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S₀ W (2 ^ i))
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S)
  [DecidableEq (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)] (label : ℕ)
  (E : WeierstrassCurve (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)) [E.IsElliptic] (m : ℕ) [NeZero m]
  (ι :
    ZInQ.Manuscript.RC.CoefModules.TorsAlg (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v) E m →+
      ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)
        (ZInQ.Manuscript.RC.CoefModules.MinS hS W i α))
  (hι :
    ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
      (t : ZInQ.Manuscript.RC.CoefModules.TorsAlg (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v) E m),
      ι (g • t) = g • ι t)
  (n : ℤ) (hn : n ≠ 1) :
  Module.Flat (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
    ↑((ZInQ.Contrib.RC53Assist.ResidualBounds.standardOldAt K S (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
              (ZInQ.Manuscript.RC.CoefModules.MinS hS W i α) v label E m ι hι).U.X
        n)
'ZInQ.Contrib.RC53Assist.KummerFlat.standardOldAt_flat_off_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `standardOldAt_not_flat_of_zero`

Kind: theorem, proved. The literal standard Kummer condition at the
actual second stage is nonflat for a zero coefficient map and a
nontrivial local sign action. These are conditions on the actual action
and map, not a flatness or nonflatness premise; tex 2725–2726,
3430–3438, and 4391–4414.

Authored signature:

```lean
theorem standardOldAt_not_flat_of_zero
    (α : GKS K S₀ →* (Acoef 2)ˣ) [IsOpenKer α] (v : Places K S)
    [DecidableEq (v.1.adicCompletion K)] (label : ℕ) (h0 : label ≠ 0) (h1 : label ≠ 1)
    (E : WeierstrassCurve (v.1.adicCompletion K)) [E.IsElliptic] (m : ℕ) [NeZero m]
    (ι : TorsAlg (v.1.adicCompletion K) E m →+
      ResMod (locMap K S v.1) (MinS hS W 2 α))
    (hι : ∀ (g : Gloc K v.1) t, ι (g • t) = g • ι t) (hzero : ι = 0)
    (hsign : ∀ (g : Gloc K v.1) (x : ResMod (locMap K S v.1) (MinS hS W 2 α)),
      g • x = x ∨ g • x = -x)
    (hmove : ∃ (g : Gloc K v.1) (x : ResMod (locMap K S v.1) (MinS hS W 2 α)),
      g • x ≠ x) :
    ¬ Module.Flat (Acoef 2)
      ((standardOldAt K S (Acoef 2) (MinS hS W 2 α) v label E m ι hι).U.X 1)
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.standardOldAt_not_flat_of_zero {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S₀ →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef 2)ˣ)
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α] (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S)
  [DecidableEq (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)] (label : ℕ) (h0 : label ≠ 0) (h1 : label ≠ 1)
  (E : WeierstrassCurve (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)) [E.IsElliptic] (m : ℕ) [NeZero m]
  (ι :
    ZInQ.Manuscript.RC.CoefModules.TorsAlg (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v) E m →+
      ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)
        (ZInQ.Manuscript.RC.CoefModules.MinS hS W 2 α))
  (hι :
    ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
      (t : ZInQ.Manuscript.RC.CoefModules.TorsAlg (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v) E m),
      ι (g • t) = g • ι t)
  (hzero : ι = 0)
  (hsign :
    ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
      (x :
        ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)
          (ZInQ.Manuscript.RC.CoefModules.MinS hS W 2 α)),
      g • x = x ∨ g • x = -x)
  (hmove : ∃ g x, g • x ≠ x) :
  ¬Module.Flat (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef 2)
      ↑((ZInQ.Contrib.RC53Assist.ResidualBounds.standardOldAt K S (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef 2)
                (ZInQ.Manuscript.RC.CoefModules.MinS hS W 2 α) v label E m ι hι).U.X
          1)
'ZInQ.Contrib.RC53Assist.KummerFlat.standardOldAt_not_flat_of_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `stdOldConditions_flat_off_one`

Kind: theorem, proved. All quantified stage terms of the exact
standard old-condition family are flat off degree one, from the
existing full-torsion input alone; tex 2725, 3415–3417, and 4391–4414.

Authored signature:

```lean
theorem stdOldConditions_flat_off_one
    (hTor : ∀ i, FullTorsion K S₀ W (2 ^ i)) (i : ℕ) [NeZero i]
    (v : Places K S) (hv : v.1 ∈ S₀) (n : ℤ) (hn : n ≠ 1) :
    Module.Flat (Acoef i)
      (((stdOldConditions hS W α Bv label m ιK hιK) i v hv).U.X n)
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.stdOldConditions_flat_off_one {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic]
  (α : (i : ℕ) → ZInQ.Manuscript.RC.SelmerComplex.GKS K S₀ →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [hα : ∀ (i : ℕ), ZInQ.Manuscript.RC.CoefModules.IsOpenKer (α i)]
  (Bv :
    (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) →
      WeierstrassCurve (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v))
  [hBv : ∀ (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S), (Bv v).IsElliptic]
  (label : ℕ → ZInQ.Manuscript.RC.SelmerComplex.Places K S → ℕ) (m : ℕ → ℕ) [hm : ∀ (i : ℕ), NeZero (m i)]
  (ιK :
    (i : ℕ) →
      (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) →
        ZInQ.Manuscript.RC.CoefModules.TorsAlg (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v) (Bv v) (m i) →+
          ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)
            (ZInQ.Manuscript.RC.CoefModules.MinS hS W i (α i)))
  (hιK :
    ∀ (i : ℕ) (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) (g : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
      (t :
        ZInQ.Manuscript.RC.CoefModules.TorsAlg (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v) (Bv v) (m i)),
      (ιK i v) (g • t) = g • (ιK i v) t)
  (hTor : ∀ (i : ℕ), ZInQ.Manuscript.RC.CoefModules.FullTorsion K S₀ W (2 ^ i)) (i : ℕ) [NeZero i]
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) (hv : ↑v ∈ S₀) (n : ℤ) (hn : n ≠ 1) :
  Module.Flat (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
    ↑((ZInQ.Manuscript.RC.Wiring.stdOldConditions hS W α Bv label m ιK hιK i v hv).U.X n)
'ZInQ.Contrib.RC53Assist.KummerFlat.stdOldConditions_flat_off_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `hcflatK_refuted_at_two`

Kind: theorem, proved. The exact quantified Kummer-flatness field
cannot hold if one second-stage old place has a zero coefficient map
and a nontrivial local sign action. The conclusion is the negation of
that field's complete quantifier order; tex 2725–2726, 3430–3438, and
4391–4414.

Authored signature:

```lean
theorem hcflatK_refuted_at_two (v : Places K S) (hv : v.1 ∈ S₀)
    (h0 : label 2 v ≠ 0) (h1 : label 2 v ≠ 1) (hzero : ιK 2 v = 0)
    (hsign : ∀ (g : Gloc K v.1)
      (x : ResMod (locMap K S v.1) (MinS hS W 2 (α 2))), g • x = x ∨ g • x = -x)
    (hmove : ∃ (g : Gloc K v.1)
      (x : ResMod (locMap K S v.1) (MinS hS W 2 (α 2))), g • x ≠ x) :
    ¬ (∀ i [NeZero i] (w : Places K S) (hw : w.1 ∈ S₀) (n : ℤ),
      label i w ≠ 0 → label i w ≠ 1 → Module.Flat (Acoef i)
        (((stdOldConditions hS W α Bv label m ιK hιK) i w hw).U.X n))
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.hcflatK_refuted_at_two {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K)
  (α : (i : ℕ) → ZInQ.Manuscript.RC.SelmerComplex.GKS K S₀ →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [hα : ∀ (i : ℕ), ZInQ.Manuscript.RC.CoefModules.IsOpenKer (α i)]
  (Bv :
    (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) →
      WeierstrassCurve (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v))
  [hBv : ∀ (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S), (Bv v).IsElliptic]
  (label : ℕ → ZInQ.Manuscript.RC.SelmerComplex.Places K S → ℕ) (m : ℕ → ℕ) [hm : ∀ (i : ℕ), NeZero (m i)]
  (ιK :
    (i : ℕ) →
      (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) →
        ZInQ.Manuscript.RC.CoefModules.TorsAlg (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v) (Bv v) (m i) →+
          ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)
            (ZInQ.Manuscript.RC.CoefModules.MinS hS W i (α i)))
  (hιK :
    ∀ (i : ℕ) (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) (g : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
      (t :
        ZInQ.Manuscript.RC.CoefModules.TorsAlg (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v) (Bv v) (m i)),
      (ιK i v) (g • t) = g • (ιK i v) t)
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) (hv : ↑v ∈ S₀) (h0 : label 2 v ≠ 0) (h1 : label 2 v ≠ 1)
  (hzero : ιK 2 v = 0)
  (hsign :
    ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
      (x :
        ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)
          (ZInQ.Manuscript.RC.CoefModules.MinS hS W 2 (α 2))),
      g • x = x ∨ g • x = -x)
  (hmove : ∃ g x, g • x ≠ x) :
  ¬∀ (i : ℕ) [NeZero i] (w : ZInQ.Manuscript.RC.SelmerComplex.Places K S) (hw : ↑w ∈ S₀) (n : ℤ),
      label i w ≠ 0 →
        label i w ≠ 1 →
          Module.Flat (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
            ↑((ZInQ.Manuscript.RC.Wiring.stdOldConditions hS W α Bv label m ιK hιK i w hw).U.X n)
'ZInQ.Contrib.RC53Assist.KummerFlat.hcflatK_refuted_at_two' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `coefMod_smul_of_fixed`

Kind: theorem, proved. If the torsion representation is fixed, its
scalar extension is acted on solely through the twisting character.
This is the actual tensor construction of tex 2725–2726 and 2790–2796.

Authored signature:

```lean
theorem coefMod_smul_of_fixed {G : Type} [Group G] {A : Type} [CommRing A]
    (α : G →* Aˣ) {T : Type} [AddCommGroup T] [DistribMulAction G T]
    (hfixed : ∀ (g : G) (t : T), g • t = t) (g : G) (x : CoefMod A α T) :
    g • x = ((α g : Aˣ) : A) • x
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.coefMod_smul_of_fixed {G : Type} [Group G] {A : Type} [CommRing A] (α : G →* Aˣ)
  {T : Type} [AddCommGroup T] [DistribMulAction G T] (hfixed : ∀ (g : G) (t : T), g • t = t) (g : G)
  (x : ZInQ.Manuscript.RC.CoefModules.CoefMod A α T) : g • x = ↑(α g) • x
'ZInQ.Contrib.RC53Assist.KummerFlat.coefMod_smul_of_fixed' depends on axioms: [propext, Quot.sound]
```

### `minS_quadratic_action`

Kind: theorem, proved. For split torsion, the actual inflated
coefficient module has the local quadratic action prescribed by its
character, including both restriction maps; tex 2725–2726, 2791,
and 3479–3498.

Authored signature:

```lean
theorem minS_quadratic_action (i : ℕ)
    (hfixed : ∀ (g : GKS K S₀) (t : TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)), g • t = t)
    (v : Places K S) (g : Gloc K v.1)
    (x : ResMod (locMap K S v.1) (MinS hS W i (quadraticStageCharacter χ i))) :
    g • x = ((χ (inflMap K hS (locMap K S v.1 g)) : ℤˣ) : ℤ) • x
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.minS_quadratic_action {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) (χ : ZInQ.Manuscript.RC.SelmerComplex.GKS K S₀ →* ℤˣ) (i : ℕ)
  (hfixed :
    ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S₀) (t : ZInQ.Manuscript.RC.CoefModules.TorsS K S₀ W ↑(2 ^ i)),
      g • t = t)
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) (g : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
  (x :
    ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)
      (ZInQ.Manuscript.RC.CoefModules.MinS hS W i (ZInQ.Contrib.RC53Assist.KummerFlat.quadraticStageCharacter χ i))) :
  g • x =
    ↑(χ ((ZInQ.Manuscript.RC.SelmerComplex.inflMap K hS) ((ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v) g))) • x
'ZInQ.Contrib.RC53Assist.KummerFlat.minS_quadratic_action' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `standardOldAt_split_quadratic_not_flat`

Kind: theorem, proved. For the actual `MinS` module, split
four-torsion and a nontrivial local quadratic character yield a
nonflat zero-map Kummer term at stage two. The full-torsion premise is
the existing stage input; neither a module flatness conclusion nor a
local action identity is assumed. Tex 2725–2726, 3430–3438,
3479–3498, and 4391–4414.

Authored signature:

```lean
theorem standardOldAt_split_quadratic_not_flat
    (hTor : FullTorsion K S₀ W (2 ^ 2))
    (hfixed : ∀ (g : GKS K S₀) (t : TorsS K S₀ W ((2 ^ 2 : ℕ) : ℤ)), g • t = t)
    (v : Places K S) [DecidableEq (v.1.adicCompletion K)]
    (hχ : ∃ g : Gloc K v.1, χ (inflMap K hS (locMap K S v.1 g)) = -1)
    (label : ℕ) (h0 : label ≠ 0) (h1 : label ≠ 1)
    (E : WeierstrassCurve (v.1.adicCompletion K)) [E.IsElliptic] (m : ℕ) [NeZero m]
    (ι : TorsAlg (v.1.adicCompletion K) E m →+
      ResMod (locMap K S v.1) (MinS hS W 2 (quadraticStageCharacter χ 2)))
    (hι : ∀ (g : Gloc K v.1) t, ι (g • t) = g • ι t) (hzero : ι = 0) :
    ¬ Module.Flat (Acoef 2)
      ((standardOldAt K S (Acoef 2) (MinS hS W 2 (quadraticStageCharacter χ 2))
        v label E m ι hι).U.X 1)
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.standardOldAt_split_quadratic_not_flat {K : Type} [Field K] [NumberField K]
  {S₀ S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (χ : ZInQ.Manuscript.RC.SelmerComplex.GKS K S₀ →* ℤˣ)
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer χ] (hTor : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S₀ W (2 ^ 2))
  (hfixed :
    ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S₀) (t : ZInQ.Manuscript.RC.CoefModules.TorsS K S₀ W ↑(2 ^ 2)),
      g • t = t)
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S)
  [DecidableEq (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)]
  (hχ :
    ∃ g, χ ((ZInQ.Manuscript.RC.SelmerComplex.inflMap K hS) ((ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v) g)) = -1)
  (label : ℕ) (h0 : label ≠ 0) (h1 : label ≠ 1)
  (E : WeierstrassCurve (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)) [E.IsElliptic] (m : ℕ) [NeZero m]
  (ι :
    ZInQ.Manuscript.RC.CoefModules.TorsAlg (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v) E m →+
      ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)
        (ZInQ.Manuscript.RC.CoefModules.MinS hS W 2 (ZInQ.Contrib.RC53Assist.KummerFlat.quadraticStageCharacter χ 2)))
  (hι :
    ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
      (t : ZInQ.Manuscript.RC.CoefModules.TorsAlg (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v) E m),
      ι (g • t) = g • ι t)
  (hzero : ι = 0) :
  ¬Module.Flat (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef 2)
      ↑((ZInQ.Contrib.RC53Assist.ResidualBounds.standardOldAt K S (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef 2)
                (ZInQ.Manuscript.RC.CoefModules.MinS hS W 2
                  (ZInQ.Contrib.RC53Assist.KummerFlat.quadraticStageCharacter χ 2))
                v label E m ι hι).U.X
          1)
'ZInQ.Contrib.RC53Assist.KummerFlat.standardOldAt_split_quadratic_not_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `exists_stage_diagram_of_gradedModel`

Kind: theorem, proved. The stage matrix-diagram consumer needs a
bounded graded finite free model and the actual duality data, not
termwise flatness of the chosen cochain presentation. The model's
localization, global trace pairing, and local trace pairing are retained
exactly. This exposes the weaker sufficient interface at tex 4391–4451;
it does not construct the required model for arbitrary Kummer maps.

Authored signature:

```lean
theorem exists_stage_diagram_of_gradedModel
    {A : Type} [CommRing A] (G : GCx A) {U : GCx A}
    {res : GHom G (splitLocalComplex A)} {ι : GHom U (splitLocalComplex A)}
    (Q : SelPairData (splitSelData G res U ι) (splitSelData G res U ι))
    (tr : (coneCx Q.resE).X 3 →ₗ[A] A)
    (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (hdual : QuasiIso (GHom.toCC (globalDualityMap Q tr htr)))
    (R : GradedModel G) (lo hi : ℤ)
    (hr : ∀ n, n < lo ∨ hi < n → R.rank n = 0) :
    ∃ S : StageMatrixDiagram A R.rank,
      S.dC = R.dC ∧ S.res = modelRes R (stagePairingInputOfSel Q tr htr) ∧
        S.glob = modelGlob R (stagePairingInputOfSel Q tr htr) ∧ S.loc = stageLocMat Q tr
```

Compiler type and axiom output:

```text
ZInQ.Contrib.RC53Assist.KummerFlat.exists_stage_diagram_of_gradedModel {A : Type} [CommRing A]
  (G : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx A) {U : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx A}
  {res : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom G (ZInQ.Contrib.RC53Assist.InnerLimit.splitLocalComplex A)}
  {ι : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom U (ZInQ.Contrib.RC53Assist.InnerLimit.splitLocalComplex A)}
  (Q :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData (ZInQ.Manuscript.RC.FibreDuality.splitSelData G res U ι)
      (ZInQ.Manuscript.RC.FibreDuality.splitSelData G res U ι))
  (tr : ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx Q.resE).X 3) →ₗ[A] A)
  (htr :
    ∀ (z : ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx Q.resE).X 2)),
      tr (((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx Q.resE).d 2 3 ⋯) z) = 0)
  (hdual :
    QuasiIso
      (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC
        (ZInQ.Contrib.CloudB3RC53.SelmerDuality.globalDualityMap Q tr htr)))
  (R : ZInQ.Manuscript.RC.Limits.GradedModel G) (lo hi : ℤ) (hr : ∀ (n : ℤ), n < lo ∨ hi < n → R.rank n = 0) :
  ∃ S,
    S.dC = R.dC ∧
      S.res =
          ZInQ.Manuscript.RC.FibreDuality.modelRes R (ZInQ.Manuscript.RC.FibreDuality.stagePairingInputOfSel Q tr htr) ∧
        S.glob =
            ZInQ.Manuscript.RC.FibreDuality.modelGlob R
              (ZInQ.Manuscript.RC.FibreDuality.stagePairingInputOfSel Q tr htr) ∧
          S.loc = ZInQ.Manuscript.RC.FibreDuality.stageLocMat Q tr
'ZInQ.Contrib.RC53Assist.KummerFlat.exists_stage_diagram_of_gradedModel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Definitions and instances

These supporting declarations were audited as well.

### `stageConstantTerm`

Kind: definition. Evaluation at `t = 0` on the positive coefficient
stage `A_i = (ℤ/2^i)[t]/(t^i)` of tex 2725.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.stageConstantTerm (i : ℕ) (hi : i ≠ 0) :
  ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i →+* ZMod (2 ^ i)
'ZInQ.Contrib.RC53Assist.KummerFlat.stageConstantTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `SignModule`

Kind: definition. The free rank-two stage module with quadratic
scalar action, as allowed by the characters in tex 2725–2726 and 2791.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.SignModule {G : Type} [Group G] (_χ : G →* ℤˣ) : Type
'ZInQ.Contrib.RC53Assist.KummerFlat.SignModule' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `signModuleAddCommGroup`

Kind: instance, defined. The additive group of the sign coefficient
module; tex 2725–2726.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.signModuleAddCommGroup {G : Type} [Group G] (χ : G →* ℤˣ) :
  AddCommGroup (ZInQ.Contrib.RC53Assist.KummerFlat.SignModule χ)
'ZInQ.Contrib.RC53Assist.KummerFlat.signModuleAddCommGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `signModuleModule`

Kind: instance, defined. The stage-ring scalar structure of the sign
coefficient module; tex 2725–2726.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.signModuleModule {G : Type} [Group G] (χ : G →* ℤˣ) :
  Module (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef 2) (ZInQ.Contrib.RC53Assist.KummerFlat.SignModule χ)
'ZInQ.Contrib.RC53Assist.KummerFlat.signModuleModule' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `signModuleFree`

Kind: instance, proved. The sign coefficient module is free of rank
two over the second stage ring; tex 2725.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.signModuleFree {G : Type} [Group G] (χ : G →* ℤˣ) :
  Module.Free (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef 2) (ZInQ.Contrib.RC53Assist.KummerFlat.SignModule χ)
'ZInQ.Contrib.RC53Assist.KummerFlat.signModuleFree' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `signModuleNontrivial`

Kind: instance, proved. The sign coefficient module is nonzero;
tex 2725 and the nonzero scalar two.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.signModuleNontrivial {G : Type} [Group G] (χ : G →* ℤˣ) :
  Nontrivial (ZInQ.Contrib.RC53Assist.KummerFlat.SignModule χ)
'ZInQ.Contrib.RC53Assist.KummerFlat.signModuleNontrivial' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `signModuleAction`

Kind: instance, defined. The Galois action is multiplication by the
quadratic character, with unchanged stage scalars; tex 2726 and 2791.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.signModuleAction {G : Type} [Group G] (χ : G →* ℤˣ) :
  DistribMulAction G (ZInQ.Contrib.RC53Assist.KummerFlat.SignModule χ)
'ZInQ.Contrib.RC53Assist.KummerFlat.signModuleAction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `signModuleSMulCommClass`

Kind: instance, proved. The quadratic action commutes with the
coefficient-ring scalars; tex 2725–2726 and 2791.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.signModuleSMulCommClass {G : Type} [Group G] (χ : G →* ℤˣ) :
  SMulCommClass G (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef 2) (ZInQ.Contrib.RC53Assist.KummerFlat.SignModule χ)
'ZInQ.Contrib.RC53Assist.KummerFlat.signModuleSMulCommClass' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `signModuleTopology`

Kind: instance, defined. Finite coefficients carry the discrete
topology used by the continuous cochains in tex 3455–3463.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.signModuleTopology {G : Type} [Group G] (χ : G →* ℤˣ) :
  TopologicalSpace (ZInQ.Contrib.RC53Assist.KummerFlat.SignModule χ)
'ZInQ.Contrib.RC53Assist.KummerFlat.signModuleTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `signModuleDiscrete`

Kind: instance, proved. The sign coefficient topology is discrete;
tex 3455–3463.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.signModuleDiscrete {G : Type} [Group G] (χ : G →* ℤˣ) :
  DiscreteTopology (ZInQ.Contrib.RC53Assist.KummerFlat.SignModule χ)
'ZInQ.Contrib.RC53Assist.KummerFlat.signModuleDiscrete' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `signModuleContinuousSMul`

Kind: instance, proved. A quadratic character with open kernel gives
a continuous action on the discrete stage module; tex 2781–2796.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.signModuleContinuousSMul {G : Type} [Group G] (χ : G →* ℤˣ) [TopologicalSpace G]
  [IsTopologicalGroup G] [ZInQ.Manuscript.RC.CoefModules.IsOpenKer χ] :
  ContinuousSMul G (ZInQ.Contrib.RC53Assist.KummerFlat.SignModule χ)
'ZInQ.Contrib.RC53Assist.KummerFlat.signModuleContinuousSMul' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `sqrtCharacter`

Kind: definition. The genuine absolute Galois character attached to
a nonzero square root; tex 2726 and 2791.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.sqrtCharacter {F : Type} [Field F] [CharZero F] (s : AlgebraicClosure F) {a : F}
  (hs : s ^ 2 = (algebraMap F (AlgebraicClosure F)) a) (hs0 : s ≠ 0) : Field.absoluteGaloisGroup F →* ℤˣ
'ZInQ.Contrib.RC53Assist.KummerFlat.sqrtCharacter' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `sqrtCharacterOpenKer`

Kind: instance, proved. The quadratic character has open kernel:
its kernel is the open stabilizer of its defining square root;
tex 2781–2796.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.sqrtCharacterOpenKer {F : Type} [Field F] [CharZero F] (s : AlgebraicClosure F)
  {a : F} (hs : s ^ 2 = (algebraMap F (AlgebraicClosure F)) a) (hs0 : s ≠ 0) :
  ZInQ.Manuscript.RC.CoefModules.IsOpenKer (ZInQ.Contrib.RC53Assist.KummerFlat.sqrtCharacter s hs hs0)
'ZInQ.Contrib.RC53Assist.KummerFlat.sqrtCharacterOpenKer' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `dyadicSqrtTwo`

Kind: definition. A square root of two in the algebraic closure of
the dyadic local field; tex 2726 and 3413–3438.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.dyadicSqrtTwo : AlgebraicClosure ℚ_[2]
'ZInQ.Contrib.RC53Assist.KummerFlat.dyadicSqrtTwo' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `dyadicSignCharacter`

Kind: definition. The continuous quadratic character of the actual
extension obtained by adjoining the square root of two to the dyadic
field; tex 2726 and 2791.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.dyadicSignCharacter : Field.absoluteGaloisGroup ℚ_[2] →* ℤˣ
'ZInQ.Contrib.RC53Assist.KummerFlat.dyadicSignCharacter' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `dyadicSignCharacterOpenKer`

Kind: instance, proved. The concrete quadratic character has open
kernel, as required of stage characters in tex 2781–2796.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.dyadicSignCharacterOpenKer :
  ZInQ.Manuscript.RC.CoefModules.IsOpenKer ZInQ.Contrib.RC53Assist.KummerFlat.dyadicSignCharacter
'ZInQ.Contrib.RC53Assist.KummerFlat.dyadicSignCharacterOpenKer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `dyadicZeroKummerCondition`

Kind: definition. The literal finite Kummer condition over `A₂`
for the elliptic curve `y² = x³ - x` over the dyadic field and the zero
equivariant map from its four-torsion into the free sign module. This
map is permitted by the coefficient-map interface of tex 3430–3438.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.dyadicZeroKummerCondition :
  ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef 2)
'ZInQ.Contrib.RC53Assist.KummerFlat.dyadicZeroKummerCondition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `quadraticStageCharacter`

Kind: definition. The scalar stage character obtained from an
integer-valued quadratic character; tex 2726 and 2791.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.quadraticStageCharacter {G : Type} [Group G] (χ : G →* ℤˣ) (i : ℕ) :
  G →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ
'ZInQ.Contrib.RC53Assist.KummerFlat.quadraticStageCharacter' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `quadraticStageCharacterOpenKer`

Kind: instance, proved. A quadratic character with open kernel
retains an open kernel at every coefficient stage; tex 2781–2796.

```text
ZInQ.Contrib.RC53Assist.KummerFlat.quadraticStageCharacterOpenKer {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (χ : G →* ℤˣ) [ZInQ.Manuscript.RC.CoefModules.IsOpenKer χ] (i : ℕ) :
  ZInQ.Manuscript.RC.CoefModules.IsOpenKer (ZInQ.Contrib.RC53Assist.KummerFlat.quadraticStageCharacter χ i)
'ZInQ.Contrib.RC53Assist.KummerFlat.quadraticStageCharacterOpenKer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
