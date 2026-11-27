# Exact completion theorem statements and axiom reports

The standalone source and the full audit both compile. The reports below are the unaltered type-printer and axiom-printer output.
The literature interfaces remain hypotheses, and the two raw-representation Tate readings remain explicitly named GLUE.

## Unfolded target and input interfaces

```lean
def ZInQ.Contrib.CloudB3RC53.ModularWeil.LiCarayolNewformOfModular : Prop :=
∀ (E : WeierstrassCurve ℚ),
  E.IsElliptic →
    ∀ (N : ℕ),
      0 < N →
        ∀ (f : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)) 2),
          (∀ (n : ℕ), 0 < n → (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑f) = ↑(E.LFunction n)) →
            ∃ M,
              ∃ (x : NeZero M),
                ∃ F,
                  M ∣ N ∧
                    F.χ = 1 ∧
                      ∀ (n : ℕ),
                        0 < n → (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = ↑(E.LFunction n)
def ZInQ.Contrib.RC53Assist.NewformGlueG0.Li1975StrongMultiplicityOneWeightTwo : Prop :=
∀ (M N : ℕ) [inst : NeZero M] [inst_1 : NeZero N] (F : HeckeRing.GL2.Newform M 2) (G : HeckeRing.GL2.Newform N 2),
  F.χ = 1 →
    G.χ = 1 →
      (∃ S,
          ∀ (p : ℕ),
            Nat.Prime p →
              p ∉ S →
                (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) =
                  (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑G.toCuspForm)) →
        M = N ∧ ∀ (τ : UpperHalfPlane), F.toCuspForm τ = G.toCuspForm τ
def ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.Shimura1973ConjugateEigenforms : Prop :=
∀ (M : ℕ) [inst : NeZero M] (F : HeckeRing.GL2.Newform M 2),
  F.χ = 1 →
    FiniteDimensional ℚ ↥(ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.coefficientField F) ∧
      ∀ (σ : ↥(ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.coefficientField F) →ₐ[ℚ] ℂ),
        ∃ g,
          ZInQ.Contrib.RC53Assist.NewformPeriods.IsNormalizedFullEigenformGamma0 M g ∧
            ∀ (n : ℕ),
              (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑g) =
                σ ⟨(PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm), ⋯⟩
def ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.Carayol1986RationalNewformEulerFactors : Prop :=
∀ (M : ℕ) [inst : NeZero M] (F : HeckeRing.GL2.Newform M 2) (hχ : F.χ = 1),
  (∀ (n : ℕ), ∃ b, (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = ↑b) →
    ∃ A,
      A.IsElliptic ∧
        ∀ (p : ℕ) (hp : Nat.Prime p),
          Polynomial.map (Int.castRingHom ℂ)
              (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.localPolynomialQ A
                (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp)) =
            ZInQ.Contrib.RC53Assist.NewformGlueG0.newformEulerPolynomial F hχ p
def ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.Faltings1983EulerFactorRigidityQ : Prop :=
∀ (E A : WeierstrassCurve ℚ),
  E.IsElliptic →
    A.IsElliptic →
      ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.LocalPolynomialsAgreeAlmostEverywhere E A →
        ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
          ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.localPolynomialQ E v =
            ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.localPolynomialQ A v
def ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Carayol1986ThmAWeightTwoQ : Prop :=
∀ (M : ℕ) [inst : NeZero M] (F : HeckeRing.GL2.Newform M 2),
  F.χ = 1 →
    ∃ K,
      ∃ (hK : NumberField ↥K) (hcoeff :
        ∀ (n : ℕ), (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) ∈ K),
        ∀ (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (lam : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)),
          ↑ℓ ∈ lam.asIdeal →
            ∃ ρ,
              (Continuous fun g =>
                  (LinearMap.toMatrix (Pi.basisFun (IsDedekindDomain.HeightOneSpectrum.adicCompletion (↥K) lam) (Fin 2))
                      (Pi.basisFun (IsDedekindDomain.HeightOneSpectrum.adicCompletion (↥K) lam) (Fin 2)))
                    (ρ g)) ∧
                ρ.IsIrreducible ∧
                  (∀ (p : ℕ),
                      Nat.Prime p →
                        ¬p ∣ M * ℓ →
                          ∀ (g : GlueC10.GQ),
                            GlueC10.IsFrobAt g p →
                              (LinearMap.trace (IsDedekindDomain.HeightOneSpectrum.adicCompletion (↥K) lam)
                                    (Fin 2 → IsDedekindDomain.HeightOneSpectrum.adicCompletion (↥K) lam))
                                  (ρ g) =
                                (algebraMap (↥K) (IsDedekindDomain.HeightOneSpectrum.adicCompletion (↥K) lam))
                                  ⟨(PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm), ⋯⟩) ∧
                    ∀ (p : ℕ),
                      Nat.Prime p →
                        p ≠ ℓ →
                          ∀ (D : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.LocalArithmeticFrobenius p),
                            ZInQ.Contrib.RC53Assist.NewformGlueG0.inertiaEulerPolynomial ρ
                                (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.inertiaAt D) D.element ⋯ =
                              1 -
                                  Polynomial.C
                                      ((algebraMap (↥K) (IsDedekindDomain.HeightOneSpectrum.adicCompletion (↥K) lam))
                                        ⟨(PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm), ⋯⟩) *
                                    Polynomial.X +
                                Polynomial.C (if p.Coprime M then ↑p else 0) * Polynomial.X ^ 2
def ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Carayol1986ThmARationalWeightTwo : Prop :=
∀ (M : ℕ) [inst : NeZero M] (F : HeckeRing.GL2.Newform M 2) (hχ : F.χ = 1) (b : ℕ → ℚ)
  (hb : ∀ (n : ℕ), (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = ↑(b n)) (ℓ : ℕ)
  [inst_1 : Fact (Nat.Prime ℓ)],
  Nonempty (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.CarayolRationalRealization F hχ b hb ℓ)
def ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Faltings1983Satz3EllipticQ : Prop :=
∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [inst : Fact (Nat.Prime ℓ)],
  IsSemisimpleModule (MonoidAlgebra ℚ_[ℓ] GlueC10.GQ)
    (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTateRep E ℓ).asModule
def ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.GlobalGoodReductionTraceReading : Prop :=
ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.GoodReductionFrobeniusTraceDictionaryQ →
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [inst : Fact (Nat.Prime ℓ)] (p : ℕ) (hp : Nat.Prime p),
    p ≠ ℓ →
      ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.GoodReductionAt E
          (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp) →
        (∀ (D : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.LocalArithmeticFrobenius p),
            ∀ i ∈ ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.inertiaAt D,
              (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTateRep E ℓ) i = 1) ∧
          ∀ (g : GlueC10.GQ),
            GlueC10.IsFrobAt g p →
              (LinearMap.trace ℚ_[ℓ] (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTate E ℓ))
                    ((ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTateRep E ℓ) g) =
                  ↑(E.LFunction p) ∧
                LinearMap.det ((ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTateRep E ℓ) g) = ↑p
def ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.BadReductionTatePolynomialReading : Prop :=
∀ (E : WeierstrassCurve ℚ) [inst : E.IsElliptic] (ℓ : ℕ) [inst_1 : Fact (Nat.Prime ℓ)] (p : ℕ) (hp : Nat.Prime p),
  p ≠ ℓ →
    ¬ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.GoodReductionAt E
          (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp) →
      ∀ (D : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.LocalArithmeticFrobenius p),
        ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.localTatePolynomial E ℓ D =
          Polynomial.map (Int.castRingHom ℚ_[ℓ])
            (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.localPolynomialQ E
              (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp))
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTate_finrank

Source: `GaloisCompletion.lean`, line 94.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTate_finrank (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ)
  [Fact (Nat.Prime ℓ)] : Module.finrank ℚ_[ℓ] (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTate E ℓ) = 2
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTate_finrank' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.extendedTate_finrank

Source: `GaloisCompletion.lean`, line 127.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.extendedTate_finrank (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ)
  [Fact (Nat.Prime ℓ)] (K : Type) [Field K] [Algebra ℚ_[ℓ] K] :
  Module.finrank K (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.extendedTate E ℓ K) = 2
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.extendedTate_finrank' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.continuous_integralTateBasis_equivFun

Source: `GaloisCompletion.lean`, line 136.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.continuous_integralTateBasis_equivFun (E : WeierstrassCurve ℚ)
  [E.IsElliptic] (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
  Continuous ⇑(ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.integralTateBasis E ℓ).equivFun
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.continuous_integralTateBasis_equivFun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.continuous_matrix_of_continuous_action

Source: `GaloisCompletion.lean`, line 156.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.continuous_matrix_of_continuous_action.{u_1, u_2, u_3, u_4}
  {R : Type u_1} {G : Type u_2} {V : Type u_3} {ι : Type u_4} [CommRing R] [TopologicalSpace R] [Monoid G]
  [TopologicalSpace G] [AddCommGroup V] [Module R V] [TopologicalSpace V] [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι R V) (hb : Continuous ⇑b.equivFun) (ρ : Representation R G V)
  (hρ : Continuous fun q => (ρ q.1) q.2) : Continuous fun g => (LinearMap.toMatrix b b) (ρ g)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.continuous_matrix_of_continuous_action' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.continuous_integralTateRep_matrix

Source: `GaloisCompletion.lean`, line 173.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.continuous_integralTateRep_matrix (E : WeierstrassCurve ℚ)
  [E.IsElliptic] (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
  Continuous fun g =>
    (LinearMap.toMatrix (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.integralTateBasis E ℓ)
        (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.integralTateBasis E ℓ))
      ((ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.integralTateRep E ℓ) g)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.continuous_integralTateRep_matrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTateRep_matrix

Source: `GaloisCompletion.lean`, line 185.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTateRep_matrix (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ)
  [Fact (Nat.Prime ℓ)] (g : GlueC10.GQ) :
  (LinearMap.toMatrix (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTateBasis E ℓ)
        (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTateBasis E ℓ))
      ((ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTateRep E ℓ) g) =
    ((LinearMap.toMatrix (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.integralTateBasis E ℓ)
            (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.integralTateBasis E ℓ))
          ((ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.integralTateRep E ℓ) g)).map
      ⇑(algebraMap ℤ_[ℓ] ℚ_[ℓ])
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTateRep_matrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.continuous_rationalTateRep_matrix

Source: `GaloisCompletion.lean`, line 197.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.continuous_rationalTateRep_matrix (E : WeierstrassCurve ℚ)
  [E.IsElliptic] (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
  Continuous fun g =>
    (LinearMap.toMatrix (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTateBasis E ℓ)
        (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTateBasis E ℓ))
      ((ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTateRep E ℓ) g)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.continuous_rationalTateRep_matrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.extendedTateRep_matrix

Source: `GaloisCompletion.lean`, line 207.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.extendedTateRep_matrix (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ)
  [Fact (Nat.Prime ℓ)] (K : Type) [Field K] [Algebra ℚ_[ℓ] K] (g : GlueC10.GQ) :
  (LinearMap.toMatrix (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.extendedTateBasis E ℓ K)
        (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.extendedTateBasis E ℓ K))
      ((ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.extendedTateRep E ℓ K) g) =
    ((LinearMap.toMatrix (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTateBasis E ℓ)
            (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTateBasis E ℓ))
          ((ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTateRep E ℓ) g)).map
      ⇑(algebraMap ℚ_[ℓ] K)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.extendedTateRep_matrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.continuous_extendedTateRep_matrix

Source: `GaloisCompletion.lean`, line 221.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.continuous_extendedTateRep_matrix (E : WeierstrassCurve ℚ)
  [E.IsElliptic] (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (K : Type) [Field K] [Algebra ℚ_[ℓ] K] [TopologicalSpace K]
  (hK : Continuous ⇑(algebraMap ℚ_[ℓ] K)) :
  Continuous fun g =>
    (LinearMap.toMatrix (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.extendedTateBasis E ℓ K)
        (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.extendedTateBasis E ℓ K))
      ((ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.extendedTateRep E ℓ K) g)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.continuous_extendedTateRep_matrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.goodReductionFrobeniusTraceDictionaryQ_proved

Source: `GaloisCompletion.lean`, line 234.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.goodReductionFrobeniusTraceDictionaryQ_proved :
  ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.GoodReductionFrobeniusTraceDictionaryQ
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.goodReductionFrobeniusTraceDictionaryQ_proved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.one_notMem

Source: `GaloisCompletion.lean`, line 309.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.one_notMem (P : Ideal GlueC10.Zbar) [hP : P.IsPrime] : 1 ∉ P
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.one_notMem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.natCast_mem

Source: `GaloisCompletion.lean`, line 315.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.natCast_mem (P : Ideal GlueC10.Zbar) (p : ℕ)
  (hPp : Ideal.under ℤ P = Ideal.span {↑p}) : ↑p ∈ P
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.natCast_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.exists_frac_or_inv

Source: `GaloisCompletion.lean`, line 325.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.exists_frac_or_inv (K : Type) [Field K] [NumberField K]
  (Q : Ideal (NumberField.RingOfIntegers K)) [Q.IsPrime] (hQ0 : Q ≠ ⊥) (x : K) (hx0 : x ≠ 0) :
  ∃ r, ∃ s ∉ Q, x * ↑s = ↑r ∨ x⁻¹ * ↑s = ↑r
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.exists_frac_or_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.locMem_or_inv

Source: `GaloisCompletion.lean`, line 374.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.locMem_or_inv (P : Ideal GlueC10.Zbar) [hP : P.IsPrime]
  (p : ℕ) (hp : Nat.Prime p) (hPp : Ideal.under ℤ P = Ideal.span {↑p})
  (x : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.Qbar) :
  ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.LocMem P x ∨
    ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.LocMem P x⁻¹
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.locMem_or_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.mem_zbarLoc

Source: `GaloisCompletion.lean`, line 435.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.mem_zbarLoc (P : Ideal GlueC10.Zbar) [hP : P.IsPrime]
  {p : ℕ} {hp : Nat.Prime p} {hPp : Ideal.under ℤ P = Ideal.span {↑p}}
  {x : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.Qbar} :
  x ∈ ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.zbarLoc P p hp hPp ↔
    ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.LocMem P x
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.mem_zbarLoc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.gZ_coe

Source: `GaloisCompletion.lean`, line 450.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.gZ_coe
  (g : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.GQ) (z : GlueC10.Zbar) :
  ↑(ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.gZ g z) = g ↑z
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.gZ_coe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.liesOver_and_isArithFrob

Source: `GaloisCompletion.lean`, line 455.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.liesOver_and_isArithFrob (P : Ideal GlueC10.Zbar)
  [hP : P.IsPrime] (h : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.GQ) (p : ℕ) (hp : Nat.Prime p)
  (hPp : Ideal.under ℤ P = Ideal.span {↑p}) (hh : ∀ (x y : GlueC10.Zbar), ↑y = h ↑x - ↑x ^ p → y ∈ P) :
  ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.LiesOver
      (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.zbarLoc P p hp hPp) p ∧
    ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.IsArithFrob h
      (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.zbarLoc P p hp hPp) p
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.liesOver_and_isArithFrob' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.place_of_isFrobAt

Source: `GaloisCompletion.lean`, line 538.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.place_of_isFrobAt
  (g : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.GQ) (p : ℕ) (hp : Nat.Prime p)
  (h : GlueC10.IsFrobAt g p) :
  ∃ v,
    ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.LiesOver v p ∧
      ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.IsArithFrob g v p
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.place_of_isFrobAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.exists_place_and_frobenius

Source: `GaloisCompletion.lean`, line 548.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.exists_place_and_frobenius (p : ℕ) (hp : Nat.Prime p) :
  ∃ v g,
    ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.LiesOver v p ∧
      ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.IsArithFrob g v p ∧ GlueC10.IsFrobAt g p
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Arithmetic.exists_place_and_frobenius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.coeff_mem

Source: `GaloisCompletion.lean`, line 611.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.coeff_mem {M : ℕ} [NeZero M] (F : HeckeRing.GL2.Newform M 2) (n : ℕ) :
  (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) ∈
    ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.coefficientField F
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.coeff_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.fullEigenform_divisor_newform

Source: `GaloisCompletion.lean`, line 634.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.fullEigenform_divisor_newform {M : ℕ} [NeZero M]
  (g : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 M)) 2)
  (hg : ZInQ.Contrib.RC53Assist.NewformPeriods.IsNormalizedFullEigenformGamma0 M g) :
  ∃ e,
    e.χ = 1 ∧
      (∀ (τ : UpperHalfPlane), e.toCuspForm τ = g τ) ∧
        (PowerSeries.coeff 1) (UpperHalfPlane.qExpansion 1 ⇑e.toCuspForm) = 1 ∧
          ∃ L,
            ∃ (x : NeZero L) (hLM : L ∣ M),
              ∃ G,
                G.χ = 1 ∧ ∀ (p : ℕ) (hp : Nat.Prime p) (hpM : p.Coprime M), G.eigenvalue ⟨p, ⋯⟩ ⋯ = e.eigenvalue ⟨p, ⋯⟩
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.fullEigenform_divisor_newform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.embedding_fixes_coefficients

Source: `GaloisCompletion.lean`, line 663.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.embedding_fixes_coefficients
  (hS : ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.Shimura1973ConjugateEigenforms)
  (hL : ZInQ.Contrib.RC53Assist.NewformGlueG0.Li1975StrongMultiplicityOneWeightTwo) (E : WeierstrassCurve ℚ) {M : ℕ}
  [NeZero M] (F : HeckeRing.GL2.Newform M 2) (hχ : F.χ = 1) (S : Finset ℕ)
  (hF :
    ∀ (p : ℕ),
      Nat.Prime p → p ∉ S → (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = ↑(E.LFunction p))
  (σ : ↥(ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.coefficientField F) →ₐ[ℚ] ℂ) (n : ℕ) :
  σ ⟨(PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm), ⋯⟩ =
    (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.embedding_fixes_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.coefficients_rational_of_almost_all_primes

Source: `GaloisCompletion.lean`, line 710.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.coefficients_rational_of_almost_all_primes
  (hS : ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.Shimura1973ConjugateEigenforms)
  (hL : ZInQ.Contrib.RC53Assist.NewformGlueG0.Li1975StrongMultiplicityOneWeightTwo) (E : WeierstrassCurve ℚ) {M : ℕ}
  [NeZero M] (F : HeckeRing.GL2.Newform M 2) (hχ : F.χ = 1) (S : Finset ℕ)
  (hF :
    ∀ (p : ℕ),
      Nat.Prime p → p ∉ S → (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = ↑(E.LFunction p))
  (n : ℕ) : ∃ b, (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = ↑b
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.coefficients_rational_of_almost_all_primes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.coefficientField_eq_bot_of_almost_all_primes

Source: `GaloisCompletion.lean`, line 740.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.coefficientField_eq_bot_of_almost_all_primes
  (hS : ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.Shimura1973ConjugateEigenforms)
  (hL : ZInQ.Contrib.RC53Assist.NewformGlueG0.Li1975StrongMultiplicityOneWeightTwo) (E : WeierstrassCurve ℚ) {M : ℕ}
  [NeZero M] (F : HeckeRing.GL2.Newform M 2) (hχ : F.χ = 1) (S : Finset ℕ)
  (hF :
    ∀ (p : ℕ),
      Nat.Prime p → p ∉ S → (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = ↑(E.LFunction p)) :
  ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.coefficientField F = ⊥
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.coefficientField_eq_bot_of_almost_all_primes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.liCarayolNewformOfModular_of_printed_corollaries

Source: `GaloisCompletion.lean`, line 787.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.liCarayolNewformOfModular_of_printed_corollaries
  (hS : ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.Shimura1973ConjugateEigenforms)
  (hL : ZInQ.Contrib.RC53Assist.NewformGlueG0.Li1975StrongMultiplicityOneWeightTwo)
  (hC : ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.Carayol1986RationalNewformEulerFactors)
  (hF : ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.Faltings1983EulerFactorRigidityQ) :
  ZInQ.Contrib.CloudB3RC53.ModularWeil.LiCarayolNewformOfModular
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.liCarayolNewformOfModular_of_printed_corollaries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.newformOfModularCurveGlue_of_printed_corollaries

Source: `GaloisCompletion.lean`, line 832.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.newformOfModularCurveGlue_of_printed_corollaries
  (hS : ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.Shimura1973ConjugateEigenforms)
  (hL : ZInQ.Contrib.RC53Assist.NewformGlueG0.Li1975StrongMultiplicityOneWeightTwo)
  (hC : ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.Carayol1986RationalNewformEulerFactors)
  (hF : ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.Faltings1983EulerFactorRigidityQ) :
  ZInQ.Contrib.RC53Assist.NewformPeriods.NewformOfModularCurveGlue
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.newformOfModularCurveGlue_of_printed_corollaries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.localArithmeticFrobenius_nonempty

Source: `GaloisCompletion.lean`, line 892.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.localArithmeticFrobenius_nonempty (p : ℕ) (hp : Nat.Prime p) :
  Nonempty (ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.LocalArithmeticFrobenius p)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.localArithmeticFrobenius_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.inertiaAt_normalized

Source: `GaloisCompletion.lean`, line 905.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.inertiaAt_normalized {p : ℕ}
  (D : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.LocalArithmeticFrobenius p) (i : GlueC10.GQ) :
  i ∈ ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.inertiaAt D →
    D.element⁻¹ * i * D.element ∈ ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.inertiaAt D
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.inertiaAt_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.tate_equiv_Carayol_of_almost_all_primes

Source: `GaloisCompletion.lean`, line 1062.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.tate_equiv_Carayol_of_almost_all_primes
  (hFa : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Faltings1983Satz3EllipticQ)
  (hG : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.GlobalGoodReductionTraceReading) (E : WeierstrassCurve ℚ)
  [E.IsElliptic] {M : ℕ} [NeZero M] (F : HeckeRing.GL2.Newform M 2) (hχ : F.χ = 1) (b : ℕ → ℚ)
  (hb : ∀ (n : ℕ), (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = ↑(b n)) (S : Finset ℕ)
  (hFp :
    ∀ (p : ℕ),
      Nat.Prime p → p ∉ S → (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = ↑(E.LFunction p))
  (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
  (R : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.CarayolRationalRealization F hχ b hb ℓ) :
  Nonempty ((ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalTateRep E ℓ).Equiv R.normalizedRep)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.tate_equiv_Carayol_of_almost_all_primes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.localTatePolynomial_eq_newform_of_comparison

Source: `GaloisCompletion.lean`, line 1103.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.localTatePolynomial_eq_newform_of_comparison
  (hFa : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Faltings1983Satz3EllipticQ)
  (hG : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.GlobalGoodReductionTraceReading) (E : WeierstrassCurve ℚ)
  [E.IsElliptic] {M : ℕ} [NeZero M] (F : HeckeRing.GL2.Newform M 2) (hχ : F.χ = 1) (b : ℕ → ℚ)
  (hb : ∀ (n : ℕ), (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = ↑(b n)) (S : Finset ℕ)
  (hFp :
    ∀ (p : ℕ),
      Nat.Prime p → p ∉ S → (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = ↑(E.LFunction p))
  (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
  (R : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.CarayolRationalRealization F hχ b hb ℓ) (p : ℕ)
  (hp : Nat.Prime p) (hpℓ : p ≠ ℓ) (D : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.LocalArithmeticFrobenius p) :
  ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.localTatePolynomial E ℓ D =
    ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalNewformPolynomial M ℓ b p
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.localTatePolynomial_eq_newform_of_comparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.inertiaEulerPolynomial_of_trivial_inertia

Source: `GaloisCompletion.lean`, line 1120.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.inertiaEulerPolynomial_of_trivial_inertia.{u_1, u_2, u_3}
  {K : Type u_1} {G : Type u_2} {V : Type u_3} [Field K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (ρ : Representation K G V) (I : Subgroup G) (g : G) (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I) (hI : ∀ i ∈ I, ρ i = 1) :
  ZInQ.Contrib.RC53Assist.NewformGlueG0.inertiaEulerPolynomial ρ I g hg = (ρ g).charpoly.reverse
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.inertiaEulerPolynomial_of_trivial_inertia' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.reversedCharpoly_rank_two

Source: `GaloisCompletion.lean`, line 1151.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.reversedCharpoly_rank_two.{u_1, u_2} {K : Type u_1} {V : Type u_2}
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (b : Module.Basis (Fin 2) K V) (f : Module.End K V) :
  (LinearMap.charpoly f).reverse =
    1 - Polynomial.C ((LinearMap.trace K V) f) * Polynomial.X + Polynomial.C (LinearMap.det f) * Polynomial.X ^ 2
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.reversedCharpoly_rank_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.localTatePolynomial_of_good

Source: `GaloisCompletion.lean`, line 1163.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.localTatePolynomial_of_good
  (hG : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.GlobalGoodReductionTraceReading) (E : WeierstrassCurve ℚ)
  [E.IsElliptic] (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (p : ℕ) (hp : Nat.Prime p) (hpℓ : p ≠ ℓ)
  (hgood :
    ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.GoodReductionAt E
      (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp))
  (D : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.LocalArithmeticFrobenius p) :
  ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.localTatePolynomial E ℓ D =
    Polynomial.map (Int.castRingHom ℚ_[ℓ])
      (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.localPolynomialQ E
        (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp))
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.localTatePolynomial_of_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.complexPolynomial_of_adicPolynomial

Source: `GaloisCompletion.lean`, line 1183.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.complexPolynomial_of_adicPolynomial (E : WeierstrassCurve ℚ) {M : ℕ}
  [NeZero M] (F : HeckeRing.GL2.Newform M 2) (hχ : F.χ = 1) (b : ℕ → ℚ)
  (hb : ∀ (n : ℕ), (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = ↑(b n)) (ℓ : ℕ)
  [Fact (Nat.Prime ℓ)] (p : ℕ) (hp : Nat.Prime p)
  (hP :
    Polynomial.map (Int.castRingHom ℚ_[ℓ])
        (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.localPolynomialQ E
          (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp)) =
      ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.rationalNewformPolynomial M ℓ b p) :
  Polynomial.map (Int.castRingHom ℂ)
      (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.localPolynomialQ E
        (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp)) =
    ZInQ.Contrib.RC53Assist.NewformGlueG0.newformEulerPolynomial F hχ p
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.complexPolynomial_of_adicPolynomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.exists_auxiliary_prime_ne

Source: `GaloisCompletion.lean`, line 1221.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.exists_auxiliary_prime_ne (p : ℕ) : ∃ ℓ, Nat.Prime ℓ ∧ p ≠ ℓ
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.exists_auxiliary_prime_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.liCarayolNewformOfModular_of_representations

Source: `GaloisCompletion.lean`, line 1232.

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.liCarayolNewformOfModular_of_representations
  (hS : ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.Shimura1973ConjugateEigenforms)
  (hL : ZInQ.Contrib.RC53Assist.NewformGlueG0.Li1975StrongMultiplicityOneWeightTwo)
  (hC : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Carayol1986ThmARationalWeightTwo)
  (hFa : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.Faltings1983Satz3EllipticQ)
  (hG : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.GlobalGoodReductionTraceReading)
  (hB : ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.BadReductionTatePolynomialReading) :
  ZInQ.Contrib.CloudB3RC53.ModularWeil.LiCarayolNewformOfModular
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion.liCarayolNewformOfModular_of_representations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
