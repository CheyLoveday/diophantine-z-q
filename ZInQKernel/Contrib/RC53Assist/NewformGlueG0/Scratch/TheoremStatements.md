# Exact theorem statements and axiom reports

All four source files and the integrated comparison were checked together.
The statements and reports below are the unaltered type-printer and axiom-printer output.
Printed propositions used as parameters remain parameters; they are not new axioms.

## Unfolded propositions

```lean
def GlueC10.BrauerNesbittChar0 : Prop :=
∀ (k G V W : Type) [inst : Field k] [CharZero k] [inst_2 : Group G] [inst_3 : AddCommGroup V] [inst_4 : Module k V]
  [FiniteDimensional k V] [inst_6 : AddCommGroup W] [inst_7 : Module k W] [FiniteDimensional k W]
  (ρ : Representation k G V) (σ : Representation k G W),
  IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
    IsSemisimpleModule (MonoidAlgebra k G) σ.asModule →
      (∀ (g : G), (LinearMap.trace k V) (ρ g) = (LinearMap.trace k W) (σ g)) →
        Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule)
def ZInQ.Contrib.RC53Assist.NewformGlueG0.Li1975BadPrimeWeightTwo : Prop :=
∀ (M : ℕ) [inst : NeZero M] (F : HeckeRing.GL2.Newform M 2),
  F.χ = 1 →
    ∀ (p : ℕ),
      Nat.Prime p →
        p ∣ M →
          (p ^ 2 ∣ M → (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = 0) ∧
            (¬p ^ 2 ∣ M → (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) ^ 2 = 1)
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
```

## ofPowerSeries_apply_eq_one_of_not_dvd

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.ofPowerSeries_apply_eq_one_of_not_dvd.{u_1} {B : Type u_1} [CommSemiring B]
  {q n : ℕ} (hq : 1 < q) (f : PowerSeries B) (hf : PowerSeries.constantCoeff f = 1) (hqn : ¬q ∣ n) :
  ((ArithmeticFunction.ofPowerSeries q) f) n = 1 n
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.ofPowerSeries_apply_eq_one_of_not_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ofPowerSeries_mul_apply_of_not_dvd

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.ofPowerSeries_mul_apply_of_not_dvd.{u_1} {B : Type u_1} [CommSemiring B] {q n : ℕ}
  (hq : 1 < q) (f : PowerSeries B) (hf : PowerSeries.constantCoeff f = 1) (hqn : ¬q ∣ n) (g : ArithmeticFunction B) :
  ((ArithmeticFunction.ofPowerSeries q) f * g) n = g n
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.ofPowerSeries_mul_apply_of_not_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## finsetProduct_mul_apply_of_forall_not_dvd

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.finsetProduct_mul_apply_of_forall_not_dvd.{u_1, u_2} {B : Type u_1} {ι : Type u_2}
  [CommSemiring B] (q : ι → ℕ) (f : ι → PowerSeries B) (hq : ∀ (i : ι), 1 < q i)
  (hf : ∀ (i : ι), PowerSeries.constantCoeff (f i) = 1) (s : Finset ι) (n : ℕ) (hqn : ∀ i ∈ s, ¬q i ∣ n)
  (g : ArithmeticFunction B) : ((∏ i ∈ s, (ArithmeticFunction.ofPowerSeries (q i)) (f i)) * g) n = g n
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.finsetProduct_mul_apply_of_forall_not_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## eulerProduct_at_prime_pow

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.eulerProduct_at_prime_pow.{u_1, u_2} {B : Type u_1} {ι : Type u_2}
  [CommSemiring B] (q : ι → ℕ) [Northcott q] (hq : ∀ (i : ι), Nat.Prime (q i)) (hinj : Function.Injective q)
  (f : ι → PowerSeries B) (hf : ∀ (i : ι), PowerSeries.constantCoeff (f i) = 1) (i : ι) (r : ℕ) :
  (ArithmeticFunction.eulerProduct fun j => (ArithmeticFunction.ofPowerSeries (q j)) (f j)) (q i ^ r) =
    (PowerSeries.coeff r) (f i)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.eulerProduct_at_prime_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## lFunction_isMultiplicative

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.lFunction_isMultiplicative (E : WeierstrassCurve ℚ) : E.LFunction.IsMultiplicative
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.lFunction_isMultiplicative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## lFunction_one

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.lFunction_one (E : WeierstrassCurve ℚ) : E.LFunction 1 = 1
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.lFunction_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## lFunction_prime_pow

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.lFunction_prime_pow (E : WeierstrassCurve ℚ) (p : ℕ) (hp : Nat.Prime p) (r : ℕ) :
  E.LFunction (p ^ r) =
    (PowerSeries.coeff r)
      (WeierstrassCurve.localPowerSeries
        (↥(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp)))
        (E.baseChange
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp))))
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.lFunction_prime_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## reciprocal_quadratic_recurrence

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.reciprocal_quadratic_recurrence (a d : ℤ) (r : ℕ) :
  have P := 1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C d * PowerSeries.X ^ 2;
  (PowerSeries.coeff (r + 2)) (P.invOfUnit 1) =
    a * (PowerSeries.coeff (r + 1)) (P.invOfUnit 1) - d * (PowerSeries.coeff r) (P.invOfUnit 1)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.reciprocal_quadratic_recurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## lFunction_good_prime_pow_recurrence

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.lFunction_good_prime_pow_recurrence (E : WeierstrassCurve ℚ) (p : ℕ)
  (hp : Nat.Prime p)
  (hgood :
    ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.GoodReductionAt E
      (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp))
  (r : ℕ) : E.LFunction (p ^ (r + 2)) = E.LFunction p * E.LFunction (p ^ (r + 1)) - ↑p * E.LFunction (p ^ r)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.lFunction_good_prime_pow_recurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## lFunction_good_prime_mul

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.lFunction_good_prime_mul (E : WeierstrassCurve ℚ) (p : ℕ) (hp : Nat.Prime p)
  (hgood :
    ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.GoodReductionAt E
      (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp))
  (m : ℕ) : E.LFunction (p * m) = E.LFunction p * E.LFunction m - if p ∣ m then ↑p * E.LFunction (m / p) else 0
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.lFunction_good_prime_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## localPolynomial_quadratic_shape

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.localPolynomial_quadratic_shape.{u_1, u_2} (R : Type u_1) [CommRing R]
  [IsDomain R] [IsDiscreteValuationRing R] {K : Type u_2} [Field K] [Algebra R K] [IsFractionRing R K]
  (E : WeierstrassCurve K) :
  WeierstrassCurve.localPolynomial R E =
    1 - Polynomial.C (-(WeierstrassCurve.localPolynomial R E).coeff 1) * Polynomial.X +
      Polynomial.C ((WeierstrassCurve.localPolynomial R E).coeff 2) * Polynomial.X ^ 2
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.localPolynomial_quadratic_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## localPolynomialQ_shape

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.localPolynomialQ_shape (E : WeierstrassCurve ℚ) (p : ℕ) (hp : Nat.Prime p) :
  ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.localPolynomialQ E
      (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp) =
    1 - Polynomial.C (E.LFunction p) * Polynomial.X +
      Polynomial.C
          ((ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.localPolynomialQ E
                (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp)).coeff
            2) *
        Polynomial.X ^ 2
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.localPolynomialQ_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## lFunction_prime_pow_recurrence

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.lFunction_prime_pow_recurrence (E : WeierstrassCurve ℚ) (p : ℕ) (hp : Nat.Prime p)
  (r : ℕ) :
  E.LFunction (p ^ (r + 2)) =
    E.LFunction p * E.LFunction (p ^ (r + 1)) -
      (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.localPolynomialQ E
              (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp)).coeff
          2 *
        E.LFunction (p ^ r)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.lFunction_prime_pow_recurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## arithmeticFunction_eq_of_prime_recurrences

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.arithmeticFunction_eq_of_prime_recurrences.{u_1} {B : Type u_1} [CommRing B]
  (a b : ArithmeticFunction B) (ha : a.IsMultiplicative) (hb : b.IsMultiplicative) (d : ℕ → B)
  (hp : ∀ (p : ℕ), Nat.Prime p → a p = b p)
  (har : ∀ (p : ℕ), Nat.Prime p → ∀ (r : ℕ), a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - d p * a (p ^ r))
  (hbr : ∀ (p : ℕ), Nat.Prime p → ∀ (r : ℕ), b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - d p * b (p ^ r)) : a = b
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.arithmeticFunction_eq_of_prime_recurrences' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## modular_coefficients_all

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.modular_coefficients_all {N : ℕ} [NeZero N] (E : WeierstrassCurve ℚ)
  (f : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)) 2)
  (hf : ∀ (n : ℕ), 0 < n → (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑f) = ↑(E.LFunction n)) (n : ℕ) :
  (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑f) = ↑(E.LFunction n)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.modular_coefficients_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## modular_form_normalized

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.modular_form_normalized {N : ℕ} (E : WeierstrassCurve ℚ)
  (f : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)) 2)
  (hf : ∀ (n : ℕ), 0 < n → (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑f) = ↑(E.LFunction n)) :
  (PowerSeries.coeff 1) (UpperHalfPlane.qExpansion 1 ⇑f) = 1
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.modular_form_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## modular_restrict_hecke_good

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.modular_restrict_hecke_good {N : ℕ} [NeZero N] (E : WeierstrassCurve ℚ)
  (f : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)) 2)
  (hf : ∀ (n : ℕ), 0 < n → (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑f) = ↑(E.LFunction n)) (p : ℕ)
  (hp : Nat.Prime p) (hpN : p.Coprime N)
  (hgood :
    ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.GoodReductionAt E
      (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp)) :
  (HeckeRing.GL2.heckeTCuspNat 2 p) ↑((TauCeti.cuspFormCharSpaceOneEquiv N 2).symm f) =
    ↑(E.LFunction p) • ↑((TauCeti.cuspFormCharSpaceOneEquiv N 2).symm f)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.modular_restrict_hecke_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## modular_heckeGamma0_good

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.modular_heckeGamma0_good {N : ℕ} [NeZero N] (E : WeierstrassCurve ℚ)
  (f : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)) 2)
  (hf : ∀ (n : ℕ), 0 < n → (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑f) = ↑(E.LFunction n)) (p : ℕ)
  (hp : Nat.Prime p) (hpN : p.Coprime N)
  (hgood :
    ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.GoodReductionAt E
      (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp)) :
  (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.heckeGamma0 N p) f = ↑(E.LFunction p) • f
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.modular_heckeGamma0_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## modular_hecke_almost_all

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.modular_hecke_almost_all {N : ℕ} [NeZero N] (E : WeierstrassCurve ℚ)
  (hE : E.IsElliptic) (f : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)) 2)
  (hf : ∀ (n : ℕ), 0 < n → (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑f) = ↑(E.LFunction n)) :
  (PowerSeries.coeff 1) (UpperHalfPlane.qExpansion 1 ⇑f) = 1 ∧
    ∃ S,
      ∀ (p : ℕ),
        Nat.Prime p →
          p.Coprime N →
            p ∉ S → (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.heckeGamma0 N p) f = ↑(E.LFunction p) • f
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.modular_hecke_almost_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## exists_newform_of_cofinite_prime_eigen

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.exists_newform_of_cofinite_prime_eigen {N : ℕ} [NeZero N] {k : ℤ}
  {χ : (ZMod N)ˣ →* ℂˣ}
  {F : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma1 N)) k}
  (hFχ : F ∈ cuspFormCharSpace k χ) (hF0 : F ≠ 0) (S : Finset ℕ) (a : ℕ → ℂ)
  (hF : ∀ (p : ℕ) (hp : Nat.Prime p), p.Coprime N → p ∉ S → (HeckeRing.GL2.heckeTCuspNat k p) F = a p • F) :
  ∃ M,
    ∃ (x : NeZero M) (hMN : M ∣ N),
      ∃ g,
        g.χ.comp (ZMod.unitsMap hMN) = χ ∧
          ∀ (p : ℕ) (hp : Nat.Prime p) (hpN : p.Coprime N), p ∉ S → g.eigenvalue ⟨p, ⋯⟩ ⋯ = a p
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.exists_newform_of_cofinite_prime_eigen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## exists_newform_almost_all_prime_coeff

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.exists_newform_almost_all_prime_coeff (E : WeierstrassCurve ℚ) (hE : E.IsElliptic)
  (N : ℕ) (hN : 0 < N) (f : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)) 2)
  (hf : ∀ (n : ℕ), 0 < n → (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑f) = ↑(E.LFunction n)) :
  ∃ M,
    ∃ (x : NeZero M),
      ∃ g,
        M ∣ N ∧
          g.χ = 1 ∧
            ∃ S,
              ∀ (p : ℕ),
                Nat.Prime p →
                  p ∉ S → (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑g.toCuspForm) = ↑(E.LFunction p)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.exists_newform_almost_all_prime_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## exists_gamma0_full_eigenform_almost_all

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.exists_gamma0_full_eigenform_almost_all (E : WeierstrassCurve ℚ)
  (hE : E.IsElliptic) (N : ℕ) (hN : 0 < N)
  (f : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)) 2)
  (hf : ∀ (n : ℕ), 0 < n → (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑f) = ↑(E.LFunction n)) :
  ∃ M,
    ∃ (x : NeZero M),
      ∃ g,
        M ∣ N ∧
          ZInQ.Contrib.RC53Assist.NewformPeriods.IsNormalizedFullEigenformGamma0 M g ∧
            ∃ S,
              ∀ (p : ℕ), Nat.Prime p → p ∉ S → (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑g) = ↑(E.LFunction p)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.exists_gamma0_full_eigenform_almost_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## newformCoefficients_apply

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.newformCoefficients_apply {M : ℕ} [NeZero M] (F : HeckeRing.GL2.Newform M 2)
  (n : ℕ) :
  (ZInQ.Contrib.RC53Assist.NewformGlueG0.newformCoefficients F) n =
    (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.newformCoefficients_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## newformCoefficients_isMultiplicative

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.newformCoefficients_isMultiplicative {M : ℕ} [NeZero M]
  (F : HeckeRing.GL2.Newform M 2) : (ZInQ.Contrib.RC53Assist.NewformGlueG0.newformCoefficients F).IsMultiplicative
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.newformCoefficients_isMultiplicative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## newform_prime_pow_recurrence

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.newform_prime_pow_recurrence {M : ℕ} [NeZero M] (F : HeckeRing.GL2.Newform M 2)
  (hχ : F.χ = 1) (p : ℕ) (hp : Nat.Prime p) (r : ℕ) :
  (PowerSeries.coeff (p ^ (r + 2))) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) =
    (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) *
        (PowerSeries.coeff (p ^ (r + 1))) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) -
      (if p.Coprime M then ↑p else 0) * (PowerSeries.coeff (p ^ r)) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.newform_prime_pow_recurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## newform_prime_pow_coeff_of_local_polynomial

Source: `HeckeBridge.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.newform_prime_pow_coeff_of_local_polynomial (E : WeierstrassCurve ℚ) {M : ℕ}
  [NeZero M] (F : HeckeRing.GL2.Newform M 2) (hχ : F.χ = 1) (p : ℕ) (hp : Nat.Prime p)
  (hlocal :
    Polynomial.map (Int.castRingHom ℂ)
        (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.localPolynomialQ E
          (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp)) =
      ZInQ.Contrib.RC53Assist.NewformGlueG0.newformEulerPolynomial F hχ p)
  (r : ℕ) : (PowerSeries.coeff (p ^ r)) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = ↑(E.LFunction (p ^ r))
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.newform_prime_pow_coeff_of_local_polynomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## hom_from_isotypic_eq_zero

Source: `BrauerNesbitt.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.hom_from_isotypic_eq_zero.{u_1, u_2, u_3, u_4} {R : Type u_1} {A : Type u_2}
  {B : Type u_3} {S : Type u_4} [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup S]
  [Module R S] [IsSemisimpleModule R A] (hA : IsIsotypicOfType R A S) (hno : ∀ (f : S →ₗ[R] B), f = 0) (f : A →ₗ[R] B) :
  f = 0
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.hom_from_isotypic_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## hom_to_isotypic_eq_zero

Source: `BrauerNesbitt.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.hom_to_isotypic_eq_zero.{u_1, u_2, u_3, u_4} {R : Type u_1} {A : Type u_2}
  {B : Type u_3} {S : Type u_4} [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup S]
  [Module R S] [IsSimpleModule R S] [IsSemisimpleModule R B] (hA : IsIsotypicOfType R A S)
  (hno : ∀ (f : S →ₗ[R] B), f = 0) (f : B →ₗ[R] A) : f = 0
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.hom_to_isotypic_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## firstProjection_commutes

Source: `BrauerNesbitt.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.firstProjection_commutes.{u_1, u_2, u_3} {R : Type u_1} {A : Type u_2}
  {B : Type u_3} [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] (hAB : ∀ (f : A →ₗ[R] B), f = 0)
  (hBA : ∀ (f : B →ₗ[R] A), f = 0) (f : Module.End R (A × B)) (v : A × B) :
  ZInQ.Contrib.RC53Assist.NewformGlueG0.firstProjection (f v) =
    f (ZInQ.Contrib.RC53Assist.NewformGlueG0.firstProjection v)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.firstProjection_commutes' depends on axioms: [propext, Quot.sound]
```

## exists_scalar_first_projection

Source: `BrauerNesbitt.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.exists_scalar_first_projection.{u_1, u_2, u_3, u_4} {R : Type u_1} {A : Type u_2}
  {B : Type u_3} [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] {K : Type u_4} [Field K]
  [Module K A] [SMulCommClass R K A] [Module K B] [SMulCommClass R K B] [FiniteDimensional K A] [FiniteDimensional K B]
  [IsSemisimpleModule R A] [IsSemisimpleModule R B] (hAB : ∀ (f : A →ₗ[R] B), f = 0) (hBA : ∀ (f : B →ₗ[R] A), f = 0) :
  ∃ r, (∀ (x : A), r • x = x) ∧ ∀ (y : B), r • y = 0
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.exists_scalar_first_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## actionTrace_one

Source: `BrauerNesbitt.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace_one.{u_1, u_2, u_3} (K : Type u_1) (R : Type u_2) (V : Type u_3)
  [Field K] [Ring R] [AddCommGroup V] [Module K V] [Module R V] [SMulCommClass R K V] [FiniteDimensional K V] :
  ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace K R V 1 = ↑(Module.finrank K V)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## actionTrace_congr

Source: `BrauerNesbitt.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace_congr.{u_1, u_2, u_3, u_4} {K : Type u_1} {R : Type u_2}
  {V : Type u_3} [Field K] [Ring R] [Algebra K R] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower K R V]
  [SMulCommClass R K V] {W : Type u_4} [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower K R W]
  [SMulCommClass R K W] (e : V ≃ₗ[R] W) (r : R) :
  ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace K R V r = ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace K R W r
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## actionTrace_prod

Source: `BrauerNesbitt.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace_prod.{u_1, u_2, u_3, u_4} {K : Type u_1} {R : Type u_2} {V : Type u_3}
  [Field K] [Ring R] [AddCommGroup V] [Module K V] [Module R V] [SMulCommClass R K V] {W : Type u_4} [AddCommGroup W]
  [Module K W] [Module R W] [SMulCommClass R K W] [FiniteDimensional K V] [FiniteDimensional K W] (r : R) :
  ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace K R (V × W) r =
    ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace K R V r +
      ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace K R W r
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## exists_nonzero_hom_of_actionTrace_eq

Source: `BrauerNesbitt.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.exists_nonzero_hom_of_actionTrace_eq.{u_1, u_2, u_3, u_4} {K : Type u_1}
  {R : Type u_2} {V : Type u_3} {W : Type u_4} [Field K] [CharZero K] [Ring R] [Algebra K R] [AddCommGroup V]
  [Module K V] [Module R V] [IsScalarTower K R V] [SMulCommClass R K V] [FiniteDimensional K V] [IsSemisimpleModule R V]
  [AddCommGroup W] [Module K W] [Module R W] [SMulCommClass R K W] [FiniteDimensional K W] [IsSemisimpleModule R W]
  (htr :
    ∀ (r : R),
      ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace K R V r =
        ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace K R W r)
  (S : Submodule R V) [IsSimpleModule R ↥S] : ∃ f, f ≠ 0
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.exists_nonzero_hom_of_actionTrace_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## semisimple_actionTrace_comparison

Source: `BrauerNesbitt.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.semisimple_actionTrace_comparison (K R : Type) [Field K] [CharZero K] [Ring R]
  [Algebra K R] (V W : Type) [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower K R V] [SMulCommClass R K V]
  [FiniteDimensional K V] [IsSemisimpleModule R V] [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower K R W]
  [SMulCommClass R K W] [FiniteDimensional K W] [IsSemisimpleModule R W]
  (htr :
    ∀ (r : R),
      ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace K R V r =
        ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace K R W r) :
  Nonempty (V ≃ₗ[R] W)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.semisimple_actionTrace_comparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## actionTrace_asModule

Source: `BrauerNesbitt.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace_asModule.{u_1, u_2, u_3} {K : Type u_1} {G : Type u_2} {V : Type u_3}
  [Field K] [Monoid G] [AddCommGroup V] [Module K V] (ρ : Representation K G V) (a : MonoidAlgebra K G) :
  ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace K (MonoidAlgebra K G) ρ.asModule a =
    (LinearMap.trace K V) (ρ.asAlgebraHom a)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.actionTrace_asModule' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## trace_on_groupAlgebra_eq

Source: `BrauerNesbitt.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.trace_on_groupAlgebra_eq.{u_1, u_2, u_3, u_4} {K : Type u_1} {G : Type u_2}
  {V : Type u_3} {W : Type u_4} [Field K] [Monoid G] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  (ρ : Representation K G V) (σ : Representation K G W)
  (htr : ∀ (g : G), (LinearMap.trace K V) (ρ g) = (LinearMap.trace K W) (σ g)) (a : MonoidAlgebra K G) :
  (LinearMap.trace K V) (ρ.asAlgebraHom a) = (LinearMap.trace K W) (σ.asAlgebraHom a)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.trace_on_groupAlgebra_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## brauerNesbittChar0

Source: `BrauerNesbitt.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.brauerNesbittChar0 : GlueC10.BrauerNesbittChar0
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.brauerNesbittChar0' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## galois_comparison_from_frobenius

Source: `BrauerNesbitt.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.galois_comparison_from_frobenius (K V W ι κ : Type) [Field K] [CharZero K]
  [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (bV : Module.Basis ι K V) (bW : Module.Basis κ K W) (ρ : Representation K GlueC10.GQ V)
  (σ : Representation K GlueC10.GQ W) (hρc : Continuous fun g => (LinearMap.toMatrix bV bV) (ρ g))
  (hσc : Continuous fun g => (LinearMap.toMatrix bW bW) (σ g))
  (hρ : IsSemisimpleModule (MonoidAlgebra K GlueC10.GQ) ρ.asModule)
  (hσ : IsSemisimpleModule (MonoidAlgebra K GlueC10.GQ) σ.asModule) (S : Finset ℕ)
  (htr :
    ∀ (g : GlueC10.GQ) (p : ℕ),
      Nat.Prime p → p ∉ S → GlueC10.IsFrobAt g p → (LinearMap.trace K V) (ρ g) = (LinearMap.trace K W) (σ g)) :
  Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra K GlueC10.GQ] σ.asModule)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.galois_comparison_from_frobenius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## frobeniusElements_dense

Source: `FrobeniusLocal.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.frobeniusElements_dense (S : Finset ℕ) :
  Dense (ZInQ.Contrib.RC53Assist.NewformGlueG0.frobeniusElements S)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.frobeniusElements_dense' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## trace_eq_of_frobenius

Source: `FrobeniusLocal.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.trace_eq_of_frobenius.{u_1, u_2, u_3, u_4, u_5} {K : Type u_1} {V : Type u_2}
  {W : Type u_3} {ι : Type u_4} {κ : Type u_5} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (bV : Module.Basis ι K V) (bW : Module.Basis κ K W)
  (ρ : Representation K GlueC10.GQ V) (σ : Representation K GlueC10.GQ W)
  (hρc : Continuous fun g => (LinearMap.toMatrix bV bV) (ρ g))
  (hσc : Continuous fun g => (LinearMap.toMatrix bW bW) (σ g)) (S : Finset ℕ)
  (htr :
    ∀ (g : GlueC10.GQ) (p : ℕ),
      Nat.Prime p → p ∉ S → GlueC10.IsFrobAt g p → (LinearMap.trace K V) (ρ g) = (LinearMap.trace K W) (σ g))
  (g : GlueC10.GQ) : (LinearMap.trace K V) (ρ g) = (LinearMap.trace K W) (σ g)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.trace_eq_of_frobenius' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## representationEquiv_of_BN_frobenius

Source: `FrobeniusLocal.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.representationEquiv_of_BN_frobenius (hBN : GlueC10.BrauerNesbittChar0)
  (K V W ι κ : Type) [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] (bV : Module.Basis ι K V) (bW : Module.Basis κ K W) (ρ : Representation K GlueC10.GQ V)
  (σ : Representation K GlueC10.GQ W) (hρc : Continuous fun g => (LinearMap.toMatrix bV bV) (ρ g))
  (hσc : Continuous fun g => (LinearMap.toMatrix bW bW) (σ g))
  (hρ : IsSemisimpleModule (MonoidAlgebra K GlueC10.GQ) ρ.asModule)
  (hσ : IsSemisimpleModule (MonoidAlgebra K GlueC10.GQ) σ.asModule) (S : Finset ℕ)
  (htr :
    ∀ (g : GlueC10.GQ) (p : ℕ),
      Nat.Prime p → p ∉ S → GlueC10.IsFrobAt g p → (LinearMap.trace K V) (ρ g) = (LinearMap.trace K W) (σ g)) :
  Nonempty (ρ.Equiv σ)
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.representationEquiv_of_BN_frobenius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## map_mem_fixedInertia

Source: `FrobeniusLocal.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.map_mem_fixedInertia.{u_1, u_2, u_3, u_4} {K : Type u_1} {G : Type u_2}
  {V : Type u_3} {W : Type u_4} [Field K] [Group G] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {ρ : Representation K G V} {σ : Representation K G W} (e : ρ.Equiv σ) (I : Subgroup G) {v : V}
  (hv : v ∈ ZInQ.Contrib.RC53Assist.NewformGlueG0.fixedInertia ρ I) :
  e v ∈ ZInQ.Contrib.RC53Assist.NewformGlueG0.fixedInertia σ I
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.map_mem_fixedInertia' depends on axioms: [propext, Quot.sound]
```

## fixedInertia_stable

Source: `FrobeniusLocal.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.fixedInertia_stable.{u_1, u_2, u_3} {K : Type u_1} {G : Type u_2} {V : Type u_3}
  [Field K] [Group G] [AddCommGroup V] [Module K V] (ρ : Representation K G V) (I : Subgroup G) (g : G)
  (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I) {v : V} (hv : v ∈ ZInQ.Contrib.RC53Assist.NewformGlueG0.fixedInertia ρ I) :
  (ρ g) v ∈ ZInQ.Contrib.RC53Assist.NewformGlueG0.fixedInertia ρ I
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.fixedInertia_stable' depends on axioms: [propext, Quot.sound]
```

## inertiaFrobenius_conj

Source: `FrobeniusLocal.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.inertiaFrobenius_conj.{u_1, u_2, u_3, u_4} {K : Type u_1} {G : Type u_2}
  {V : Type u_3} {W : Type u_4} [Field K] [Group G] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {ρ : Representation K G V} {σ : Representation K G W} (e : ρ.Equiv σ) (I : Subgroup G) (g : G)
  (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I) :
  (ZInQ.Contrib.RC53Assist.NewformGlueG0.fixedInertiaEquiv e I).conj
      (ZInQ.Contrib.RC53Assist.NewformGlueG0.inertiaFrobenius ρ I g hg) =
    ZInQ.Contrib.RC53Assist.NewformGlueG0.inertiaFrobenius σ I g hg
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.inertiaFrobenius_conj' depends on axioms: [propext, Quot.sound]
```

## inertiaEulerPolynomial_eq_of_equiv

Source: `FrobeniusLocal.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.inertiaEulerPolynomial_eq_of_equiv.{u_1, u_2, u_3, u_4} {K : Type u_1}
  {G : Type u_2} {V : Type u_3} {W : Type u_4} [Field K] [Group G] [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W] [FiniteDimensional K V] [FiniteDimensional K W] {ρ : Representation K G V} {σ : Representation K G W}
  (e : ρ.Equiv σ) (I : Subgroup G) (g : G) (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I) :
  ZInQ.Contrib.RC53Assist.NewformGlueG0.inertiaEulerPolynomial ρ I g hg =
    ZInQ.Contrib.RC53Assist.NewformGlueG0.inertiaEulerPolynomial σ I g hg
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.inertiaEulerPolynomial_eq_of_equiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## localFactors_eq_of_BN_frobenius

Source: `FrobeniusLocal.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.localFactors_eq_of_BN_frobenius (hBN : GlueC10.BrauerNesbittChar0)
  (K V W ι κ : Type) [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] (bV : Module.Basis ι K V) (bW : Module.Basis κ K W) (ρ : Representation K GlueC10.GQ V)
  (σ : Representation K GlueC10.GQ W) (hρc : Continuous fun g => (LinearMap.toMatrix bV bV) (ρ g))
  (hσc : Continuous fun g => (LinearMap.toMatrix bW bW) (σ g))
  (hρ : IsSemisimpleModule (MonoidAlgebra K GlueC10.GQ) ρ.asModule)
  (hσ : IsSemisimpleModule (MonoidAlgebra K GlueC10.GQ) σ.asModule) (S : Finset ℕ)
  (htr :
    ∀ (g : GlueC10.GQ) (p : ℕ),
      Nat.Prime p → p ∉ S → GlueC10.IsFrobAt g p → (LinearMap.trace K V) (ρ g) = (LinearMap.trace K W) (σ g))
  (I : Subgroup GlueC10.GQ) (g : GlueC10.GQ) (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I) :
  ZInQ.Contrib.RC53Assist.NewformGlueG0.inertiaEulerPolynomial ρ I g hg =
    ZInQ.Contrib.RC53Assist.NewformGlueG0.inertiaEulerPolynomial σ I g hg
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.localFactors_eq_of_BN_frobenius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## newform_bad_prime_sign

Source: `PrintedInputs.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.newform_bad_prime_sign
  (hLi : ZInQ.Contrib.RC53Assist.NewformGlueG0.Li1975BadPrimeWeightTwo) {M : ℕ} [NeZero M]
  (F : HeckeRing.GL2.Newform M 2) (hχ : F.χ = 1) (p : ℕ) (hp : Nat.Prime p) (hpM : p ∣ M) (hpsq : ¬p ^ 2 ∣ M) :
  (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = 1 ∨
    (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = -1
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.newform_bad_prime_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## newform_bad_prime_values

Source: `PrintedInputs.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.newform_bad_prime_values
  (hLi : ZInQ.Contrib.RC53Assist.NewformGlueG0.Li1975BadPrimeWeightTwo) {M : ℕ} [NeZero M]
  (F : HeckeRing.GL2.Newform M 2) (hχ : F.χ = 1) (p : ℕ) (hp : Nat.Prime p) (hpM : p ∣ M) :
  (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = 1 ∨
    (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = -1 ∨
      (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = 0
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.newform_bad_prime_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## newform_bad_operator_values

Source: `PrintedInputs.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.newform_bad_operator_values
  (hLi : ZInQ.Contrib.RC53Assist.NewformGlueG0.Li1975BadPrimeWeightTwo) {M : ℕ} [NeZero M]
  (F : HeckeRing.GL2.Newform M 2) (hχ : F.χ = 1) (p : ℕ) (hp : Nat.Prime p) (hpM : p ∣ M) :
  (HeckeRing.GL2.heckeUCuspNat 2 p hp hpM) F.toCuspForm = F.toCuspForm ∨
    (HeckeRing.GL2.heckeUCuspNat 2 p hp hpM) F.toCuspForm = -F.toCuspForm ∨
      (HeckeRing.GL2.heckeUCuspNat 2 p hp hpM) F.toCuspForm = 0
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.newform_bad_operator_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## elliptic_bad_prime_values

Source: `PrintedInputs.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.elliptic_bad_prime_values (E : WeierstrassCurve ℚ) (p : ℕ) (hp : Nat.Prime p)
  (hbad :
    ¬ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.GoodReductionAt E
        (ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary.primeIdealQ p hp)) :
  E.LFunction p = 1 ∨ E.LFunction p = -1 ∨ E.LFunction p = 0
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.elliptic_bad_prime_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## newform_unique_of_almost_all_prime_coeff

Source: `PrintedInputs.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.newform_unique_of_almost_all_prime_coeff
  (hLi : ZInQ.Contrib.RC53Assist.NewformGlueG0.Li1975StrongMultiplicityOneWeightTwo) (E : WeierstrassCurve ℚ) {M N : ℕ}
  [NeZero M] [NeZero N] (F : HeckeRing.GL2.Newform M 2) (G : HeckeRing.GL2.Newform N 2) (hFχ : F.χ = 1) (hGχ : G.χ = 1)
  (S T : Finset ℕ)
  (hF :
    ∀ (p : ℕ),
      Nat.Prime p → p ∉ S → (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑F.toCuspForm) = ↑(E.LFunction p))
  (hG :
    ∀ (p : ℕ),
      Nat.Prime p → p ∉ T → (PowerSeries.coeff p) (UpperHalfPlane.qExpansion 1 ⇑G.toCuspForm) = ↑(E.LFunction p)) :
  M = N ∧ ∀ (τ : UpperHalfPlane), F.toCuspForm τ = G.toCuspForm τ
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.newform_unique_of_almost_all_prime_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## localFactors_from_frobenius_without_BN_input

Source: `Scratch/StatementsAxioms.lean`

```lean
ZInQ.Contrib.RC53Assist.NewformGlueG0.localFactors_from_frobenius_without_BN_input (K V W ι κ : Type) [Field K]
  [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] (bV : Module.Basis ι K V) (bW : Module.Basis κ K W) (ρ : Representation K GlueC10.GQ V)
  (σ : Representation K GlueC10.GQ W) (hρc : Continuous fun g => (LinearMap.toMatrix bV bV) (ρ g))
  (hσc : Continuous fun g => (LinearMap.toMatrix bW bW) (σ g))
  (hρ : IsSemisimpleModule (MonoidAlgebra K GlueC10.GQ) ρ.asModule)
  (hσ : IsSemisimpleModule (MonoidAlgebra K GlueC10.GQ) σ.asModule) (S : Finset ℕ)
  (htr :
    ∀ (g : GlueC10.GQ) (p : ℕ),
      Nat.Prime p → p ∉ S → GlueC10.IsFrobAt g p → (LinearMap.trace K V) (ρ g) = (LinearMap.trace K W) (σ g))
  (I : Subgroup GlueC10.GQ) (g : GlueC10.GQ) (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I) :
  ZInQ.Contrib.RC53Assist.NewformGlueG0.inertiaEulerPolynomial ρ I g hg =
    ZInQ.Contrib.RC53Assist.NewformGlueG0.inertiaEulerPolynomial σ I g hg
```

```text
'ZInQ.Contrib.RC53Assist.NewformGlueG0.localFactors_from_frobenius_without_BN_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
