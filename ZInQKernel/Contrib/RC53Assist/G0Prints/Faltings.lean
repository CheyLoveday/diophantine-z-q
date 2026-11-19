import ZInQKernel.Contrib.RC53Assist.GlobalTrace.GoodReductionReading
import ZInQKernel.Contrib.RC53Assist.GlobalTrace.CoinvariantReadings

/-!
# Faltings's printed local-factor implication

The implication iii) ⇒ iv) of Korollar 2 is kept in the language of local
L-factors. The factors are reciprocals of the Frobenius polynomials on the
inertia coinvariants of the actual rational Tate module. No equality of
minimal Weierstrass polynomials occurs in the printed proposition.

The translation to minimal Weierstrass polynomials is proved separately.
Good reduction uses the proved trace and determinant dictionary. Bad reduction
uses only the three previously named hypotheses about Tate curves, local
and global decomposition groups, and additive coinvariants.

Locators: Faltings, Invent. Math. 73 (1983), §5, pp. 360–361, Korollar 2;
bibliography key `faltings1983`, TeX lines 11084–11086.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.G0Prints

open NumberField IsDedekindDomain Filter
open ZInQ.Contrib.RC53Assist.NewformGlueG0
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open ZInQ.Contrib.RC53Assist.GlobalTrace

/-- **DEFINITION**, the finite places of the rational number field.
Locator: Faltings 1983, p. 361, the index `v` of the Euler product. -/
abbrev RationalPlace := HeightOneSpectrum (RingOfIntegers ℚ)

/-- **DEFINITION**, `P_v(T)`, on the actual rational Tate module, with arithmetic
Frobenius on inertia coinvariants. Equivalently this is geometric Frobenius on
inertia invariants of the dual, as proved by `localTatePolynomialCoinv_eq_dual`.
Locators: Faltings 1983, p. 361; Carayol 1986, §§0.4–0.8, pp. 409–411. -/
def faltingsPv (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] {p : ℕ} (D : LocalArithmeticFrobenius p) :
    Polynomial ℚ_[ℓ] :=
  localTatePolynomialCoinv E ℓ D

/-- **DEFINITION**, the literal rational local factor `L_v = 1 / P_v(T)`.
The variable `T` stands for `(N_v)^{-s}`; equality is equality of rational
functions, not an evaluation at a single value of `s`.
Locator: Faltings 1983, p. 361, the displayed definition of `L(A,s)`. -/
def faltingsLv (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] {p : ℕ} (D : LocalArithmeticFrobenius p) :
    RatFunc ℚ_[ℓ] :=
  (algebraMap (Polynomial ℚ_[ℓ]) (RatFunc ℚ_[ℓ]) (faltingsPv E ℓ D))⁻¹

/-- **PROVED**, taking a reciprocal in the rational-function field loses no
information about the polynomial. Locator: inversion in a field and the
injective embedding of a polynomial ring into its fraction field. -/
theorem faltingsLv_eq_iff (E A : WeierstrassCurve ℚ)
    [E.IsElliptic] [A.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]
    {p : ℕ} (D : LocalArithmeticFrobenius p) :
    faltingsLv E ℓ D = faltingsLv A ℓ D ↔ faltingsPv E ℓ D = faltingsPv A ℓ D := by
  constructor
  · intro h
    exact (IsFractionRing.injective (Polynomial ℚ_[ℓ]) (RatFunc ℚ_[ℓ]))
      (inv_injective h)
  · intro h
    unfold faltingsLv
    rw [h]

/-- **PROVED**, the place with prime norm `p` is the ideal `(p)`.
Locator: the proved rational prime-ideal norm dictionary. -/
theorem rationalPlace_eq_primeIdealQ (v : RationalPlace) :
    primeIdealQ v.asIdeal.absNorm (prime_absNorm_rational v) = v :=
  absNorm_rational_injective (primeIdealQ_absNorm _ _)

/-- **PROVED READING**, the Tate polynomial at a finite place equals the
integer minimal-reduction polynomial after coefficient extension. At good
places the trace and determinant dictionary is proved; at bad places the
corrected named reading is the only parameter.
Locators: Silverman V.2.3 and VII.7; Appendix C, §§14 and 16. -/
theorem faltingsPv_eq_localPolynomial (hB : BadReductionTatePolynomialReadingCoinv)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]
    (v : RationalPlace) (hvℓ : v.asIdeal.absNorm ≠ ℓ)
    (D : LocalArithmeticFrobenius v.asIdeal.absNorm) :
    faltingsPv E ℓ D = (localPolynomialQ E v).map (Int.castRingHom ℚ_[ℓ]) := by
  unfold faltingsPv
  have hp := prime_absNorm_rational v
  have hv := rationalPlace_eq_primeIdealQ v
  by_cases hgood : GoodReductionAt E (primeIdealQ v.asIdeal.absNorm hp)
  · have h := localTatePolynomialCoinv_of_good globalGoodReductionTraceReading_proved
      E ℓ v.asIdeal.absNorm hp hvℓ hgood D
    simpa only [hv] using h
  · have h := hB E ℓ v.asIdeal.absNorm hp hvℓ hgood D
    simpa only [hv] using h

/-- **PRINT**, Faltings 1983, §5, Korollar 2, p. 361: iii) ⇒ iv), specialized
only to elliptic curves over `ℚ` and to finite places of residual characteristic
other than the chosen auxiliary prime. The local factors are the displayed
Tate-module rational functions `1/P_v(T)`, not minimal-model polynomials.
Changing the auxiliary prime recovers every finite place in the theorem below.
Bibliography key `faltings1983`, TeX lines 11084–11086.

Verbatim printed text, p. 360 (the setting of §5):

§5. Endomorphismen
Sei K Zahlkörper, A/K eine abelsche Varietät der Dimension g, l eine Prim-
zahl, T_l = T_l(A) der Tate-Modul, auf dem π = Gal(K̄/K) operiert.

Verbatim printed text, p. 361 (the setting and Korollar 2):

Korollar 1. Seien A₁ und A₂ abelsche Varietäten über K. Dann ist
Hom_K(A₁, A₂) ⊗_ℤ ℤ_l → Hom_π(T_l(A₁), T_l(A₂))
ein Isomorphismus.

Die L-Reihe eines A's ist bekanntlich definiert als
L(A,s) = ∏_v 1 / det(1 − (N_v)^{−s} · F_v | T_l(A)) = ∏_v L_v(A,s),
wobei das Produkt über fast alle Stellen von K zu erstrecken ist. Die lokalen
L-Faktoren L_v(A,s) sind unabhängig von l.

Korollar 2. Seien A₁, A₂ wie im Korollar 1. Es sind äquivalent
 i) A₁ und A₂ sind isogen.
 ii) T_l(A₁) ⊗_{ℤ_l} ℚ_l ≅ T_l(A₂) ⊗_{ℤ_l} ℚ_l als π-Modul.
 iii) L_v(s,A₁) = L_v(s,A₂) für fast alle Stellen v von K.
 iv) L_v(s,A₁) = L_v(s,A₂) für alle v.

The mathematics is transcribed with Unicode and subscripts; printed line
breaks other than the displayed hyphenation are immaterial. The proposition
keeps precisely iii) ⇒ iv); it does not postulate a Weierstrass reading. -/
def Faltings1983Korollar2iiiivPrint : Prop :=
  ∀ (E A : WeierstrassCurve ℚ) [E.IsElliptic] [A.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime],
    (∀ᶠ v : RationalPlace in cofinite, v.asIdeal.absNorm ≠ ℓ →
      ∀ D : LocalArithmeticFrobenius v.asIdeal.absNorm,
        faltingsLv E ℓ D = faltingsLv A ℓ D) →
    ∀ (v : RationalPlace), v.asIdeal.absNorm ≠ ℓ →
      ∀ D : LocalArithmeticFrobenius v.asIdeal.absNorm,
        faltingsLv E ℓ D = faltingsLv A ℓ D

/-- **PROVED FROM THE PRINT**, the exact existing Euler-factor rigidity
statement, with its original cofinite premise and every finite place in its
conclusion. Only the corrected bad-reduction reading is an additional input.
Locators: Faltings 1983, §5, Korollar 2, p. 361, iii) ⇒ iv);
`faltingsLv_eq_iff` and `faltingsPv_eq_localPolynomial`. -/
theorem Faltings1983EulerFactorRigidityQ_of_print_of_badReading
    (hB : BadReductionTatePolynomialReadingCoinv) :
    Faltings1983Korollar2iiiivPrint → Descent.Faltings1983EulerFactorRigidityQ := by
  intro hF E A hE hA hP v
  letI : E.IsElliptic := hE
  letI : A.IsElliptic := hA
  obtain ⟨ℓ, hℓ, hvℓ⟩ := exists_auxiliary_prime_ne v.asIdeal.absNorm
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  have hcof : ∀ᶠ w : RationalPlace in cofinite, w.asIdeal.absNorm ≠ ℓ →
      ∀ D : LocalArithmeticFrobenius w.asIdeal.absNorm,
        faltingsLv E ℓ D = faltingsLv A ℓ D := by
    filter_upwards [hP] with w hw
    intro hwℓ D
    apply (faltingsLv_eq_iff E A ℓ D).mpr
    rw [faltingsPv_eq_localPolynomial hB E ℓ w hwℓ D,
      faltingsPv_eq_localPolynomial hB A ℓ w hwℓ D, hw]
  obtain ⟨D⟩ := localArithmeticFrobenius_nonempty v.asIdeal.absNorm
    (prime_absNorm_rational v)
  have heq := (faltingsLv_eq_iff E A ℓ D).mp (hF E A ℓ hcof v hvℓ D)
  rw [faltingsPv_eq_localPolynomial hB E ℓ v hvℓ D,
    faltingsPv_eq_localPolynomial hB A ℓ v hvℓ D] at heq
  ext n
  have hn := congrArg (fun P : Polynomial ℚ_[ℓ] => P.coeff n) heq
  simp only [Polynomial.coeff_map, Int.coe_castRingHom] at hn
  exact_mod_cast hn

/-- **PROVED FROM THE PRINT AND THE THREE NAMED BAD-PRIME INPUTS**, the exact
unchanged rigidity field. No copy of the rigidity conclusion is assumed.
The named inputs are consumed through their already proved bad-prime assembly.
Locators: Faltings 1983, p. 361; Silverman, Appendix C, §§14 and 16. -/
theorem Faltings1983EulerFactorRigidityQ_of_print
    (hT : TateCurveTateModulePrint) (hLG : DecompositionGroupLocalGlobalGlue)
    (hA : AdditiveReductionCoinvariantsVanish) :
    Faltings1983Korollar2iiiivPrint → Descent.Faltings1983EulerFactorRigidityQ :=
  Faltings1983EulerFactorRigidityQ_of_print_of_badReading
    (badReductionTatePolynomialReadingCoinv_of_inputs hT hLG hA)

/-- **DEFINITION**, the nonsingular rational curve `y² = x³ − x`.
Locator: Silverman III.1, short Weierstrass equations. -/
def testCurve : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩

/-- **PROVED NON-VACUITY**, the discriminant is `64`, so this is an elliptic
curve, not a hypothetical empty object type. Locator: Silverman III.1. -/
instance testCurve_isElliptic : testCurve.IsElliptic := by
  constructor
  apply isUnit_iff_ne_zero.mpr
  norm_num [testCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- **PROVED NON-VACUITY**, the printed almost-all premise is inhabited by a
concrete elliptic curve compared with itself, for every auxiliary prime.
Locator: Faltings 1983, p. 361, iii). -/
theorem faltings_print_diagonal_premise (ℓ : ℕ) [Fact ℓ.Prime] :
    ∀ᶠ v : RationalPlace in cofinite, v.asIdeal.absNorm ≠ ℓ →
      ∀ D : LocalArithmeticFrobenius v.asIdeal.absNorm,
        faltingsLv testCurve ℓ D = faltingsLv testCurve ℓ D :=
  Filter.Eventually.of_forall (fun _ _ _ => rfl)

/-- **PROVED NON-VACUITY**, arithmetic Frobenius and the actual two-dimensional
Tate module both exist at the concrete pair of distinct primes `p = 3`, `ℓ = 2`.
Locator: Silverman III.7 and the arithmetic Frobenius construction. -/
theorem faltings_print_concrete_objects :
    Nonempty (LocalArithmeticFrobenius 3) ∧
      Nonempty (rationalTate testCurve 2) := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact ⟨localArithmeticFrobenius_nonempty 3 (by decide), ⟨0⟩⟩

end ZInQ.Contrib.RC53Assist.G0Prints
