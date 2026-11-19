import ZInQKernel.Contrib.RC53Assist.G0Prints.Faltings

/-!
# The elliptic L-function defined by its actual cohomological Tate factors

The source L-function is built from arithmetic Frobenius on inertia
coinvariants of the genuine homological Tate module, equivalently geometric
Frobenius on invariants of its dual. It does not use minimal-model
polynomials by definition. Integer descent of each actual Tate polynomial
uses its unique polynomial preimage if one exists; that it exists at every
finite place is proved by the good and corrected bad dictionaries.

The dictionary to the minimal-model Euler product is proved term by term.
Thus an analytic equality involving this source L-function does not assume
the local-factor reading hidden in the existing Weierstrass L-function.

Locators: Faltings 1983, p. 361; Carayol 1986, §§0.4–0.8, pp. 409–411;
Silverman V.2.3, VII.7, Appendix C §§14 and 16.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.G0Prints

open NumberField IsDedekindDomain Polynomial
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
open ZInQ.Contrib.RC53Assist.GlobalTrace

/-- **DEFINITION**, an auxiliary prime different from the norm of the finite
place. Its primality and inequality are proved, not part of a print.
Locator: the condition `p ≠ ℓ` of Carayol's local compatibility. -/
def sourceAuxiliaryPrime (v : RationalPlace) : ℕ :=
  (exists_auxiliary_prime_ne v.asIdeal.absNorm).choose

/-- **PROVED PROPERTY**, the auxiliary integer is prime. -/
instance sourceAuxiliaryPrime_prime (v : RationalPlace) :
    Fact (sourceAuxiliaryPrime v).Prime :=
  ⟨(exists_auxiliary_prime_ne v.asIdeal.absNorm).choose_spec.1⟩

/-- **PROVED PROPERTY**, the excluded residual characteristic is avoided.
Locator: Carayol 1986, Théorème (A), pp. 410–411. -/
theorem sourceAuxiliaryPrime_ne (v : RationalPlace) :
    v.asIdeal.absNorm ≠ sourceAuxiliaryPrime v :=
  (exists_auxiliary_prime_ne v.asIdeal.absNorm).choose_spec.2

/-- **DEFINITION WITH PROVED EXISTENCE**, a genuine local arithmetic Frobenius
at the finite place. Its underlying valuation, inertia and residue action
are the existing arithmetic objects, not supplied independently.
Locator: Frobenius of the finite residue field. -/
def sourceFrobenius (v : RationalPlace) : LocalArithmeticFrobenius v.asIdeal.absNorm :=
  Classical.choice (localArithmeticFrobenius_nonempty _ (prime_absNorm_rational v))

/-- **DEFINITION**, the actual cohomological local Tate polynomial, in the
auxiliary completion. It is the polynomial of geometric Frobenius on
inertia invariants of the dual of the genuine rational Tate module.
The equivalent coinvariant definition avoids the false multiplicative-prime
invariant reading of the homological representation.
Locators: Carayol §§0.4–0.8, pp. 409–411; Faltings p. 361. -/
def sourceTatePolynomial (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (v : RationalPlace) : Polynomial ℚ_[sourceAuxiliaryPrime v] :=
  faltingsPv E (sourceAuxiliaryPrime v) (sourceFrobenius v)

/-- **DEFINITION**, integer descent of the actual Tate polynomial. The
polynomial preimage is unique because the integer coefficient map is
injective. The unused fallback is `1`; the existence of the preimage at
every place is proved from the corrected local dictionaries below.
This is not defined to be a minimal-reduction polynomial.
Locators: rationality of elliptic cohomological local factors; Carayol p. 411. -/
def sourceEulerPolynomial (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (v : RationalPlace) : Polynomial ℤ := by
  classical
  exact if h : ∃ P : Polynomial ℤ,
      P.map (Int.castRingHom ℚ_[sourceAuxiliaryPrime v]) = sourceTatePolynomial E v then
    h.choose else 1

/-- **PROVED LOCAL DICTIONARY**, the integer preimage exists and is precisely
the minimal-reduction polynomial. Good reduction uses the proved trace and
determinant; bad reduction uses only the corrected named reading.
Locators: Silverman V.2.3, VII.7, Appendix C §§14 and 16. -/
theorem sourceEulerPolynomial_eq_localPolynomial
    (hB : BadReductionTatePolynomialReadingCoinv)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (v : RationalPlace) :
    sourceEulerPolynomial E v = localPolynomialQ E v := by
  classical
  have heq : sourceTatePolynomial E v =
      (localPolynomialQ E v).map (Int.castRingHom ℚ_[sourceAuxiliaryPrime v]) :=
    faltingsPv_eq_localPolynomial hB E _ v (sourceAuxiliaryPrime_ne v) (sourceFrobenius v)
  have hex : ∃ P : Polynomial ℤ,
      P.map (Int.castRingHom ℚ_[sourceAuxiliaryPrime v]) = sourceTatePolynomial E v :=
    ⟨localPolynomialQ E v, heq.symm⟩
  have hmap : (sourceEulerPolynomial E v).map (Int.castRingHom ℚ_[sourceAuxiliaryPrime v]) =
      (localPolynomialQ E v).map (Int.castRingHom ℚ_[sourceAuxiliaryPrime v]) := by
    unfold sourceEulerPolynomial
    rw [dif_pos hex]
    exact hex.choose_spec.trans heq
  ext n
  have hn := congrArg (fun P : Polynomial ℚ_[sourceAuxiliaryPrime v] => P.coeff n) hmap
  simp only [Polynomial.coeff_map, Int.coe_castRingHom] at hn
  exact_mod_cast hn

/-- **DEFINITION**, the formal Dirichlet coefficients of the genuine
cohomological Tate Euler product. Every local factor is the reciprocal of
the integer descent of the actual Tate polynomial, at the actual place norm.
Locators: Faltings p. 361, `L(A,s)`; Carayol §0.8, p. 411. -/
def sourceLFunction (E : WeierstrassCurve ℚ) [E.IsElliptic] : ArithmeticFunction ℤ :=
  ArithmeticFunction.eulerProduct (fun v : RationalPlace =>
    ArithmeticFunction.ofPowerSeries v.asIdeal.absNorm
      (PowerSeries.invOfUnit (sourceEulerPolynomial E v : PowerSeries ℤ) 1))

/-- **DEFINITION**, the analytic L-function with precisely those genuine
cohomological Tate factors. It is not the minimal-model L-function by
fiat; their equality is the theorem below.
Locators: Carayol 1986, §0.8, p. 411; Faltings 1983, p. 361. -/
def sourceLSeries (E : WeierstrassCurve ℚ) [E.IsElliptic] (s : ℂ) : ℂ :=
  LSeries (fun n : ℕ => (sourceLFunction E n : ℂ)) s

/-- **PROVED GLOBAL DICTIONARY**, the actual cohomological Tate Euler product
is the existing minimal-model Euler product, because their local factors
are equal at each finite place. No newform or analytic equality is used.
Locators: the proved local dictionaries and the Euler-product definition. -/
theorem sourceLFunction_eq_LFunction (hB : BadReductionTatePolynomialReadingCoinv)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] : sourceLFunction E = E.LFunction := by
  unfold sourceLFunction WeierstrassCurve.LFunction
  apply congrArg ArithmeticFunction.eulerProduct
  funext v
  rw [sourceEulerPolynomial_eq_localPolynomial hB E v]
  unfold WeierstrassCurve.localEulerFactor
  rw [card_residueField_completion]
  apply congrArg (ArithmeticFunction.ofPowerSeries v.asIdeal.absNorm)
  unfold WeierstrassCurve.localPowerSeries localPolynomialQ WeierstrassCurve.baseChange
  apply congrArg (fun P : Polynomial ℤ => PowerSeries.invOfUnit (P : PowerSeries ℤ) 1)
  apply congrArg (fun W : WeierstrassCurve (v.adicCompletion ℚ) =>
    W.localPolynomial (v.adicCompletionIntegers ℚ))
  apply congrArg (WeierstrassCurve.map E)
  exact Subsingleton.elim _ _

/-- **PROVED ANALYTIC DICTIONARY**, equality of the two analytic L-functions
follows from the already proved coefficientwise Tate-to-minimal Euler
product reading, not the other way around.
Locators: Faltings p. 361; Carayol p. 411. -/
theorem sourceLSeries_eq_LSeries (hB : BadReductionTatePolynomialReadingCoinv)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (s : ℂ) :
    sourceLSeries E s = E.LSeries s := by
  rw [sourceLSeries, sourceLFunction_eq_LFunction hB E]
  rfl

/-- **PROVED NORMALIZATION**, the fallback branch in integer descent is
never used when the corrected local dictionaries are supplied. The source
polynomial still acts on the actual Tate module.
Locators: the local good and corrected bad readings. -/
theorem sourceEulerPolynomial_maps_to_Tate (hB : BadReductionTatePolynomialReadingCoinv)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (v : RationalPlace) :
    (sourceEulerPolynomial E v).map (Int.castRingHom ℚ_[sourceAuxiliaryPrime v]) =
      sourceTatePolynomial E v := by
  rw [sourceEulerPolynomial_eq_localPolynomial hB E v]
  exact (faltingsPv_eq_localPolynomial hB E _ v (sourceAuxiliaryPrime_ne v)
    (sourceFrobenius v)).symm

end ZInQ.Contrib.RC53Assist.G0Prints
