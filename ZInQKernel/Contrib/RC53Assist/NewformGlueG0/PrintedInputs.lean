import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.NewformGlue
import ZInQKernel.Contrib.RC53Assist.NewformPeriodsDictionary.Dictionary

/-!
# The precise Li inputs and the bad-prime signs

Li, *Newforms and Functional Equations*, Math. Ann. 212 (1975), 285–315,
bibitem `li-newforms`, is read from the Göttingen article scan. Printed
p. 285 is PDF page 2; pp. 294, 295, 298 are PDF pages 11, 12, 15.
The two propositions below are special cases of actual printed statements,
not a newform-existence assertion for an elliptic curve.

* Theorem 3(i), p. 295: a normalized newform has eigenvalue `a_p` at the
  good Hecke operators and `a_q` at the bad operators. Its coefficients
  satisfy the good-prime quadratic recurrence and `a_{nq} = a_n a_q`
  at a bad prime. This full-eigenform part is already proved by the
  imported newform API.
* Theorem 3(iii), p. 295, for weight two and trivial character: at a prime
  `q` dividing the level, `a_q = 0` if `q²` divides the level, and
  `a_q² = 1` otherwise. The character factors through the level divided
  by `q`, as required by the print.
* Theorem 5, p. 298, for trivial character: normalized newforms at two
  levels with equal `a_p` at almost all primes are the same form and
  their levels are equal.

The sign alternatives `1`, `-1`, `0` for the existing elliptic-curve local
polynomials are also proved below directly from their minimal-reduction
definition. That the newform and the curve have the same sign at the
same prime still requires the representation and local-factor dictionaries
in Carayol 1986, Théorème (A), pp. 410–411 and §0.8, p. 411.
-/

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.NewformGlueG0

open UpperHalfPlane HeckeRing.GL2
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary

/-- **PRINT INPUT, SPECIAL CASE**, Li 1975, bibitem `li-newforms`,
Theorem 3(iii), p. 295, weight two and trivial character; page image checked.
This is a proposition, not an axiom or a proof of the printed theorem. -/
def Li1975BadPrimeWeightTwo : Prop :=
  ∀ (M : ℕ) [NeZero M] (F : Newform M 2), F.χ = 1 →
    ∀ (p : ℕ), p.Prime → p ∣ M →
      (p ^ 2 ∣ M → (qExpansion 1 F.toCuspForm).coeff p = 0) ∧
      (¬p ^ 2 ∣ M → (qExpansion 1 F.toCuspForm).coeff p ^ 2 = 1)

/-- **PRINT INPUT, SPECIAL CASE**, Li 1975, bibitem `li-newforms`,
Theorem 5, p. 298, weight two and trivial character; page image checked.
Only two genuine normalized newforms are compared, with no elliptic curve
and no hypothesis equivalent to G0. This is a proposition, not an axiom. -/
def Li1975StrongMultiplicityOneWeightTwo : Prop :=
  ∀ (M N : ℕ) [NeZero M] [NeZero N] (F : Newform M 2) (G : Newform N 2),
    F.χ = 1 → G.χ = 1 →
    (∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      (qExpansion 1 F.toCuspForm).coeff p = (qExpansion 1 G.toCuspForm).coeff p) →
      M = N ∧ ∀ τ : UpperHalfPlane, F.toCuspForm τ = G.toCuspForm τ

/-- **PROVED FROM THE PRINT INPUT**, Li 1975, Theorem 3(iii), p. 295.
Over the complex numbers the weight-two square relation gives exactly
`a_p = 1` or `a_p = -1` when the prime divides the level exactly once. -/
theorem newform_bad_prime_sign (hLi : Li1975BadPrimeWeightTwo)
    {M : ℕ} [NeZero M] (F : Newform M 2) (hχ : F.χ = 1)
    (p : ℕ) (hp : p.Prime) (hpM : p ∣ M) (hpsq : ¬p ^ 2 ∣ M) :
    (qExpansion 1 F.toCuspForm).coeff p = 1 ∨
      (qExpansion 1 F.toCuspForm).coeff p = -1 := by
  have h := (hLi M F hχ p hp hpM).2 hpsq
  have hprod : ((qExpansion 1 F.toCuspForm).coeff p - 1) *
      ((qExpansion 1 F.toCuspForm).coeff p + 1) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp hprod with hz | hz
  · exact Or.inl (sub_eq_zero.mp hz)
  · right
    linear_combination hz

/-- **PROVED FROM THE PRINT INPUT**, Li 1975, Theorem 3(iii), p. 295.
The zero and sign cases together give the three possible bad-prime
Fourier coefficients. -/
theorem newform_bad_prime_values (hLi : Li1975BadPrimeWeightTwo)
    {M : ℕ} [NeZero M] (F : Newform M 2) (hχ : F.χ = 1)
    (p : ℕ) (hp : p.Prime) (hpM : p ∣ M) :
    (qExpansion 1 F.toCuspForm).coeff p = 1 ∨
      (qExpansion 1 F.toCuspForm).coeff p = -1 ∨
      (qExpansion 1 F.toCuspForm).coeff p = 0 := by
  by_cases hpsq : p ^ 2 ∣ M
  · exact Or.inr (Or.inr ((hLi M F hχ p hp hpM).1 hpsq))
  · rcases newform_bad_prime_sign hLi F hχ p hp hpM hpsq with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- **PROVED FROM THE PRINT INPUT AND THE HECKE API**, Li 1975,
Theorem 3(i), (iii), p. 295; locator: `Newform.heckeUCuspNat_eq_qExpansion_coeff_smul`.
The actual bad-prime operator acts by `1`, `-1`, or `0`, not merely an
unspecified eigenvalue. -/
theorem newform_bad_operator_values (hLi : Li1975BadPrimeWeightTwo)
    {M : ℕ} [NeZero M] (F : Newform M 2) (hχ : F.χ = 1)
    (p : ℕ) (hp : p.Prime) (hpM : p ∣ M) :
    heckeUCuspNat 2 p hp hpM F.toCuspForm = F.toCuspForm ∨
      heckeUCuspNat 2 p hp hpM F.toCuspForm = -F.toCuspForm ∨
      heckeUCuspNat 2 p hp hpM F.toCuspForm = 0 := by
  rw [F.heckeUCuspNat_eq_qExpansion_coeff_smul hp hpM]
  rcases newform_bad_prime_values hLi F hχ p hp hpM with h | h | h
  · left
    simp [h]
  · right
    left
    simp [h]
  · right
    right
    simp [h]

/-- **PROVED**, directly from the existing minimal-reduction polynomial;
locators: Mathlib `WeierstrassCurve.localPolynomial` and
`NewformPeriodsDictionary.lFunction_prime_eq_neg_localPolynomial_coeff`.
The curve's bad-prime coefficient is `1`, `-1`, or `0`, independently of
any modularity or comparison hypothesis. -/
theorem elliptic_bad_prime_values (E : WeierstrassCurve ℚ) (p : ℕ) (hp : p.Prime)
    (hbad : ¬GoodReductionAt E (primeIdealQ p hp)) :
    E.LFunction p = 1 ∨ E.LFunction p = -1 ∨ E.LFunction p = 0 := by
  classical
  have h := lFunction_prime_eq_neg_localPolynomial_coeff E p hp
  unfold localPolynomialQ WeierstrassCurve.localPolynomial at h
  split_ifs at h with hgood hsplit hmult
  · exact (hbad hgood).elim
  · left
    simpa [Polynomial.coeff_one] using h
  · right
    left
    simpa [Polynomial.coeff_one] using h
  · right
    right
    simpa [Polynomial.coeff_one] using h

/-- **PROVED FROM THE PRINT INPUT**, Li 1975, Theorem 5, p. 298.
Two candidate newforms whose prime coefficients agree with those of the
same elliptic curve outside possibly different finite sets have the same
level and the same underlying function. No candidate's existence is assumed
as a substitute for the existence conclusion of G0. -/
theorem newform_unique_of_almost_all_prime_coeff (hLi : Li1975StrongMultiplicityOneWeightTwo)
    (E : WeierstrassCurve ℚ) {M N : ℕ} [NeZero M] [NeZero N]
    (F : Newform M 2) (G : Newform N 2) (hFχ : F.χ = 1) (hGχ : G.χ = 1)
    (S T : Finset ℕ)
    (hF : ∀ p : ℕ, p.Prime → p ∉ S →
      (qExpansion 1 F.toCuspForm).coeff p = (E.LFunction p : ℂ))
    (hG : ∀ p : ℕ, p.Prime → p ∉ T →
      (qExpansion 1 G.toCuspForm).coeff p = (E.LFunction p : ℂ)) :
    M = N ∧ ∀ τ : UpperHalfPlane, F.toCuspForm τ = G.toCuspForm τ := by
  apply hLi M N F G hFχ hGχ
  refine ⟨S ∪ T, fun p hp hnot => ?_⟩
  have hpS : p ∉ S := fun h => hnot (Finset.mem_union_left _ h)
  have hpT : p ∉ T := fun h => hnot (Finset.mem_union_right _ h)
  exact (hF p hp hpS).trans (hG p hp hpT).symm

end ZInQ.Contrib.RC53Assist.NewformGlueG0
