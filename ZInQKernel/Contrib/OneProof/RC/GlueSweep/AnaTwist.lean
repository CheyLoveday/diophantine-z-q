import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Dictionary
import ZInQKernel.Contrib.OneProof.RC.Even.EvenSource

/-!
# Lane RC22 (glue sweep): `a_q(E^{(h)}) = χ_h(q) a_q(E)` at a prime not dividing `h`

Lane RC11's `unusedFactor_central` (tex 1876–1877, 7012–7015, 7202–7203) computes the unused-prime
factor (3.1)/(K9) at the centre, `E_q(χ)(0) = (q + 1 − χ(q) a_q)/q`, and reads its numerator as
`|E^h(𝔽_q)|` "because `a_q(E^h) = χ_h(q) a_q(E)` (GLUE)". The GLUE is a docstring reading (no Lean
hypothesis carries it); lane RC18's local computation (`localPolynomial_qtwist_of_not_dvd`) proves
it for every elliptic curve over `ℚ` and every prime `q ∤ h` (with `h ≡ 1 (mod 4)` if `q = 2`),
with no modularity and no fundamental-discriminant hypothesis:

* `LFunction_qtwist_prime_pow_of_not_dvd` (PROVED): `a_{q^k}(E^{(h)}) = χ_h(q)^k a_{q^k}(E)`, with
  `χ_h(q) = (h/q)` the Kronecker symbol;
* `LFunction_qtwist_prime_of_not_dvd_of_ne_two` (PROVED): at an odd prime `q ∤ h`,
  `a_q(E^{(h)}) = (h/q) a_q(E)` with the Legendre symbol;
* `unused_numerator_eq_card` (PROVED): for the curves `E_ℓ` of the manuscript and an odd prime
  `q ∤ 6hℓ`, the numerator `q + 1 − (h/q) a_q(E_ℓ)` of lane RC11's `unusedFactor_central` is the
  number of points of the reduction of `E^{(h)}_ℓ = E_{hℓ}` modulo `q` (lane RC3's
  `LFunction_curve_apply_prime`), which is the reading of tex 1876–1877.

All results here are `PROVED`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Ana

open WeierstrassCurve IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum
  ZInQ.Literature ZInQ.Manuscript.RC.PrintsAnalytic

/-- **The twist dictionary at an unramified prime power** (PROVED, from lane RC18's
`localPolynomial_qtwist_of_not_dvd`): for an elliptic curve `E/ℚ`, an integer `h` and a prime
`q ∤ h` (with `h ≡ 1 (mod 4)` if `q = 2`), the Dirichlet coefficients of Mathlib's `L`-functions
satisfy `a_{q^k}(E^{(h)}) = χ_h(q)^k a_{q^k}(E)` (`χ_h(q) = kronecker h q`; tex 1876–1877). -/
theorem LFunction_qtwist_prime_pow_of_not_dvd (E : WeierstrassCurve ℚ) [E.IsElliptic] {h : ℤ}
    {q : ℕ} (hq : q.Prime) (hqh : ¬ (q : ℤ) ∣ h) (h4 : q = 2 → h % 4 = 1) (k : ℕ) :
    (ZInQ.Contrib.CloudB3RC53.qtwist E h).LFunction (q ^ k) =
      kronecker h q ^ k * E.LFunction (q ^ k) := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨v, rfl⟩ := exists_natGenerator_eq q
  rw [TwistDictionary.LFunction_prime_pow, TwistDictionary.LFunction_prime_pow,
    TwistDictionary.localPolynomial_qtwist_of_not_dvd v E hqh h4,
    TwistDictionary.coeff_invOfUnit_comp_C_mul_X _ (TwistDictionary.localPolynomial_coeff_zero _)]

/-- **`a_q(E^{(h)}) = (h/q) a_q(E)` at an odd prime `q ∤ h`** (PROVED; the reading of tex
1876–1877 behind lane RC11's `unusedFactor_central`), with the Legendre symbol `(h/q)`. -/
theorem LFunction_qtwist_prime_of_not_dvd_of_ne_two (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {h : ℤ} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqh : ¬ (q : ℤ) ∣ h) :
    (ZInQ.Contrib.CloudB3RC53.qtwist E h).LFunction q = jacobiSym h q * E.LFunction q := by
  have h1 := LFunction_qtwist_prime_pow_of_not_dvd E hq hqh (fun h2 => absurd h2 hq2) 1
  simp only [pow_one] at h1
  rw [TwistDictionary.kronecker_prime_of_ne_two hq hq2] at h1
  exact h1

/-- **The numerator of the unused-prime factor is a point count** (PROVED; tex 1876–1877, 7202–7203:
"`E_q(χ)(0) = 1 − a_q χ(q)/q + 1/q`, which is `|E^h(𝔽_q)|/q`"). For the curve
`E_ℓ : y² = x(x − ℓ)(x + 3ℓ)`, an integer `h` and an odd prime `q ∤ 6hℓ`, with `a = a_q(E_ℓ)` and
`χ = (h/q)` the numerator `q + 1 − χ a` of lane RC11's `unusedFactor_central` equals
`#Ẽ_{hℓ}(𝔽_q)`, the number of points (with the point at infinity) of the reduction modulo `q` of
the twist `E^{(h)}_ℓ = E_{hℓ}`. -/
theorem unused_numerator_eq_card {ℓ h : ℤ} {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (hq : ¬ (q : ℤ) ∣ 6 * (h * ℓ)) :
    (q : ℤ) + 1 - jacobiSym h q * (ZInQ.Manuscript.curve (ℓ : ℚ)).LFunction q =
      Nat.card (ZInQ.Manuscript.PoleRC.curveF (((h * ℓ : ℤ) : ℤ) : ZMod q)).toAffine.Point := by
  have hqp : q.Prime := Fact.out
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by
    rintro h0
    have : ℓ = 0 := by exact_mod_cast h0
    exact hq (by rw [this, mul_zero, mul_zero]; exact dvd_zero _)
  have hE : (ZInQ.Manuscript.curve (ℓ : ℚ)).IsElliptic :=
    ZInQ.Manuscript.PoleRC.curve_isElliptic hℓ0
  have hqh : ¬ (q : ℤ) ∣ h := fun hd => hq (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hd _) _)
  have htw := LFunction_qtwist_prime_of_not_dvd_of_ne_two (ZInQ.Manuscript.curve (ℓ : ℚ)) hqp
    hq2 hqh
  rw [PrintsAnalytic.qtwist_curve, show ((h : ℚ) * (ℓ : ℚ)) = ((h * ℓ : ℤ) : ℚ) by push_cast; ring,
    KSplit.LFunction_curve_apply_prime (h * ℓ) q hq] at htw
  rw [← htw]
  ring

end ZInQ.Manuscript.RC.GlueSweep.Ana
