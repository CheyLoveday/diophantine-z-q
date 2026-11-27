import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Newform
import ZInQKernel.Contrib.OneProof.RC.KSplit.Ap
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Coefficient

/-!
# Lane RC18-twist: a curve has good reduction at the primes not dividing the level of its newform

If `f : Newform N 2` is the newform of `E` (`IsNewformOf E f`: trivial nebentypus and
`a_n(f) = a_n(E)`), then at a prime `p ∤ N` the Hecke recurrence gives `a_{p²} = a_p² − p`
(Tau Ceti's `EigenformAwayFromLevel.qExpansion_coeff_prime_pow_add_two` at `r = 0`, with `a₁ = 1`,
`χ = 1`, `k = 2`). At a prime of bad reduction Mathlib's Euler factor is `1/(1 − εT)` with
`ε ∈ {1, −1, 0}`, so `a_{p²} = ε² = a_p²`. Hence `E` has good reduction at every `p ∤ N`.
-/

namespace ZInQ.Manuscript.RC.TwistDictionary

open WeierstrassCurve IsDedekindDomain HeightOneSpectrum Rat.HeightOneSpectrum
  ZInQ.Manuscript.RC.PrintsAnalytic HeckeRing.GL2

/-- **The coefficient of `T²` in `1 / P`** (PROVED), for an integer polynomial `P` with constant
term `1`: it is `c₁² − c₂`, where `P = 1 + c₁ T + c₂ T² + ⋯`. -/
theorem coeff_two_invOfUnit_eq_sq_sub (P : Polynomial ℤ) (hP : P.coeff 0 = 1) :
    PowerSeries.coeff 2 (PowerSeries.invOfUnit (P : PowerSeries ℤ) 1) =
      P.coeff 1 ^ 2 - P.coeff 2 := by
  have h0 : PowerSeries.constantCoeff (P : PowerSeries ℤ) = ((1 : ℤˣ) : ℤ) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hP]; rfl
  have h := congrArg (PowerSeries.coeff 2) (PowerSeries.mul_invOfUnit _ _ h0)
  have h1 := ZInQ.Literature.coeff_one_invOfUnit P hP
  have hc : PowerSeries.coeff 0 (PowerSeries.invOfUnit (P : PowerSeries ℤ) 1) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit]
    simp
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Polynomial.coeff_coe, hP, h1, hc,
    PowerSeries.coeff_one] at h
  norm_num at h
  linear_combination h

/-- **Good reduction away from the level of the newform** (PROVED): if `f : Newform N 2` is the
newform of `E` and `p = natGenerator v` does not divide `N`, the minimal model of `E` over `ℚ_v` has
good reduction. -/
theorem hasGoodReduction_of_isNewformOf {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N]
    {f : Newform N 2} (hf : IsNewformOf E f) (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hpN : ¬ natGenerator v ∣ N) :
    ((E.baseChange (v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ)).HasGoodReduction
      (v.adicCompletionIntegers ℚ) := by
  by_contra hbad
  have hp : (natGenerator v).Prime := prime_natGenerator v
  obtain ⟨P, hPdef⟩ : ∃ P, (E.baseChange (v.adicCompletion ℚ)).localPolynomial
      (v.adicCompletionIntegers ℚ) = P := ⟨_, rfl⟩
  -- At a bad place the local polynomial is `1 − T`, `1 + T` or `1`.
  have hP : P.coeff 0 = 1 ∧ P.coeff 2 = 0 := by
    rw [← hPdef]
    unfold WeierstrassCurve.localPolynomial
    simp only [hbad, ite_false]
    split_ifs <;> simp [Polynomial.coeff_one, Polynomial.coeff_X]
  -- The coefficients of `L(E, s)` at the powers of `p`; the two `ℚ`-algebra structures on `ℚ_v`
  -- met here agree, `Algebra ℚ _` being a subsingleton.
  have hL (k : ℕ) : E.LFunction (natGenerator v ^ k) =
      PowerSeries.coeff k (PowerSeries.invOfUnit (P : PowerSeries ℤ) 1) := by
    rw [← hPdef, ZInQ.Manuscript.RC.KSplit.LFunction_apply_prime_pow_eq E (natGenerator v) k v rfl]
    congr!
    exact Subsingleton.elim _ _
  have hE1 : E.LFunction (natGenerator v) = -P.coeff 1 := by
    rw [← pow_one (natGenerator v), hL 1, ZInQ.Literature.coeff_one_invOfUnit P hP.1]
  have hE2 : E.LFunction (natGenerator v ^ 2) = P.coeff 1 ^ 2 := by
    rw [hL 2, coeff_two_invOfUnit_eq_sq_sub P hP.1, hP.2, sub_zero]
  -- The Hecke recurrence at `p ∤ N`: `a_{p²}(f) = a_p(f)² − p`.
  have hcop : Nat.Coprime (natGenerator v) N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  have hrec := f.toEigenformAwayFromLevel.qExpansion_coeff_prime_pow_add_two f.isNorm
    (p := ⟨natGenerator v, hp.pos⟩) hp hcop 0
  have h1 := hf.2 (natGenerator v) hp.pos
  have h2 := hf.2 (natGenerator v ^ 2) (pow_pos hp.pos 2)
  simp only [nfCoeff, lcoeff, hE1, hE2] at h1 h2
  simp only [PNat.mk_coe, zero_add, pow_one, pow_zero, hf.1, MonoidHom.one_apply, Units.val_one,
    one_mul, f.isNorm, mul_one] at hrec
  rw [h1, h2] at hrec
  -- Hence `p = 0` in `ℂ`.
  have hp0 : ((natGenerator v : ℕ) : ℂ) = 0 := by
    norm_num at hrec
    linear_combination hrec
  exact hp.ne_zero (by exact_mod_cast hp0)

end ZInQ.Manuscript.RC.TwistDictionary
