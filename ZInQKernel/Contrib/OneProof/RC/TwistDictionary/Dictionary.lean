import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Unramified
import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Ramified
import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Hecke
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Bridges

/-!
# Lane RC18-twist: the twist dictionary `a_n(E^{(D)}) = χ_D(n) a_n(E)`

This file proves lane RC8's `ZInQ.Manuscript.RC.PrintsAnalytic.TwistDictionary` (stated there as a
GLUE): if `f : Newform N 2` is the newform of the elliptic curve `E/ℚ` and `D` is a fundamental
discriminant prime to `N`, then the Dirichlet coefficients of Mathlib's `L(E^{(D)}, s)` (with the
shared blueprint's twist `qtwist`) are `χ_D(n) a_n(E)`, `χ_D(n) = kronecker D n`.

Proof, prime by prime (Mathlib's `L(W, s)` is the Euler product of the local factors
`1 / localPolynomial`, `LFunction_prime_pow`):
* `p ∤ D`: the local polynomial of `E^{(D)}` at `p` is that of `E` at `χ_D(p) T`
  (`localPolynomial_qtwist_of_not_dvd`: good, multiplicative and additive reduction), so the
  coefficient at `p^k` is multiplied by `χ_D(p)^k` (`coeff_invOfUnit_comp_C_mul_X`);
* `p ∣ D`: then `p ∤ N`, so `E` has good reduction at `p` (`hasGoodReduction_of_isNewformOf`, from
  the Hecke recurrence of `f`), and the ramified twist has additive reduction
  (`localPolynomial_qtwist_of_dvd`): the coefficient at `p^k`, `k ≥ 1`, is `0 = χ_D(p)^k a_{p^k}`.
Both sides are multiplicative in `n` (`isMultiplicative_kroneckerFun`).

All results here are `PROVED`.
-/

namespace ZInQ.Manuscript.RC.TwistDictionary

open WeierstrassCurve IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum
  ZInQ.Literature Polynomial ZInQ.Manuscript.RC.PrintsAnalytic HeckeRing.GL2 ArithmeticFunction

/-! ### Power series -/

/-- Replacing `T` by `χ T` in the local polynomial multiplies the `k`-th coefficient of its
inverse by `χ^k`. -/
theorem coeff_invOfUnit_comp_C_mul_X (P : ℤ[X]) (hP : P.coeff 0 = 1) (χ : ℤ) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.invOfUnit ((P.comp (C χ * X) : ℤ[X]) : PowerSeries ℤ) 1) =
      χ ^ k * PowerSeries.coeff k (PowerSeries.invOfUnit (P : PowerSeries ℤ) 1) := by
  have hcomp : ((P.comp (C χ * X) : ℤ[X]) : PowerSeries ℤ) =
      PowerSeries.rescale χ (P : PowerSeries ℤ) := by
    ext n
    rw [Polynomial.coeff_coe, PowerSeries.coeff_rescale, Polynomial.coeff_coe, comp_C_mul_X_coeff,
      mul_comm]
  have h0 : PowerSeries.constantCoeff (P : PowerSeries ℤ) = ((1 : ℤˣ) : ℤ) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hP]; rfl
  have h0' : PowerSeries.constantCoeff (PowerSeries.rescale χ (P : PowerSeries ℤ)) =
      ((1 : ℤˣ) : ℤ) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero,
      one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
  have hinv : PowerSeries.invOfUnit (PowerSeries.rescale χ (P : PowerSeries ℤ)) 1 =
      PowerSeries.rescale χ (PowerSeries.invOfUnit (P : PowerSeries ℤ) 1) := by
    have h1 := PowerSeries.mul_invOfUnit _ _ h0'
    have h2 : PowerSeries.rescale χ (P : PowerSeries ℤ) *
        PowerSeries.rescale χ (PowerSeries.invOfUnit (P : PowerSeries ℤ) 1) = 1 := by
      rw [← map_mul, PowerSeries.mul_invOfUnit _ _ h0, map_one]
    calc PowerSeries.invOfUnit (PowerSeries.rescale χ (P : PowerSeries ℤ)) 1
        = PowerSeries.invOfUnit (PowerSeries.rescale χ (P : PowerSeries ℤ)) 1 *
            (PowerSeries.rescale χ (P : PowerSeries ℤ) *
              PowerSeries.rescale χ (PowerSeries.invOfUnit (P : PowerSeries ℤ) 1)) := by
          rw [h2, mul_one]
      _ = PowerSeries.rescale χ (PowerSeries.invOfUnit (P : PowerSeries ℤ) 1) := by
          rw [← mul_assoc, mul_comm (PowerSeries.invOfUnit _ _), h1, one_mul]
  rw [hcomp, hinv, PowerSeries.coeff_rescale]

/-- The inverse of the local polynomial `1`. -/
theorem coeff_invOfUnit_one (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.invOfUnit ((1 : ℤ[X]) : PowerSeries ℤ) 1) =
      if k = 0 then 1 else 0 := by
  have h1 : ((1 : ℤ[X]) : PowerSeries ℤ) = 1 := Polynomial.coe_one
  rw [h1]
  have h0 : PowerSeries.constantCoeff (1 : PowerSeries ℤ) = ((1 : ℤˣ) : ℤ) := by simp
  have h := PowerSeries.mul_invOfUnit (1 : PowerSeries ℤ) 1 h0
  rw [one_mul] at h
  rw [h, PowerSeries.coeff_one]

/-- The constant coefficient of Mathlib's local polynomial is `1`. -/
theorem localPolynomial_coeff_zero {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) : (W.localPolynomial R).coeff 0 = 1 := by
  unfold localPolynomial
  split_ifs <;> simp

/-! ### The coefficients at prime powers -/

/-- **The coefficient of `L(W, s)` at `p^k`** through the local polynomial at the place above `p`
(lane RC3's `LFunction_apply_prime_pow_eq`, restated with the `ℚ`-algebra structure on `ℚ_v` used in
this lane's statements: `Algebra ℚ ℚ_v` is a subsingleton). -/
theorem LFunction_prime_pow (W : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (k : ℕ) :
    W.LFunction (natGenerator v ^ k) = PowerSeries.coeff k (PowerSeries.invOfUnit
      ((W.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) :
        PowerSeries ℤ) 1) := by
  rw [ZInQ.Manuscript.RC.KSplit.LFunction_apply_prime_pow_eq W (natGenerator v) k v rfl]
  congr!
  exact Subsingleton.elim _ _

/-- A fundamental discriminant prime to `2` is `1 (mod 4)`. -/
theorem IsFundamentalDiscriminant.emod_four_of_odd {D : ℤ} (hD : IsFundamentalDiscriminant D)
    (h2 : ¬ (2 : ℤ) ∣ D) : D % 4 = 1 := by
  rcases hD with ⟨-, ⟨h, -⟩ | ⟨m, rfl, -, -⟩⟩
  · exact h
  · exact absurd ⟨2 * m, by ring⟩ h2

/-- **The twist dictionary at a prime power, for a curve with good reduction at the primes of `D`**
(PROVED): if `D` is a fundamental discriminant and `E` has good reduction at every prime dividing
`D`, then `a_{p^k}(E^{(D)}) = χ_D(p)^k a_{p^k}(E)` for every prime `p` and `k ≥ 0`. -/
theorem LFunction_qtwist_prime_pow_of_good {E : WeierstrassCurve ℚ} [E.IsElliptic] {D : ℤ}
    (hD : IsFundamentalDiscriminant D)
    (hgood : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ), (natGenerator v : ℤ) ∣ D →
      ((E.baseChange (v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ)).HasGoodReduction
        (v.adicCompletionIntegers ℚ))
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (ZInQ.Contrib.CloudB3RC53.qtwist E D).LFunction (p ^ k) =
      kronecker D p ^ k * E.LFunction (p ^ k) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨v, rfl⟩ := exists_natGenerator_eq p
  rw [LFunction_prime_pow, LFunction_prime_pow]
  by_cases hpD : (natGenerator v : ℤ) ∣ D
  · -- ramified: additive reduction of the twist
    rw [localPolynomial_qtwist_of_dvd v E hD hpD (hgood v hpD), coeff_invOfUnit_one,
      kronecker_eq_zero_of_dvd hp hpD]
    rcases k with _ | k
    · simp [← LFunction_prime_pow, (isMultiplicative_LFunction E).map_one]
    · simp
  · -- unramified
    have h4 : natGenerator v = 2 → D % 4 = 1 := fun h2 => by
      rw [h2] at hpD
      exact IsFundamentalDiscriminant.emod_four_of_odd hD (by exact_mod_cast hpD)
    rw [localPolynomial_qtwist_of_not_dvd v E hpD h4,
      coeff_invOfUnit_comp_C_mul_X _ (localPolynomial_coeff_zero _)]

/-- **The primes of `D` do not divide the level** (PROVED): if `D` is prime to `N` and
`p = natGenerator v` divides `D`, then `p ∤ N`. -/
theorem not_dvd_level_of_dvd {D : ℤ} {N : ℕ} (hDN : IsCoprime D (N : ℤ))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (hpD : (natGenerator v : ℤ) ∣ D) :
    ¬ natGenerator v ∣ N := by
  intro hN
  have hu := hDN.isUnit_of_dvd' hpD (Int.natCast_dvd_natCast.mpr hN)
  rw [Int.isUnit_iff] at hu
  have := (prime_natGenerator v).two_le
  omega

/-- **The twist dictionary at a prime power** (PROVED):
`a_{p^k}(E^{(D)}) = χ_D(p)^k a_{p^k}(E)` when `D` is a fundamental discriminant prime to the level
of the newform of `E`. -/
theorem LFunction_qtwist_prime_pow {E : WeierstrassCurve ℚ} [E.IsElliptic] {N : ℕ} [NeZero N]
    {f : Newform N 2} (hf : IsNewformOf E f) {D : ℤ} (hD : IsFundamentalDiscriminant D)
    (hDN : IsCoprime D (N : ℤ)) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (ZInQ.Contrib.CloudB3RC53.qtwist E D).LFunction (p ^ k) =
      kronecker D p ^ k * E.LFunction (p ^ k) :=
  LFunction_qtwist_prime_pow_of_good hD
    (fun v hpD => hasGoodReduction_of_isNewformOf hf v (not_dvd_level_of_dvd hDN v hpD)) hp k

/-! ### Multiplicativity -/

/-- `kronecker D` is completely multiplicative on positive integers. -/
theorem kronecker_mul (D : ℤ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    kronecker D (m * n) = kronecker D m * kronecker D n := by
  have hfac : (m * n).factorization 2 = m.factorization 2 + n.factorization 2 := by
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply]
  have hdm : 2 ^ m.factorization 2 ∣ m := Nat.ordProj_dvd m 2
  have hdn : 2 ^ n.factorization 2 ∣ n := Nat.ordProj_dvd n 2
  have hodd : m * n / 2 ^ (m * n).factorization 2 =
      (m / 2 ^ m.factorization 2) * (n / 2 ^ n.factorization 2) := by
    rw [hfac, pow_add, Nat.div_mul_div_comm hdm hdn]
  have hm' : m / 2 ^ m.factorization 2 ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdm) (by positivity)).ne'
  have hn' : n / 2 ^ n.factorization 2 ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdn) (by positivity)).ne'
  simp only [kronecker]
  rw [hodd, jacobiSym.mul_right' D hm' hn', hfac, pow_add]
  ring

/-- `kronecker D` as an arithmetic function (`0` at `0`). -/
noncomputable def kroneckerFun (D : ℤ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else kronecker D n, rfl⟩

/-- `kroneckerFun D n = kronecker D n` for `n ≠ 0` (PROVED). -/
theorem kroneckerFun_apply (D : ℤ) {n : ℕ} (hn : n ≠ 0) : kroneckerFun D n = kronecker D n := by
  simp [kroneckerFun, hn]

/-- `χ_D(1) = 1` (PROVED). -/
theorem kronecker_one (D : ℤ) : kronecker D 1 = 1 := by
  simp [kronecker]

/-- `kronecker D` is multiplicative. -/
theorem isMultiplicative_kroneckerFun (D : ℤ) : (kroneckerFun D).IsMultiplicative := by
  refine ⟨by rw [kroneckerFun_apply D one_ne_zero, kronecker_one], fun {m n} hmn => ?_⟩
  by_cases hm : m = 0
  · subst hm; simp [kroneckerFun]
  by_cases hn : n = 0
  · subst hn; simp [kroneckerFun]
  rw [kroneckerFun_apply D (mul_ne_zero hm hn), kroneckerFun_apply D hm, kroneckerFun_apply D hn,
    kronecker_mul D hm hn]

/-- `χ_D(p^k) = χ_D(p)^k` (PROVED). -/
theorem kronecker_pow (D : ℤ) {p : ℕ} (hp : p ≠ 0) (k : ℕ) :
    kronecker D (p ^ k) = kronecker D p ^ k := by
  induction k with
  | zero => simp [kronecker_one]
  | succ k ih => rw [pow_succ, kronecker_mul D (pow_ne_zero _ hp) hp, ih, pow_succ]

/-! ### The dictionary -/

/-- **The twist dictionary for a curve with good reduction at the primes of `D`** (PROVED): if `D`
is a fundamental discriminant and `E/ℚ` has good reduction at every prime dividing `D`, then
`a_n(E^{(D)}) = χ_D(n) a_n(E)` for every `n ≥ 1` (Mathlib's `WeierstrassCurve.LFunction`, the
blueprint's `qtwist`). No modularity is used. -/
theorem twistDictionary_of_good {E : WeierstrassCurve ℚ} [E.IsElliptic] {D : ℤ}
    (hD : IsFundamentalDiscriminant D)
    (hgood : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ), (natGenerator v : ℤ) ∣ D →
      ((E.baseChange (v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ)).HasGoodReduction
        (v.adicCompletionIntegers ℚ))
    (n : ℕ) (hn : 0 < n) :
    PrintsAnalytic.lcoeff (ZInQ.Contrib.CloudB3RC53.qtwist E D) n =
      twistCoeff (PrintsAnalytic.lcoeff E) D n := by
  have hmulT := isMultiplicative_LFunction (ZInQ.Contrib.CloudB3RC53.qtwist E D)
  have hmul := (isMultiplicative_kroneckerFun D).pmul (isMultiplicative_LFunction E)
  have heq : (ZInQ.Contrib.CloudB3RC53.qtwist E D).LFunction =
      (kroneckerFun D).pmul E.LFunction := by
    rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ hmulT _ hmul]
    intro p k hp
    rw [pmul_apply, LFunction_qtwist_prime_pow_of_good hD hgood hp k,
      kroneckerFun_apply D (pow_ne_zero _ hp.ne_zero), kronecker_pow D hp.ne_zero]
  simp only [PrintsAnalytic.lcoeff, twistCoeff, heq, pmul_apply, kroneckerFun_apply D hn.ne',
    Int.cast_mul]

/-- **The twist dictionary** (PROVED), lane RC8's GLUE `TwistDictionary`: if `f : Newform N 2` is
the newform of the elliptic curve `E/ℚ` and `D` is a fundamental discriminant prime to `N`, then
`a_n(E^{(D)}) = χ_D(n) a_n(E)` for every `n ≥ 1`, i.e. `L(E^{(D)}, s) = L(s, f, χ_D)` coefficientwise
(Mathlib's `WeierstrassCurve.LFunction`, the blueprint's `qtwist`). The newform enters only through
good reduction of `E` at the primes not dividing `N` (`hasGoodReduction_of_isNewformOf`). -/
theorem twistDictionary : TwistDictionary := by
  intro E hE N _ f hf D hD hDN n hn
  exact twistDictionary_of_good hD
    (fun v hpD => hasGoodReduction_of_isNewformOf hf v (not_dvd_level_of_dvd hDN v hpD)) n hn

end ZInQ.Manuscript.RC.TwistDictionary
