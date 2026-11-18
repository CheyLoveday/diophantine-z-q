import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.FromPrintsAnalytic
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Milne
import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Dictionary
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform

/-!
# Lane RC22 (glue sweep): the level of a functional equation is supported on bad primes

Lane RC13 (`Nonvanishing/FromPrintsAnalytic.lean`) derives its printed leaves from lane RC8's curve
forms with two GLUE facts:

* `FromRC8.LevelSupport` (GLUE): if `L(A, s)` satisfies the functional equation of level `N`
  (lane RC8's `RootNumberAt`), every prime of `N` is a prime at which the model of `A` is not good;
* `FromRC8.RootNumberExists` (GLUE): every elliptic curve over `ℚ` has a root number.

This file proves `LevelSupport` from lane RC8's printed leaf `ModularNewform` alone
(`levelSupport_of_modularNewform`), and identifies `RootNumberExists` with lane RC8's
`MilneHasseWeil`, which RC8 proves from `ModularNewform` and the GLUE `HasseConvergence`
(`rootNumberExists_of_modularNewform`).

**Proof of `LevelSupport`.** Let `f : Newform M 2` be the newform of `A` (`ModularNewform`). Lane
RC8's `eq_level_and_sign_of_rootNumberAt` (a nonzero entire function satisfies functional equations
of at most one level) gives `N = M`. Let `p ∣ M` be prime and suppose the model of `A` is good at
`p` (`GoodAt A p`: `p`-integral with discriminant a `p`-adic unit).

* *The curve side.* Over `𝓞_v ≅ ℤ_p` the model is integral with unit discriminant, hence minimal
  with good reduction (`hasGoodReduction_of_goodAt`), so Mathlib's local polynomial at `p` is
  `1 − a T + p T²` and the Dirichlet coefficients of Mathlib's `L(A, s)` satisfy
  `a_{p²}(A) = a_p(A)² − p` (`LFunction_prime_sq_of_goodAt`).
* *The newform side.* A newform is an eigenvector of `U_p` for `p ∣ M` with eigenvalue `a_p(f)`
  (Tau Ceti's `Newform.toEigenform`, Diamond–Shurman Theorem 5.8.2, Miyake Theorem 4.6.13), and
  its character vanishes at `p ∣ M`, so the Hecke recurrence reads `a_{p²}(f) = a_p(f)²`.

As `a_n(f) = a_n(A)` (`IsNewformOf`), `a_p² − p = a_p²`, i.e. `p = 0`: a contradiction.

The hypothesis used is the PRINT `ModularNewform` (BCDT Theorem A, condition (2) of the
Introduction; Milne, *Modular functions and modular forms* v1.31, Theorem 11.19 and
Proposition 11.21), which lane RC8 states and lane RC13 already uses through RC8's curve forms.
All results here are `PROVED`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Ana

open WeierstrassCurve IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum
  ZInQ.Literature

/-! ### A `p`-integral model over `ℚ_p` -/

section Local

variable (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

/-- **A `p`-integral rational number is a `v`-adic integer** (PROVED): if `p = natGenerator v`
does not divide the denominator of `x ∈ ℚ`, then `x` is the image of an element of `𝓞_v`. -/
theorem exists_lift_of_not_dvd_den (x : ℚ) (hx : ¬ natGenerator v ∣ x.den) :
    ∃ r : v.adicCompletionIntegers ℚ,
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r =
        algebraMap ℚ (v.adicCompletion ℚ) x := by
  have hu : IsUnit ((x.den : ℤ) : v.adicCompletionIntegers ℚ) :=
    (isUnit_intCast_iff v _).mpr (by exact_mod_cast hx)
  refine ⟨(x.num : v.adicCompletionIntegers ℚ) * ↑hu.unit⁻¹, ?_⟩
  have hmul : ((x.num : v.adicCompletionIntegers ℚ) * ↑hu.unit⁻¹) *
      ((x.den : ℤ) : v.adicCompletionIntegers ℚ) = (x.num : v.adicCompletionIntegers ℚ) := by
    rw [mul_assoc, IsUnit.val_inv_mul, mul_one]
  have hden : ((x.den : ℤ) : v.adicCompletion ℚ) ≠ 0 := by
    exact_mod_cast x.den_ne_zero
  have hx' : algebraMap ℚ (v.adicCompletion ℚ) x * ((x.den : ℤ) : v.adicCompletion ℚ) =
      ((x.num : ℤ) : v.adicCompletion ℚ) := by
    rw [← map_intCast (algebraMap ℚ (v.adicCompletion ℚ)),
      ← map_intCast (algebraMap ℚ (v.adicCompletion ℚ)), ← map_mul]
    congr 1
    push_cast
    exact Rat.mul_den_eq_num x
  have h := congrArg (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) hmul
  rw [map_mul, map_intCast, map_intCast] at h
  exact mul_right_cancel₀ hden (h.trans hx'.symm)

/-- **A nonzero rational of `p`-adic valuation `0` has numerator and denominator prime to `p`**
(PROVED). -/
theorem not_dvd_num_den_of_padicValRat_eq_zero {p : ℕ} [Fact p.Prime] {x : ℚ} (hx : x ≠ 0)
    (hv : padicValRat p x = 0) : ¬ (p : ℤ) ∣ x.num ∧ ¬ p ∣ x.den := by
  have hp := (Fact.out : p.Prime)
  have hnum0 : x.num ≠ 0 := Rat.num_ne_zero.mpr hx
  have hcop : Nat.Coprime x.num.natAbs x.den := x.reduced
  have hden : ¬ p ∣ x.den := by
    intro h
    have hnum : ¬ p ∣ x.num.natAbs := fun h' =>
      hp.one_lt.ne' (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h' h))
    have h1 : 1 ≤ padicValNat p x.den := one_le_padicValNat_of_dvd x.den_ne_zero h
    have h0 : padicValNat p x.num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hnum
    have := hv
    rw [padicValRat, padicValInt, h0] at this
    omega
  refine ⟨fun h => ?_, hden⟩
  have h' : p ∣ x.num.natAbs := Int.natCast_dvd.mp h
  have h1 : 1 ≤ padicValNat p x.num.natAbs :=
    one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hnum0) h'
  have h0 : padicValNat p x.den = 0 := padicValNat.eq_zero_of_not_dvd hden
  have := hv
  rw [padicValRat, padicValInt, h0] at this
  omega

/-- **A model good at `p` has good reduction over `ℚ_p`** (PROVED): if the model `A` is
`p`-integral with `v_p(Δ) = 0` (lane RC13's `GoodAt A p`, `p = natGenerator v`), then `A` over
`ℚ_v` is minimal with good reduction (it has an integral model over `𝓞_v` whose discriminant is a
unit; `isMinimal_baseChange_of_notMem`). -/
theorem hasGoodReduction_of_goodAt {A : WeierstrassCurve ℚ}
    (hA : Nonvanishing.GoodAt A (natGenerator v)) :
    HasGoodReduction (v.adicCompletionIntegers ℚ) (A.baseChange (v.adicCompletion ℚ)) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆, hΔ0, hΔ⟩ := hA
  have hI : IsIntegral (v.adicCompletionIntegers ℚ) (A.baseChange (v.adicCompletion ℚ)) :=
    isIntegral_of_exists_lift _ (exists_lift_of_not_dvd_den v _ h₁)
      (exists_lift_of_not_dvd_den v _ h₂) (exists_lift_of_not_dvd_den v _ h₃)
      (exists_lift_of_not_dvd_den v _ h₄) (exists_lift_of_not_dvd_den v _ h₆)
  set W := integralModel (v.adicCompletionIntegers ℚ) (A.baseChange (v.adicCompletion ℚ))
  have hW : W.baseChange (v.adicCompletion ℚ) = A.baseChange (v.adicCompletion ℚ) :=
    baseChange_integralModel_eq _ _
  -- the discriminant of the integral model is a unit
  have hWΔ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) W.Δ =
      algebraMap ℚ (v.adicCompletion ℚ) A.Δ := by
    have h1 : (W.baseChange (v.adicCompletion ℚ)).Δ =
        algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) W.Δ := by
      rw [baseChange, map_Δ]
    have h2 : (A.baseChange (v.adicCompletion ℚ)).Δ = algebraMap ℚ (v.adicCompletion ℚ) A.Δ := by
      rw [baseChange, map_Δ]
    rw [← h1, hW, h2]
  have : Fact (natGenerator v).Prime := ⟨prime_natGenerator v⟩
  obtain ⟨hnum, hden⟩ := not_dvd_num_den_of_padicValRat_eq_zero hΔ0 hΔ
  have hunit : IsUnit W.Δ := by
    have hd : IsUnit ((A.Δ.den : ℤ) : v.adicCompletionIntegers ℚ) :=
      (isUnit_intCast_iff v _).mpr (by exact_mod_cast hden)
    have hn : IsUnit ((A.Δ.num : ℤ) : v.adicCompletionIntegers ℚ) :=
      (isUnit_intCast_iff v _).mpr hnum
    have heq : W.Δ * ((A.Δ.den : ℤ) : v.adicCompletionIntegers ℚ) =
        ((A.Δ.num : ℤ) : v.adicCompletionIntegers ℚ) := by
      apply IsFractionRing.injective (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
      rw [map_mul, map_intCast, map_intCast, hWΔ, ← map_intCast (algebraMap ℚ (v.adicCompletion ℚ)),
        ← map_intCast (algebraMap ℚ (v.adicCompletion ℚ)), ← map_mul]
      congr 1
      push_cast
      exact Rat.mul_den_eq_num A.Δ
    rw [← heq] at hn
    exact isUnit_of_mul_isUnit_left hn
  have hnotmem : W.Δ ∉ IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) :=
    IsLocalRing.notMem_maximalIdeal.mpr hunit
  have hmin : IsMinimal (v.adicCompletionIntegers ℚ) (A.baseChange (v.adicCompletion ℚ)) := by
    rw [← hW]
    exact isMinimal_baseChange_of_notMem W fun h => hnotmem (Ideal.pow_le_self (by norm_num) h)
  refine (hasGoodReduction_iff _ _).mpr ⟨hmin, ?_⟩
  have h1 : (A.baseChange (v.adicCompletion ℚ)).Δ =
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) W.Δ := by
    rw [← hW, baseChange, map_Δ]
  rw [h1, valuation_of_algebraMap, intValuation_eq_one_iff]
  exact hnotmem

end Local

open Polynomial in
/-- **The coefficients of Mathlib's `L(A, s)` at `p` and `p²` for a model good at `p`**
(PROVED): `a_{p²}(A) = a_p(A)² − p`. The local polynomial at the place above `p` is
`1 − a T + p T²` (good reduction, `hasGoodReduction_of_goodAt`; residue field `𝔽_p`), and the
coefficient of `T²` in its inverse is `a² − p`. -/
theorem LFunction_prime_sq_of_goodAt {A : WeierstrassCurve ℚ} {p : ℕ} (hp : p.Prime)
    (hgood : Nonvanishing.GoodAt A p) :
    A.LFunction (p ^ 2) = A.LFunction p ^ 2 - p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨v, rfl⟩ := exists_natGenerator_eq p
  have hgr := hasGoodReduction_of_goodAt v hgood
  set P := (A.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ)
    with hPdef
  have hPeq := localPolynomial_of_hasGoodReduction (A.baseChange (v.adicCompletion ℚ))
    (R := v.adicCompletionIntegers ℚ)
  rw [natCard_residueField v] at hPeq
  have hP0 : P.coeff 0 = 1 := TwistDictionary.localPolynomial_coeff_zero _
  have hP2 : P.coeff 2 = (natGenerator v : ℤ) := by
    rw [hPdef, hPeq]
    simp [Polynomial.coeff_one]
  have hL1 : A.LFunction (natGenerator v) = -P.coeff 1 := by
    rw [← pow_one (natGenerator v), TwistDictionary.LFunction_prime_pow A v 1]
    exact coeff_one_invOfUnit P hP0
  have hL2 : A.LFunction (natGenerator v ^ 2) = P.coeff 1 ^ 2 - P.coeff 2 := by
    rw [TwistDictionary.LFunction_prime_pow A v 2]
    exact TwistDictionary.coeff_two_invOfUnit_eq_sq_sub P hP0
  rw [hL2, hL1, hP2]
  ring

/-! ### The newform side -/

open HeckeRing.GL2 in
/-- **The Hecke recurrence of a newform at a prime of the level** (PROVED, from Tau Ceti):
for `f : Newform M k` and a prime `p ∣ M`, `a_{p²}(f) = a_p(f)²`. The newform is a full Hecke
eigenform (`Newform.toEigenform`: `U_p f = a_p(f) f` at `p ∣ M`), and in its prime-power
recurrence `a_{p^{r+2}} = a_p a_{p^{r+1}} − χ(p) p^{k−1} a_{p^r}` the character term vanishes at
`p ∣ M`. -/
theorem newform_coeff_prime_sq_of_dvd {M : ℕ} [NeZero M] {k : ℤ} (f : Newform M k) {p : ℕ}
    (hp : p.Prime) (hpM : p ∣ M) :
    PrintsAnalytic.nfCoeff f (p ^ 2) = PrintsAnalytic.nfCoeff f p ^ 2 := by
  have h := f.toEigenform.qExpansion_coeff_prime_pow_add_two f.toEigenform_qExpansion_coeff_one
    hp 0
  have hχ : (MulChar.ofUnitHom f.toEigenform.χ : DirichletCharacter ℂ M) p = 0 := by
    refine MulChar.map_nonunit _ ?_
    rw [ZMod.isUnit_iff_coprime]
    intro hcop
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hpM)
  rw [hχ, zero_mul, zero_mul, sub_zero, Newform.toEigenform_toCuspForm, zero_add, pow_one] at h
  unfold PrintsAnalytic.nfCoeff
  rw [h, sq]

/-! ### `LevelSupport` and `RootNumberExists` -/

open HeckeRing.GL2 PrintsAnalytic in
/-- **Lane RC13's GLUE `LevelSupport`, from lane RC8's print `ModularNewform`** (PROVED; consumer:
`Nonvanishing.FromRC8.bfhSimpleZero_of_curve`, `bfhNonvanishing_of_curve`, `bfhTwistSign_of_curve`,
tex 1985–1997 and App G 9995–10051). If `L(A, s)` satisfies the functional equation of level `N`,
every prime `p ∣ N` is a prime at which the model of `A` is not good. By lane RC8's
`eq_level_and_sign_of_rootNumberAt`, `N` is the level of the newform `f` of `A`; at a prime
`p ∣ N` the newform has `a_{p²} = a_p²` (`newform_coeff_prime_sq_of_dvd`) while a model good at `p`
has `a_{p²} = a_p² − p` (`LFunction_prime_sq_of_goodAt`). -/
theorem levelSupport_of_modularNewform (hM : ModularNewform) :
    Nonvanishing.FromRC8.LevelSupport := by
  intro A hA N w hN p hp hpN hgood
  obtain ⟨M, _, f, hf⟩ := hM A hA
  obtain ⟨hNM, -⟩ := eq_level_and_sign_of_rootNumberAt hf hN
  subst hNM
  have hrec := newform_coeff_prime_sq_of_dvd f hp hpN
  have h1 := hf.2 p hp.pos
  have h2 := hf.2 (p ^ 2) (pow_pos hp.pos 2)
  rw [h1, h2] at hrec
  simp only [lcoeff, LFunction_prime_sq_of_goodAt hp hgood] at hrec
  have hp0 : ((p : ℤ) : ℂ) = 0 := by
    push_cast at hrec ⊢
    linear_combination -hrec
  exact hp.ne_zero (by exact_mod_cast hp0)

open PrintsAnalytic in
/-- **Lane RC13's GLUE `RootNumberExists` is lane RC8's `MilneHasseWeil`** (PROVED; the two
definitions have the same body; consumer: `Nonvanishing.FromRC8.rootNumber_of_mem_integral`,
tex 1994–2001). RC8 proves it (`milneHasseWeil_of`) from its print `ModularNewform` and its GLUE
`HasseConvergence` (absolute convergence of `L(E, s)` on `Re s > 3/2`, from Hasse's bound, which is
not in Mathlib or the tree). -/
theorem rootNumberExists_of_modularNewform (hM : ModularNewform) (hH : HasseConvergence) :
    Nonvanishing.FromRC8.RootNumberExists :=
  milneHasseWeil_of hM hH

/-- `RootNumberExists` and `MilneHasseWeil` are the same proposition (PROVED, by `Iff.rfl`). -/
theorem rootNumberExists_iff_milneHasseWeil :
    Nonvanishing.FromRC8.RootNumberExists ↔ PrintsAnalytic.MilneHasseWeil :=
  Iff.rfl

end ZInQ.Manuscript.RC.GlueSweep.Ana
