import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalInertGood
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Artin34

/-!
# GenusOdd: `ArtinFactorization` without local GLUE

`ArtinFactorization` assumes that every prime dividing the level of `E` splits in `K`. So at a prime
`p` inert in `K`, `p` does not divide the level, and `E` has good reduction at `p`
(`GoodReductionOffLevel`, PROVED from `ModularNewform`). The inert clause of `LocalFactorK` is
therefore only needed at primes of good reduction, where it is PROVED (`localFactorInert_good`),
and the split and ramified clauses are PROVED (`localFactorK_clause_split`,
`localFactorK_clause_good`). The proof of `artinFactorization_of_local` then goes through with no
local hypothesis:

* `not_splitsIn_of_inert`: an inert prime does not split.
* `prod_twistFactor_eq_of_split`: `prod_twistFactor_eq` without `LocalFactorK`, under the
  splitting hypothesis.
* `artinFactorization_of_goodOffLevel : HasseConvergence → GoodReductionOffLevel →
  ArtinFactorization`, `artinFactorization_of_newform' : HasseConvergence → ModularNewform →
  ArtinFactorization`, `genusLower34_of_newform'`.

In particular `LocalFactorInert`, `LocalFactorInertBad` and `LocalFactorInertAdditive23` are not
needed for `ArtinFactorization` or (3.4).

Classification: PROVED.
-/

noncomputable section

open NumberField IsDedekindDomain TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory ArithmeticFunction Rat.HeightOneSpectrum

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Manuscript.RC.PrintsAnalytic

/-- **An inert prime does not split** (PROVED): if `𝔭` is the only prime of `K` above `p`, then
`p 𝓞_K` is not a product of two distinct maximal ideals. -/
theorem not_splitsIn_of_inert {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    {𝔭 : HeightOneSpectrum (𝓞 K)} (hS : primesAbove K p = {𝔭}) : ¬ SplitsIn K p := by
  rintro ⟨P, Q, hP, hQ, hne, hPQ⟩
  have hp0 : ((p : ℤ) : 𝓞 K) ≠ 0 := by
    rw [Int.cast_natCast]; exact_mod_cast hp.ne_zero
  have hspan : ((p : ℤ) : 𝓞 K) ∈ P * Q := by
    rw [← hPQ, Int.cast_natCast]
    exact Ideal.mem_span_singleton_self _
  have hmemP : ((p : ℤ) : 𝓞 K) ∈ P := (Ideal.mul_le_left : P * Q ≤ P) hspan
  have hmemQ : ((p : ℤ) : 𝓞 K) ∈ Q := (Ideal.mul_le_right : P * Q ≤ Q) hspan
  have hPb : P ≠ ⊥ := fun h => hp0 (Ideal.mem_bot.mp (h ▸ hmemP))
  have hQb : Q ≠ ⊥ := fun h => hp0 (Ideal.mem_bot.mp (h ▸ hmemQ))
  let P' : HeightOneSpectrum (𝓞 K) := ⟨P, hP.isPrime, hPb⟩
  let Q' : HeightOneSpectrum (𝓞 K) := ⟨Q, hQ.isPrime, hQb⟩
  have h1 : P' ∈ primesAbove K p := hmemP
  have h2 : Q' ∈ primesAbove K p := hmemQ
  rw [hS] at h1 h2
  have e : P' = Q' := (Set.mem_singleton_iff.mp h1).trans (Set.mem_singleton_iff.mp h2).symm
  exact hne (congrArg HeightOneSpectrum.asIdeal e)

open Classical in
/-- **The Euler factor of `L(E/K, χ)` at `p` is that of `L(E^{(d₁)}) L(E^{(d₂)})`** (PROVED from
`GoodReductionOffLevel` alone, when the primes of bad reduction split in `K`; as
`prod_twistFactor_eq`, with the clauses of `LocalFactorK` supplied by `localFactorK_clause_split`,
`localFactorK_clause_good` and, at an inert prime, which is then of good reduction,
`localFactorInert_good`): the product over the primes `𝔭 ∣ p` of the twisted
local factors of `E/K` equals, as arithmetic functions supported on powers of `p`,
`1/L_p(E^{(d₁)}) · 1/L_p(E^{(d₂)})`. -/
theorem prod_twistFactor_eq_of_split (hG : GoodReductionOffLevel)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) (hDodd : Odd (discr K))
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)
    (c : ℕ) [NeZero c] (d₁ d₂ : ℤ) (hprod : d₁ * d₂ = discr K * c ^ 2) (hd₁ : d₁ % 4 = 1)
    (hsq : Squarefree d₁) (hcd : (c : ℤ) ∣ d₁) (hcD : Nat.Coprime c (discr K).natAbs)
    (hlev : Nat.Coprime (d₁ * d₂).natAbs (newformLevel E))
    (χ : Pic (conductorOrder K c) →* ℂˣ) (hχ : IsQuadRingClassChar K c d₁ χ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∏ 𝔭 ∈ primesAboveFinset K (natGenerator v) (prime_natGenerator v).ne_zero,
        ofPowerSeries (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)))
          (twistFactor E (chiAt (conductorOrder K c) χ) 𝔭) =
      ofPowerSeries (natGenerator v)
        (invC (localPolyQ (qtwist E d₁) v) * invC (localPolyQ (qtwist E d₂) v)) := by
  have hp : (natGenerator v).Prime := prime_natGenerator v
  have hD4 := discr_mod_four_of_odd hK2 hDodd
  have hDsq := squarefree_discr_of_odd hK2 hDodd
  have hd₂4 := d₂_mod_four hprod hd₁ hD4 hcd
  have hd₂sq := squarefree_d₂ hprod hsq hcd hcD hDsq (NeZero.ne c)
  have hd₁0 : d₁ ≠ 0 := hsq.ne_zero
  have hd₂0 : d₂ ≠ 0 := hd₂sq.ne_zero
  have hD0 : discr K ≠ 0 := hDsq.ne_zero
  have hgood : (natGenerator v : ℤ) ∣ d₁ * d₂ → GoodAt E v := fun h =>
    hG E v (not_dvd_level_of_dvd' hp hlev h)
  rw [invC_localPolyQ_qtwist E hd₁ hsq v (fun h => hgood (Dvd.dvd.mul_right h _)),
    invC_localPolyQ_qtwist E hd₂4 hd₂sq v (fun h => hgood (Dvd.dvd.mul_left h _))]
  set p := natGenerator v with hpdef
  have hF : (localPolyQ E v).coeff 0 = 1 :=
    ZInQ.Manuscript.RC.TwistDictionary.localPolynomial_coeff_zero _
  have hκ₁ : kronecker d₁ p = chiD d₁ p := (chiD_eq_kronecker hd₁ hp).symm
  have hκ₂ : kronecker d₂ p = chiD d₂ p := (chiD_eq_kronecker hd₂4 hp).symm
  have hκD : kronecker (discr K) p = chiD (discr K) p := (chiD_eq_kronecker hD4 hp).symm
  -- `χ(𝔭) = χ_{d₁}(N𝔭)` away from `c d₁`
  have hval : ∀ 𝔯 ∈ primesAbove K p, ¬ p ∣ c → ¬ (p : ℤ) ∣ d₁ →
      chiAt (conductorOrder K c) χ 𝔯 = (chiD d₁ (Ideal.absNorm 𝔯.asIdeal) : ℂ) := by
    intro 𝔯 h𝔯 hpc hpd
    rw [chiAt_eq_of_not_dvd (not_dvd_conductor_of_not_dvd hp h𝔯 hpc)]
    exact hχ.2 𝔯 _ (fun h => hpd ((intCast_mem_iff hp h𝔯 d₁).mp h))
  have hsubst1 : (1 : PowerSeries ℂ).subst (PowerSeries.X ^ 2 : PowerSeries ℂ) = 1 := by
    rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.X_pow two_ne_zero), map_one]
  rcases decomposition hK2 hDodd hp with
      ⟨𝔭, 𝔮, hne, hS, hN𝔭, hN𝔮, hu𝔭, hu𝔮, hkr⟩ | ⟨𝔭, hS, hN, hu, hkr⟩ | ⟨𝔭, hS, hN, hu, hpD⟩
  · -- split
    have h𝔭 : 𝔭 ∈ primesAbove K p := by rw [hS]; simp
    have h𝔮 : 𝔮 ∈ primesAbove K p := by rw [hS]; simp
    rw [primesAboveFinset_eq_pair _ hS, Finset.prod_pair hne,
      natCard_residueField_adicCompletionIntegers, natCard_residueField_adicCompletionIntegers,
      hN𝔭, hN𝔮, ← map_mul]
    congr 1
    rw [twistFactor_eq, twistFactor_eq, localFactorK_clause_split E 𝔭 v h𝔭 hN𝔭 hu𝔭,
      localFactorK_clause_split E 𝔮 v h𝔮 hN𝔮 hu𝔮]
    by_cases hpc : p ∣ c
    · obtain ⟨h1, h2⟩ := dvd_both_of_dvd_c hprod hsq hcd (NeZero.ne c) hp hpc
      rw [chiAt_eq_zero_of_dvd hK2 hp h𝔭 hpc, chiAt_eq_zero_of_dvd hK2 hp h𝔮 hpc,
        kronecker_eq_zero_of_dvd hp h1, kronecker_eq_zero_of_dvd hp h2, Int.cast_zero]
    · have hpD : ¬ (p : ℤ) ∣ discr K := fun h => by
        rw [kronecker_eq_zero_of_dvd hp h] at hkr; exact absurd hkr (by norm_num)
      have hp1 : ¬ (p : ℤ) ∣ d₁ := fun h => hpD ((dvd_one_iff hprod hp hpc).mp (Or.inl h))
      have hp2 : ¬ (p : ℤ) ∣ d₂ := fun h => hpD ((dvd_one_iff hprod hp hpc).mp (Or.inr h))
      have hmul := chiD_mul_chiD hprod hd₁0 hd₂0 hD0 hp hpc
      rw [← hκD, hkr] at hmul
      have h12 : chiD d₂ p = chiD d₁ p := by
        rcases chiD_eq_one_or hp hp1 with h | h <;> rw [h] at hmul ⊢ <;> linarith
      rw [hval 𝔭 h𝔭 hpc hp1, hval 𝔮 h𝔮 hpc hp1, hN𝔭, hN𝔮, hκ₁, hκ₂, h12]
  · -- inert
    have h𝔭 : 𝔭 ∈ primesAbove K p := by rw [hS]; simp
    rw [primesAboveFinset_eq_singleton _ hS, Finset.prod_singleton,
      natCard_residueField_adicCompletionIntegers, hN, ofPowerSeries_pow p two_ne_zero]
    congr 1
    rw [twistFactor_eq]
    by_cases hpc : p ∣ c
    · obtain ⟨h1, h2⟩ := dvd_both_of_dvd_c hprod hsq hcd (NeZero.ne c) hp hpc
      rw [chiAt_eq_zero_of_dvd hK2 hp h𝔭 hpc, kronecker_eq_zero_of_dvd hp h1,
        kronecker_eq_zero_of_dvd hp h2, Int.cast_zero, rescale_zero_invC, rescale_zero_invC,
        hsubst1, mul_one]
    · have hpD : ¬ (p : ℤ) ∣ discr K := fun h => by
        rw [kronecker_eq_zero_of_dvd hp h] at hkr; exact absurd hkr (by norm_num)
      have hp1 : ¬ (p : ℤ) ∣ d₁ := fun h => hpD ((dvd_one_iff hprod hp hpc).mp (Or.inl h))
      have hp2 : ¬ (p : ℤ) ∣ d₂ := fun h => hpD ((dvd_one_iff hprod hp hpc).mp (Or.inr h))
      have hmul := chiD_mul_chiD hprod hd₁0 hd₂0 hD0 hp hpc
      rw [← hκD, hkr] at hmul
      have hε : (kronecker d₁ p = 1 ∧ kronecker d₂ p = -1) ∨
          (kronecker d₁ p = -1 ∧ kronecker d₂ p = 1) := by
        rw [hκ₁, hκ₂]
        rcases chiD_eq_one_or hp hp1 with h | h <;> rw [h] at hmul ⊢
        · left; exact ⟨rfl, by linarith⟩
        · right; exact ⟨rfl, by linarith⟩
      rw [hval 𝔭 h𝔭 hpc hp1, hN, chiD_sq_prime hp hp1, Int.cast_one, PowerSeries.rescale_one,
        RingHom.id_apply]
      exact localIdentity_inert hF (localFactorInert_good E 𝔭 v h𝔭 hN
        (hG E v fun hdvd => not_splitsIn_of_inert hp hS (hsplit p hp hdvd))) hε
  · -- ramified
    have h𝔭 : 𝔭 ∈ primesAbove K p := by rw [hS]; simp
    have hpc : ¬ p ∣ c := by
      intro hpc
      have h1 : p ∣ Nat.gcd c (discr K).natAbs := Nat.dvd_gcd hpc (Int.natCast_dvd.mp hpD)
      rw [hcD] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
    have hone := (dvd_one_iff hprod hp hpc).mpr hpD
    have hgoodv : GoodAt E v := hgood (by
      rcases hone with h | h
      · exact Dvd.dvd.mul_right h _
      · exact Dvd.dvd.mul_left h _)
    rw [primesAboveFinset_eq_singleton _ hS, Finset.prod_singleton,
      natCard_residueField_adicCompletionIntegers, hN]
    congr 1
    rw [twistFactor_eq, localFactorK_clause_good E 𝔭 v h𝔭 hN hgoodv]
    have hp2odd : p ≠ 2 := by
      rintro h2
      rw [h2] at hpD
      exact (Int.not_even_iff_odd.mpr hDodd) (even_iff_two_dvd.mpr (by exact_mod_cast hpD))
    by_cases hp1 : (p : ℤ) ∣ d₁
    · have hp2 : ¬ (p : ℤ) ∣ d₂ := fun h => not_dvd_both hprod hDsq hp hpc ⟨hp1, h⟩
      have h2d : ((2 * d₂ : ℤ) : 𝓞 K) ∉ 𝔭.asIdeal := by
        rw [intCast_mem_iff hp h𝔭]
        intro h
        rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h with h | h
        · have : p ∣ 2 := by exact_mod_cast h
          exact hp2odd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
        · exact hp2 h
      rw [chiAt_eq_chiD_partner hK2 hTC hDodd hprod hd₁ hsq hcd hcD hd₂4 hχ
        (not_dvd_conductor_of_not_dvd hp h𝔭 hpc) h2d, hN, kronecker_eq_zero_of_dvd hp hp1,
        Int.cast_zero, rescale_zero_invC, one_mul, hκ₂]
    · have hp2 : (p : ℤ) ∣ d₂ := hone.resolve_left hp1
      rw [hval 𝔭 h𝔭 hpc hp1, hN, kronecker_eq_zero_of_dvd hp hp2, Int.cast_zero,
        rescale_zero_invC, mul_one, hκ₁]

/-- **`ArtinFactorization` from `HasseConvergence` and `GoodReductionOffLevel`** (PROVED
reduction; no local GLUE): as `artinFactorization_of_local`, using the hypothesis of
`ArtinFactorization` that the primes dividing the level split in `K`, so that the inert clause of
`LocalFactorK` is only needed at primes of good reduction (`prod_twistFactor_eq_of_split`). -/
theorem artinFactorization_of_goodOffLevel (hH : HasseConvergence) (hG : GoodReductionOffLevel) :
    ArtinFactorization := by
  intro E _ K _ _ hK2 hTC hDodd hlevelSplit c _ d₁ d₂ hprod hd₁ hsq hcd hcD hlev χ hχ s hs
  have hD4 := discr_mod_four_of_odd hK2 hDodd
  have hDsq := squarefree_discr_of_odd hK2 hDodd
  have hd₂sq := squarefree_d₂ hprod hsq hcd hcD hDsq (NeZero.ne c)
  have hd₁0 : (d₁ : ℚ) ≠ 0 := by exact_mod_cast hsq.ne_zero
  have hd₂0 : (d₂ : ℚ) ≠ 0 := by exact_mod_cast hd₂sq.ne_zero
  set A₁ : ArithmeticFunction ℂ := ((qtwist E d₁).LFunction : ArithmeticFunction ℂ)
  set A₂ : ArithmeticFunction ℂ := ((qtwist E d₂).LFunction : ArithmeticFunction ℂ)
  -- the identity of arithmetic functions
  have key : twistedLFunction E (chiAt (conductorOrder K c) χ) = A₁ * A₂ := by
    have hmulL : (twistedLFunction E (chiAt (conductorOrder K c) χ)).IsMultiplicative := by
      rw [twistedLFunction_eq_eulerProduct]
      exact isMultiplicative_eulerProduct_ofPowerSeries _ (constantCoeff_twistFactor E _)
    have hmulR : (A₁ * A₂).IsMultiplicative :=
      (ZInQ.Literature.isMultiplicative_LFunction _).intCast.mul
        (ZInQ.Literature.isMultiplicative_LFunction _).intCast
    refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ hmulL _ hmulR).mpr fun p k hp => ?_
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨v, rfl⟩ := ZInQ.Literature.exists_natGenerator_eq p
    rw [twistedLFunction_eq_eulerProduct,
      eulerProduct_apply_prime_pow _ (constantCoeff_twistFactor E _) hp k,
      prod_twistFactor_eq_of_split hG E K hK2 hTC hDodd hlevelSplit c d₁ d₂ hprod hd₁ hsq hcd hcD hlev χ hχ v,
      ofPowerSeries_apply_pow hp.one_lt]
    have hA : ∀ (d : ℤ) (j : ℕ), ((qtwist E d).LFunction : ArithmeticFunction ℂ)
        (natGenerator v ^ j) =
        ofPowerSeries (natGenerator v) (invC (localPolyQ (qtwist E d) v)) (natGenerator v ^ j) := by
      intro d j
      rw [intCoe_apply, ofPowerSeries_apply_pow hp.one_lt, invC, PowerSeries.coeff_map,
        ZInQ.Manuscript.RC.TwistDictionary.LFunction_prime_pow]
      rfl
    rw [mul_apply_prime_pow_congr hp (fun j _ => hA d₁ j) (fun j _ => hA d₂ j), ← map_mul,
      ofPowerSeries_apply_pow hp.one_lt]
  -- `L`-series
  have hsum : ∀ d : ℤ, (d : ℚ) ≠ 0 →
      LSeriesSummable (⇑((qtwist E d).LFunction : ArithmeticFunction ℂ)) s := by
    intro d hd
    have := hH (qtwist E d) (qtwist_isElliptic E hd) s hs
    convert this using 1
    funext n
    rw [intCoe_apply]
    rfl
  rw [key, LSeries_mul' (hsum d₁ hd₁0) (hsum d₂ hd₂0)]
  rfl

/-- **`ArtinFactorization` from `HasseConvergence` and `ModularNewform`** (PROVED reduction; no
local GLUE). -/
theorem artinFactorization_of_newform' (hH : HasseConvergence) (hMN : ModularNewform) :
    ArtinFactorization :=
  artinFactorization_of_goodOffLevel hH (goodReductionOffLevel_of_modularNewform hMN)

/-- **(3.4) from the printed leaves, `HasseConvergence` and `ModularNewform`** (PROVED reduction;
no local GLUE). -/
theorem genusLower34_of_newform' (P : Prints) (hH : HasseConvergence) (hMN : ModularNewform) :
    GenusLower34 :=
  genusLower34_of_artin P (artinFactorization_of_newform' hH hMN)

end ZInQ.Contrib.CloudB3RC53.GenusOdd
