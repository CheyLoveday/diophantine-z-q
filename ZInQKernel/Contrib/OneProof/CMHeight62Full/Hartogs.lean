import Mathlib

/-!
# Hartogs property of Noetherian normal domains

Let `A` be a Noetherian integrally closed domain with fraction field `K`. An element of `K` which
lies in the localization `A_𝔮 ⊆ K` for every prime `𝔮` of height one already lies in `A`.
Equivalently, the intersection of the subalgebras `A_𝔮 ⊆ K` over the height-one primes is `⊥`
(`iInf_localization_height_one`).

The statement covers the case of a field (dimension zero): then there is no height-one prime, the
infimum is `⊤`, and the theorem says that `algebraMap A K` is surjective.

## Proof

For `y ∈ K` let `cond y = {r : A | r • y ∈ A}`. If `x ∉ A`, choose `c` with `c • x ∉ A` and
`cond (c • x)` maximal (Noetherian). This ideal `P` is prime, and nonzero. Put `y = c • x`.
If `y • P ⊆ P`, then `y` is integral over `A` (determinant trick), hence `y ∈ A`, a contradiction.
So some `p ∈ P` has `u = p • y ∈ A \ P`; then `u • P ⊆ (p)`, which forces `P` to be minimal
over `(p)`. By Krull's principal ideal theorem `P` has height one, and `y ∈ A_P` gives an
`s ∉ P` with `s • y ∈ A`, i.e. `s ∈ P`: a contradiction.
-/

namespace ZInQ.Contrib.CMHeight62Full

variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- The conductor ideal `{r : A | r • y ∈ A}` of an element `y` of the fraction field. -/
noncomputable def hartogsConductor (A : Type*) [CommRing A] {K : Type*} [Field K] [Algebra A K]
    (y : K) : Ideal A :=
  (1 : Submodule A K).comap (LinearMap.toSpanSingleton A K y)

omit [IsDomain A] [IsFractionRing A K] in
theorem mem_hartogsConductor {y : K} {r : A} :
    r ∈ hartogsConductor A y ↔ r • y ∈ (1 : Submodule A K) :=
  Iff.rfl

omit [IsDomain A] [IsFractionRing A K] in
theorem hartogsConductor_le_smul (y : K) (c : A) :
    hartogsConductor A y ≤ hartogsConductor A (c • y) := by
  intro r hr
  rw [mem_hartogsConductor] at hr ⊢
  rw [smul_comm]
  exact Submodule.smul_mem _ c hr

omit [IsDomain A] [IsFractionRing A K] in
/-- Some multiple `c • x ∉ A` of an element `x ∉ A` has a prime conductor. -/
theorem exists_isPrime_hartogsConductor [IsNoetherianRing A] {x : K}
    (hx : x ∉ (1 : Submodule A K)) :
    ∃ c : A, c • x ∉ (1 : Submodule A K) ∧ (hartogsConductor A (c • x)).IsPrime := by
  obtain ⟨_, ⟨c, hc, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian A A)
      ((fun c : A => hartogsConductor A (c • x)) '' {c | c • x ∉ (1 : Submodule A K)})
      ⟨_, 1, by simpa using hx, rfl⟩
  have hc : c • x ∉ (1 : Submodule A K) := hc
  refine ⟨c, hc, ⟨?_, ?_⟩⟩
  · rw [Ideal.ne_top_iff_one, mem_hartogsConductor, one_smul]
    exact hc
  · intro r s hrs
    by_contra! h
    obtain ⟨hr, hs⟩ := h
    have hrc : (r * c) • x ∉ (1 : Submodule A K) := by
      rwa [mul_smul, ← mem_hartogsConductor]
    have hle : hartogsConductor A (c • x) ≤ hartogsConductor A ((r * c) • x) := by
      rw [mul_smul]
      exact hartogsConductor_le_smul _ r
    have heq : hartogsConductor A (c • x) = hartogsConductor A ((r * c) • x) := by
      by_contra hne
      exact hmax _ ⟨r * c, hrc, rfl⟩ (lt_of_le_of_ne hle hne)
    apply hs
    rw [heq, mem_hartogsConductor]
    have h' := mem_hartogsConductor.mp hrs
    rw [smul_smul] at h' ⊢
    convert h' using 2
    ring

/-- A nonzero prime conductor of an element `y ∉ A` has height one. -/
theorem height_hartogsConductor_eq_one [IsNoetherianRing A] [IsIntegrallyClosed A] {y : K}
    (hy : y ∉ (1 : Submodule A K)) (hP : (hartogsConductor A y).IsPrime)
    (hbot : hartogsConductor A y ≠ ⊥) : (hartogsConductor A y).height = 1 := by
  set P := hartogsConductor A y with hPdef
  have h1 : ∃ p ∈ P, ∃ u : A, u ∉ P ∧ algebraMap A K u = p • y := by
    by_contra! H
    apply hy
    let N : Submodule A K := Submodule.map (Algebra.linearMap A K) P
    have hNfg : N.FG := (IsNoetherian.noetherian P).map _
    have hN0 : N ≠ ⊥ := by
      obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      refine (Submodule.ne_bot_iff _).mpr ⟨algebraMap A K p, Submodule.mem_map_of_mem hp, ?_⟩
      exact (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hp0
    have hint : IsIntegral A y := by
      refine isIntegral_of_smul_mem_submodule N hN0 hNfg y ?_
      intro n hn
      obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hn
      obtain ⟨u, hu⟩ := Submodule.mem_one.mp (mem_hartogsConductor.mp hp)
      refine Submodule.mem_map.mpr ⟨u, ?_, ?_⟩
      · by_contra hup
        exact H p hp u hup hu
      · rw [Algebra.linearMap_apply, hu, Algebra.linearMap_apply, Algebra.smul_def,
          smul_eq_mul, mul_comm]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    exact Submodule.mem_one.mpr ⟨z, hz⟩
  obtain ⟨p, hp, u, hu, hup⟩ := h1
  have hmin : P ∈ (Ideal.span {p}).minimalPrimes := by
    refine ⟨⟨hP, (Ideal.span_singleton_le_iff_mem _).mpr hp⟩, ?_⟩
    rintro Q ⟨hQ, hpQ⟩ hQP q hq
    obtain ⟨w, hw⟩ := Submodule.mem_one.mp (mem_hartogsConductor.mp hq)
    have huq : u * q = w * p := by
      apply IsFractionRing.injective A K
      rw [map_mul, map_mul, hup, hw, Algebra.smul_def, Algebra.smul_def]
      ring
    have hmem : u * q ∈ Q :=
      huq ▸ Q.mul_mem_left w ((Ideal.span_singleton_le_iff_mem _).mp hpQ)
    exact (hQ.mem_or_mem hmem).resolve_left fun h => hu (hQP h)
  have hle : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have hne : P.height ≠ 0 := fun h => hbot (Ideal.height_eq_zero_iff_eq_bot.mp h)
  exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)

/-- **Hartogs property.** In a Noetherian integrally closed domain `A` with fraction field `K`,
an element `x : K` such that for every height-one prime `𝔮` some `s ∉ 𝔮` has `s • x ∈ A`
lies in `A`. -/
theorem mem_range_of_forall_height_one [IsNoetherianRing A] [IsIntegrallyClosed A] (x : K)
    (hx : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 →
      ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A K s * x = algebraMap A K r) :
    x ∈ (algebraMap A K).range := by
  by_contra hx'
  have hx1 : x ∉ (1 : Submodule A K) := fun h => hx' (Submodule.mem_one.mp h)
  obtain ⟨c, hc, hP⟩ := exists_isPrime_hartogsConductor hx1
  have hbot : hartogsConductor A (c • x) ≠ ⊥ := by
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A x
    have hb0 : algebraMap A K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine (Submodule.ne_bot_iff _).mpr
      ⟨b, mem_hartogsConductor.mpr ?_, nonZeroDivisors.ne_zero hb⟩
    refine Submodule.mem_one.mpr ⟨c * a, ?_⟩
    rw [← hab, Algebra.smul_def, Algebra.smul_def, map_mul]
    field_simp
  obtain ⟨r, s, hs, hrs⟩ := hx _ hP (height_hartogsConductor_eq_one hc hP hbot)
  apply hs
  rw [mem_hartogsConductor]
  refine Submodule.mem_one.mpr ⟨c * r, ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← hrs]
  ring

/-- The localization `A_𝔮` at a prime `𝔮`, as a subalgebra of the fraction field `K`. -/
noncomputable abbrev localizationAtPrimeSubalgebra (𝔮 : Ideal A) [𝔮.IsPrime] : Subalgebra A K :=
  Localization.subalgebra.ofField K 𝔮.primeCompl 𝔮.primeCompl_le_nonZeroDivisors

theorem mem_localizationAtPrimeSubalgebra_iff (𝔮 : Ideal A) [𝔮.IsPrime] (x : K) :
    x ∈ localizationAtPrimeSubalgebra (K := K) 𝔮 ↔
      ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A K s * x = algebraMap A K r := by
  constructor
  · rintro ⟨r, s, hs, rfl⟩
    have hs0 : algebraMap A K s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (𝔮.primeCompl_le_nonZeroDivisors hs)
    exact ⟨r, s, hs, by field_simp⟩
  · rintro ⟨r, s, hs, hrs⟩
    have hs0 : algebraMap A K s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (𝔮.primeCompl_le_nonZeroDivisors hs)
    refine ⟨r, s, hs, ?_⟩
    rw [← hrs]
    field_simp

/-- **Hartogs property**, subalgebra form: for a Noetherian integrally closed domain `A`, the
intersection inside `K = Frac A` of the localizations `A_𝔮` at the height-one primes is `A`. -/
theorem iInf_localization_height_one [IsNoetherianRing A] [IsIntegrallyClosed A] :
    ⨅ 𝔮 : {𝔮 : PrimeSpectrum A // 𝔮.asIdeal.height = 1},
      localizationAtPrimeSubalgebra (K := K) 𝔮.1.asIdeal = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  rw [Algebra.mem_bot]
  refine mem_range_of_forall_height_one x fun 𝔮 h𝔮 h1 => ?_
  have hmem := (iInf_le (fun 𝔮 : {𝔮 : PrimeSpectrum A // 𝔮.asIdeal.height = 1} =>
    localizationAtPrimeSubalgebra (K := K) 𝔮.1.asIdeal) ⟨⟨𝔮, h𝔮⟩, h1⟩) hx
  exact (mem_localizationAtPrimeSubalgebra_iff 𝔮 x).mp hmem

/-- The same statement for `FractionRing A`. -/
theorem iInf_localization_height_one_fractionRing [IsNoetherianRing A] [IsIntegrallyClosed A] :
    ⨅ 𝔮 : {𝔮 : PrimeSpectrum A // 𝔮.asIdeal.height = 1},
      localizationAtPrimeSubalgebra (K := FractionRing A) 𝔮.1.asIdeal = ⊥ :=
  iInf_localization_height_one

/-- Field and dimension-zero case: if `A` has no prime of height one, then `algebraMap A K` is
surjective (so `A` is a field). -/
theorem algebraMap_surjective_of_forall_height_ne_one [IsNoetherianRing A]
    [IsIntegrallyClosed A] (h : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height ≠ 1) :
    Function.Surjective (algebraMap A K) := fun x =>
  mem_range_of_forall_height_one x fun 𝔮 h𝔮 h1 => absurd h1 (h 𝔮 h𝔮)

/-- Dimension zero: a Noetherian integrally closed domain of Krull dimension `≤ 0` equals its
fraction field. -/
theorem algebraMap_surjective_of_ringKrullDim_nonpos [IsNoetherianRing A] [IsIntegrallyClosed A]
    (h : ringKrullDim A ≤ 0) : Function.Surjective (algebraMap A K) := by
  refine algebraMap_surjective_of_forall_height_ne_one fun 𝔮 h𝔮 h1 => ?_
  have := Ideal.height_le_ringKrullDim_of_ne_top h𝔮.ne_top
  rw [h1] at this
  exact absurd (this.trans h) (by norm_num)

/-- For a field, the Hartogs intersection is `⊥ = ⊤`: there is no height-one prime. -/
theorem iInf_localization_height_one_of_isField [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hA : IsField A) :
    (⊥ : Subalgebra A K) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => Algebra.mem_bot.mpr ?_
  refine algebraMap_surjective_of_forall_height_ne_one (fun 𝔮 h𝔮 h1 => ?_) x
  have hbot : 𝔮 = ⊥ := by
    let _ : Field A := hA.toField
    exact (Ideal.eq_bot_or_top 𝔮).resolve_right h𝔮.ne_top
  rw [hbot, Ideal.height_bot] at h1
  exact zero_ne_one h1

end ZInQ.Contrib.CMHeight62Full
