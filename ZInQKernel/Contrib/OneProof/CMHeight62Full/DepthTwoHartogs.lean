import ZInQKernel.Contrib.OneProof.CMHeight62Full.Hartogs

/-!
# A Hartogs lemma for depth-two local rings

Let `A` be a Noetherian local ring and `ϖ ∈ 𝔪_A` a nonzerodivisor such that `A ⧸ (ϖ)` is a
discrete valuation ring. Then:

* `A` is a domain (`depthTwo_isDomain`) of Krull dimension two (`depthTwo_ringKrullDim`);
* `(ϖ)` is a prime of height one (`depthTwo_isPrime`, `depthTwo_height`), it is the only
  height-one prime containing `ϖ` (`depthTwo_height_one_cases`), and `A_(ϖ)` is a discrete
  valuation ring (`depthTwo_isDVR`);
* **Hartogs property** (`depthTwo_mem_range`): an element `x` of the fraction field `K` which lies
  in `A_𝔮 ⊆ K` for every height-one prime `𝔮` lies in `A`.

No normality of `A` is assumed: the Hartogs property comes from depth two instead.

The primality of `(ϖ)` and `IsDomain A` are theorems here, not instances, so the statements of
`depthTwo_isDVR` and `depthTwo_iInf_localization_height_one` bind them with `haveI`.

## Proofs

*Domain.* By Krull's intersection theorem every `a ≠ 0` is `ϖ ^ n * a'` with `a' ∉ (ϖ)`. If
`a * b = 0` with `a, b ≠ 0`, then `ϖ ^ (n + m) * (a' * b') = 0`, so `a' * b' = 0 ∈ (ϖ)`, which
contradicts the primality of `(ϖ)`.

*Dimension.* A uniformizer of `A ⧸ (ϖ)` lifts to `t` with `𝔪_A = (ϖ, t)`, so `ht 𝔪_A ≤ 2` by
Krull's height theorem; and `dim A ≥ dim A ⧸ (ϖ) + 1 = 2` because `ϖ` is a nonzerodivisor.

*Hartogs.* If `x ∉ A`, some `y = c • x ∉ A` has a prime conductor `P = {r | r • y ∈ A}`, and
`P ≠ 0`. If `P = 𝔪_A`, write `ϖ • y = α` and pick `u ∈ 𝔪_A` with `u ∉ (ϖ)` (it exists because
`A ⧸ (ϖ)` is not a field); then `u • y = β ∈ A` and `u * α = ϖ * β`, so `α ∈ (ϖ)` and `y ∈ A`,
a contradiction. Hence `0 < P < 𝔪_A`, so `P` has height one, and the hypothesis at `P` gives an
`s ∉ P` with `s ∈ P`.
-/

namespace ZInQ.Contrib.CMHeight62Full

open IsLocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {ϖ : A}
  (hϖ : ϖ ∈ nonZeroDivisors A) (hm : ϖ ∈ maximalIdeal A)
  [IsDomain (A ⧸ Ideal.span {ϖ})] [IsDiscreteValuationRing (A ⧸ Ideal.span {ϖ})]

include hϖ hm

set_option linter.unusedSectionVars false in
/-- The ideal `(ϖ)` is prime. -/
theorem depthTwo_isPrime : (Ideal.span {ϖ}).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

/-- Krull intersection: every nonzero `a` is `ϖ ^ n * a'` with `a' ∉ (ϖ)`. -/
theorem depthTwo_exists_pow_mul {a : A} (ha : a ≠ 0) :
    ∃ (n : ℕ) (a' : A), a' ∉ Ideal.span {ϖ} ∧ a = ϖ ^ n * a' := by
  have hne : Ideal.span {ϖ} ≠ ⊤ := (depthTwo_isPrime hϖ hm).ne_top
  have hinf := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {ϖ}) hne
  have hex : ∃ i, a ∉ Ideal.span {ϖ ^ i} := by
    by_contra! h
    apply ha
    have hmem : a ∈ ⨅ i, Ideal.span {ϖ} ^ i := by
      rw [Submodule.mem_iInf]
      intro i
      rw [Ideal.span_singleton_pow]
      exact h i
    rwa [hinf, Ideal.mem_bot] at hmem
  classical
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    have hspec := Nat.find_spec hex
    rw [h0, pow_zero, Ideal.span_singleton_one] at hspec
    exact hspec Submodule.mem_top
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hmem : a ∈ Ideal.span {ϖ ^ j} := by
    have hmin := Nat.find_min hex (show j < Nat.find hex by omega)
    simpa using hmin
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨j, a', ?_, by rw [← ha', mul_comm]⟩
  intro hmem'
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem'
  apply Nat.find_spec hex
  rw [hj]
  refine Ideal.mem_span_singleton'.mpr ⟨b, ?_⟩
  rw [← ha', ← hb, pow_succ]
  ring

/-- `A` is a domain. -/
theorem depthTwo_isDomain : IsDomain A := by
  have hP := depthTwo_isPrime hϖ hm
  refine @NoZeroDivisors.to_isDomain A _ _ ⟨fun {a b} hab => ?_⟩
  by_contra! h
  obtain ⟨ha, hb⟩ := h
  obtain ⟨n, a', ha', rfl⟩ := depthTwo_exists_pow_mul hϖ hm ha
  obtain ⟨k, b', hb', rfl⟩ := depthTwo_exists_pow_mul hϖ hm hb
  have h0 : ϖ ^ (n + k) * (a' * b') = ϖ ^ (n + k) * 0 := by
    rw [mul_zero, ← hab]
    ring
  have hpow : ϖ ^ (n + k) ∈ nonZeroDivisors A := pow_mem hϖ _
  have hab' : a' * b' = 0 := (mul_cancel_left_mem_nonZeroDivisors hpow).mp h0
  have hmem : a' * b' ∈ Ideal.span {ϖ} := by
    rw [hab']
    exact Ideal.zero_mem _
  rcases hP.mem_or_mem hmem with h | h
  · exact ha' h
  · exact hb' h

set_option linter.unusedSectionVars false in
/-- Some `u ∈ 𝔪_A` is not in `(ϖ)`, because `A ⧸ (ϖ)` is not a field. -/
theorem depthTwo_exists_mem_maximalIdeal_notMem :
    ∃ u ∈ maximalIdeal A, u ∉ Ideal.span {ϖ} := by
  by_contra! h
  have heq : Ideal.span {ϖ} = maximalIdeal A :=
    le_antisymm ((Ideal.span_singleton_le_iff_mem _).mpr hm) fun u hu => h u hu
  have hmax : (Ideal.span {ϖ}).IsMaximal := heq ▸ maximalIdeal.isMaximal A
  exact IsDiscreteValuationRing.not_isField (A ⧸ Ideal.span {ϖ})
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)

set_option linter.unusedSectionVars false in
/-- A lift `t` of a uniformizer of `A ⧸ (ϖ)` gives `𝔪_A = (ϖ, t)`. -/
theorem depthTwo_exists_maximalIdeal_eq_span_pair :
    ∃ t : A, maximalIdeal A = Ideal.span {ϖ, t} := by
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.exists_irreducible (A ⧸ Ideal.span {ϖ})
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective u
  have hueq := IsDiscreteValuationRing.irreducible_iff_uniformizer _ |>.mp hu
  refine ⟨t, le_antisymm (fun a ha => ?_) ?_⟩
  · have hna : Ideal.Quotient.mk (Ideal.span {ϖ}) a ∈ maximalIdeal (A ⧸ Ideal.span {ϖ}) := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hunit
      obtain ⟨b, hb⟩ := hunit.exists_right_inv
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {ϖ})), Ideal.Quotient.eq] at hb
      have h1 : a * b - 1 ∈ maximalIdeal A := (Ideal.span_singleton_le_iff_mem _).mpr hm hb
      have h2 : a * b ∈ maximalIdeal A := Ideal.mul_mem_right b _ ha
      have h3 : (1 : A) ∈ maximalIdeal A := by simpa using Ideal.sub_mem _ h2 h1
      exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
    rw [hueq, Ideal.mem_span_singleton'] at hna
    obtain ⟨c, hc⟩ := hna
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hc
    obtain ⟨d, hd⟩ := hc
    rw [Ideal.mem_span_pair]
    exact ⟨-d, c, by linear_combination -hd⟩
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨hm, ?_⟩
    show t ∈ maximalIdeal A
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    exact hu.not_isUnit (hunit.map (Ideal.Quotient.mk (Ideal.span {ϖ})))

/-- `A` has Krull dimension two. -/
theorem depthTwo_ringKrullDim : ringKrullDim A = 2 := by
  obtain ⟨t, ht⟩ := depthTwo_exists_maximalIdeal_eq_span_pair hϖ hm
  apply le_antisymm
  · rw [← maximalIdeal_height_eq_ringKrullDim]
    have h1 := Ideal.height_le_spanFinrank (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top
    have h2 : (maximalIdeal A).spanFinrank ≤ 2 := by
      rw [ht]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans ?_
      exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    have h3 : (maximalIdeal A).height ≤ 2 := h1.trans (by exact_mod_cast h2)
    exact WithBot.coe_le_coe.mpr h3
  · have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hϖ
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h
    exact h

/-- `(ϖ)` has height one. -/
theorem depthTwo_height : (Ideal.span {ϖ}).height = 1 := by
  have := depthTwo_isDomain hϖ hm
  have := depthTwo_isPrime hϖ hm
  have hmin : Ideal.span {ϖ} ∈ (Ideal.span {ϖ}).minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have hne : (Ideal.span {ϖ}).height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff_eq_bot, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.ne_zero hϖ
  exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)

/-- `A_(ϖ)` is a discrete valuation ring. -/
theorem depthTwo_isDVR :
    haveI := depthTwo_isPrime hϖ hm
    haveI := depthTwo_isDomain hϖ hm
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {ϖ})) := by
  have := depthTwo_isPrime hϖ hm
  have := depthTwo_isDomain hϖ hm
  have hmax : maximalIdeal (Localization.AtPrime (Ideal.span {ϖ})) =
      Ideal.span {algebraMap A (Localization.AtPrime (Ideal.span {ϖ})) ϖ} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField (Localization.AtPrime (Ideal.span {ϖ})) := by
    intro hf
    have hbot := isField_iff_maximalIdeal_eq.mp hf
    rw [hmax, Ideal.span_singleton_eq_bot] at hbot
    refine nonZeroDivisors.ne_zero hϖ ?_
    refine IsLocalization.injective (Localization.AtPrime (Ideal.span {ϖ}))
      (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {ϖ})) ?_
    rw [hbot, map_zero]
  have hpr : Submodule.IsPrincipal (maximalIdeal (Localization.AtPrime (Ideal.span {ϖ}))) :=
    ⟨⟨_, hmax⟩⟩
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 1 5).mpr hpr

/-- `(ϖ)` is the only height-one prime containing `ϖ`. -/
theorem depthTwo_height_one_cases (𝔮 : Ideal A) [𝔮.IsPrime] (h : 𝔮.height = 1) (hq : ϖ ∈ 𝔮) :
    𝔮 = Ideal.span {ϖ} := by
  have := depthTwo_isPrime hϖ hm
  have hle : Ideal.span {ϖ} ≤ 𝔮 := (Ideal.span_singleton_le_iff_mem _).mpr hq
  by_contra hne
  have hlt : Ideal.span {ϖ} < 𝔮 := lt_of_le_of_ne hle (Ne.symm hne)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [depthTwo_height hϖ hm, h] at h2
  exact absurd h2 (by norm_num)

/-- `𝔪_A` has height two. -/
theorem depthTwo_height_maximalIdeal : (maximalIdeal A).height = 2 := by
  have h := maximalIdeal_height_eq_ringKrullDim (R := A)
  rw [depthTwo_ringKrullDim hϖ hm] at h
  exact WithBot.coe_inj.mp h

/-- **Hartogs property.** An element of the fraction field which lies in `A_𝔮` for every
height-one prime `𝔮` lies in `A`. -/
theorem depthTwo_mem_range {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K] (x : K)
    (hx : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 →
      ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A K s * x = algebraMap A K r) :
    x ∈ (algebraMap A K).range := by
  have := depthTwo_isDomain hϖ hm
  have hP0 := depthTwo_isPrime hϖ hm
  by_contra hx'
  have hx1 : x ∉ (1 : Submodule A K) := fun h => hx' (Submodule.mem_one.mp h)
  obtain ⟨c, hc, hP⟩ := exists_isPrime_hartogsConductor hx1
  have := hP
  have hbot : hartogsConductor A (c • x) ≠ ⊥ := by
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A x
    have hb0 : algebraMap A K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine (Submodule.ne_bot_iff _).mpr
      ⟨b, mem_hartogsConductor.mpr ?_, nonZeroDivisors.ne_zero hb⟩
    refine Submodule.mem_one.mpr ⟨c * a, ?_⟩
    rw [← hab, Algebra.smul_def, Algebra.smul_def, map_mul]
    field_simp
  have hPm : hartogsConductor A (c • x) ≠ maximalIdeal A := by
    intro hPm
    obtain ⟨u, hu, hu'⟩ := depthTwo_exists_mem_maximalIdeal_notMem hϖ hm
    have hϖP : ϖ ∈ hartogsConductor A (c • x) := hPm ▸ hm
    have huP : u ∈ hartogsConductor A (c • x) := hPm ▸ hu
    obtain ⟨α, hα⟩ := Submodule.mem_one.mp (mem_hartogsConductor.mp hϖP)
    obtain ⟨β, hβ⟩ := Submodule.mem_one.mp (mem_hartogsConductor.mp huP)
    have hrel : u * α = ϖ * β := by
      apply IsFractionRing.injective A K
      rw [map_mul, map_mul, hα, hβ]
      simp only [Algebra.smul_def]
      ring
    have hαmem : α ∈ Ideal.span {ϖ} := by
      have hmem : u * α ∈ Ideal.span {ϖ} :=
        hrel ▸ Ideal.mul_mem_right β _ (Ideal.mem_span_singleton_self ϖ)
      exact (hP0.mem_or_mem hmem).resolve_left hu'
    obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.mp hαmem
    apply hc
    refine Submodule.mem_one.mpr ⟨γ, ?_⟩
    have hϖ0 : algebraMap A K ϖ ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hϖ
    apply mul_left_cancel₀ hϖ0
    rw [← map_mul, mul_comm ϖ γ, hγ, hα, Algebra.smul_def]
  have hlt : hartogsConductor A (c • x) < maximalIdeal A :=
    lt_of_le_of_ne (le_maximalIdeal hP.ne_top) hPm
  have hheight : (hartogsConductor A (c • x)).height = 1 := by
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [depthTwo_height_maximalIdeal hϖ hm] at h1
    have hne : (hartogsConductor A (c • x)).height ≠ 0 :=
      fun h => hbot (Ideal.height_eq_zero_iff_eq_bot.mp h)
    generalize (hartogsConductor A (c • x)).height = n at h1 hne ⊢
    induction n using ENat.recTopCoe with
    | top => exact absurd h1 (by simp)
    | coe n =>
      norm_cast at h1 hne ⊢
      omega
  obtain ⟨r, s, hs, hrs⟩ := hx _ hP hheight
  apply hs
  rw [mem_hartogsConductor]
  refine Submodule.mem_one.mpr ⟨c * r, ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← hrs]
  ring

/-- **Hartogs property**, subalgebra form: the intersection inside `K` of the localizations
`A_𝔮` at the height-one primes is `A`. -/
theorem depthTwo_iInf_localization_height_one {K : Type*} [Field K] [Algebra A K]
    [IsFractionRing A K] :
    haveI := depthTwo_isDomain hϖ hm
    ⨅ 𝔮 : {𝔮 : PrimeSpectrum A // 𝔮.asIdeal.height = 1},
      localizationAtPrimeSubalgebra (K := K) 𝔮.1.asIdeal = ⊥ := by
  have := depthTwo_isDomain hϖ hm
  refine le_antisymm (fun x hx => ?_) bot_le
  rw [Algebra.mem_bot]
  refine depthTwo_mem_range hϖ hm x fun 𝔮 h𝔮 h1 => ?_
  have hmem := (iInf_le (fun 𝔮 : {𝔮 : PrimeSpectrum A // 𝔮.asIdeal.height = 1} =>
    localizationAtPrimeSubalgebra (K := K) 𝔮.1.asIdeal) ⟨⟨𝔮, h𝔮⟩, h1⟩) hx
  exact (mem_localizationAtPrimeSubalgebra_iff 𝔮 x).mp hmem

end ZInQ.Contrib.CMHeight62Full
