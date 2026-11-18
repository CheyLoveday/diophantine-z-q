import ZInQKernel.Contrib.CloudB3RC53.Prints.CST
import ZInQKernel.Contrib.OneProof.RC.KSplit.Seed

/-!
# Lane RC22 (glue sweep, symbols): the splitting criterion in `ℚ(√k)`, PROVED

Lane RC3 (`RC/KSplit/`) reads "`p` is `K`-split", `K = ℚ(√k)`, as the Legendre condition
`jacobiSym k p = 1` (Lemma `ex:sec7-ksplit-seed`, tex 2628–2654, and Proposition
`ex:app-nonempty-seeds`, tex 10259–10507), citing the textbook criterion "an odd prime `p ∤ k`
splits in `ℚ(√k)` iff `(k/p) = 1`" as GLUE (`Seed.lean`, module docstring). The criterion is not a
Lean hypothesis there: it is only the reading of `AppGCongruence`, `exists_ksplit_prime_v2_eq_two`
and `ksplit_seed`. Here it is PROVED over Mathlib's genuine objects, from the Kummer–Dedekind
theorem (`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`):

* for a number field `K` with a power basis over `ℚ` whose generator has minimal polynomial
  `X² − k` (any model of `ℚ(√k)`), and an odd prime `p ∤ k`:
  - `card_primesOver_eq_two_iff`: the number of primes of `𝓞 K` above `p` is `2` iff
    `(k/p) = 1`; `card_primesOver_eq_one_iff`: it is `1` iff `(k/p) = −1`;
  - `splitsIn_iff_jacobiSym_eq_one`: `p𝓞_K = 𝔭𝔮` with `𝔭 ≠ 𝔮` maximal (the shared top layer's
    `CST.SplitsIn`) iff `(k/p) = 1`;
* `QuadField k = AdjoinRoot (X² − k)` is `ℚ(√k)`; the instance `Fact (Irreducible (X² − k))` holds
  under lane RC3's hypotheses on `k` (`fact_irreducible_of_squarefree`);
* lane RC3's statements with genuine splitting: `exists_split_prime_v2_eq_two` (the `K`-split
  prime of the seed argument splits in `ℚ(√k)`), `appGCongruenceSplit_iff` (the App G congruence
  over the primes split in `ℚ(√k)` is lane RC3's `AppGCongruence`), `not_appGCongruenceSplit`.

The proof of the criterion: `ℤ[√k]` has discriminant `4k`, so `4k` lies in its conductor in
`𝓞 K` (`Algebra.discr_mul_isIntegral_mem_adjoin`) and `p ∤ 4k` does not divide the exponent of
`√k`; the primes above `p` correspond to the monic irreducible factors of `X² − k` mod `p`: two
distinct linear factors iff `k` is a nonzero square mod `p`, one quadratic factor otherwise; and
two distinct roots `r, s` mod `p` give `p𝓞_K = (p, √k − r)(p, √k − s)` explicitly
(`splitsIn_of_roots`).
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Sym

open Polynomial NumberField ZInQ.Contrib.CloudB3RC53.CST

section Criterion

/-- `X² − k` is monic over `ℤ` (PROVED, helper). -/
theorem fZ_monic (k : ℤ) : (X ^ 2 - C k : ℤ[X]).Monic := monic_X_pow_sub_C _ (by norm_num)

/-- `X² − k` over `ℤ` maps to `X² − k` over `ℚ` (PROVED, helper). -/
theorem map_fZ (k : ℤ) : (X ^ 2 - C k : ℤ[X]).map (algebraMap ℤ ℚ) = X ^ 2 - C (k : ℚ) := by
  simp

variable {K : Type} [Field K] [NumberField K] {k : ℤ} (pb : PowerBasis ℚ K)
  (hpb : minpoly ℚ pb.gen = X ^ 2 - C (k : ℚ))
include hpb

/-- The generator `√k` is an algebraic integer (PROVED, helper). -/
theorem isIntegral_gen : IsIntegral ℤ pb.gen := by
  refine ⟨X ^ 2 - C k, fZ_monic k, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap ℚ, map_fZ k, ← hpb, minpoly.aeval]

/-- The generator `√k` as an element of `𝓞 K`. -/
noncomputable def genInt : 𝓞 K := ⟨pb.gen, isIntegral_gen pb hpb⟩

/-- The minimal polynomial of `√k` over `ℤ` is `X² − k` (PROVED, helper). -/
theorem minpoly_genInt : minpoly ℤ (genInt pb hpb) = X ^ 2 - C k := by
  have h := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (isIntegral_gen pb hpb)
  rw [hpb, ← map_fZ k] at h
  have h' : minpoly ℤ pb.gen = X ^ 2 - C k :=
    (Polynomial.map_injective _ (algebraMap ℤ ℚ).injective_int h).symm
  rw [← RingOfIntegers.minpoly_coe]
  exact h'

/-- The power basis has two elements (PROVED, helper). -/
theorem dim_eq : pb.dim = 2 := by
  rw [← PowerBasis.natDegree_minpoly, hpb, natDegree_X_pow_sub_C]

/-- `[K : ℚ] = 2` (PROVED, helper). -/
theorem finrank_eq_two : Module.finrank ℚ K = 2 := by
  rw [pb.finrank, dim_eq pb hpb]

/-- The discriminant of the basis `1, √k` is `4k` (PROVED). -/
theorem discr_powerBasis_eq : Algebra.discr ℚ pb.basis = 4 * k := by
  rw [Algebra.discr_powerBasis_eq_norm, finrank_eq_two pb hpb, hpb]
  have h2 : (aeval pb.gen) (derivative (X ^ 2 - C (k : ℚ))) = algebraMap ℚ K 2 * pb.gen := by
    simp [aeval_def]
    left
    norm_num
  rw [h2, map_mul, Algebra.norm_algebraMap, finrank_eq_two pb hpb]
  have hn := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
  rw [dim_eq pb hpb, hpb] at hn
  rw [hn]
  simp only [coeff_sub, coeff_X_pow, coeff_C_zero]
  norm_num


/-- `4k` lies in the conductor of `ℤ[√k]` in `𝓞 K`, from `discr = 4k` and
`Algebra.discr_mul_isIntegral_mem_adjoin` (PROVED). -/
theorem four_k_mem_conductor :
    algebraMap ℤ (𝓞 K) (4 * k) ∈ conductor ℤ (genInt pb hpb) := by
  rw [mem_conductor_iff]
  intro b
  have hz : IsIntegral ℤ (b : K) := b.isIntegral_coe
  have h := Algebra.discr_mul_isIntegral_mem_adjoin ℚ (isIntegral_gen pb hpb) hz
  rw [discr_powerBasis_eq pb hpb] at h
  let f : 𝓞 K →ₐ[ℤ] K := (algebraMap (𝓞 K) K).toIntAlgHom
  have hinj : Function.Injective f := RingOfIntegers.coe_injective
  have himg : Algebra.adjoin ℤ {pb.gen} = (Algebra.adjoin ℤ {genInt pb hpb}).map f := by
    rw [← Algebra.adjoin_image, Set.image_singleton]
    rfl
  rw [himg] at h
  obtain ⟨y, hy, hfy⟩ := Subalgebra.mem_map.mp h
  have hy' : y = algebraMap ℤ (𝓞 K) (4 * k) * b := by
    apply hinj
    rw [hfy, map_mul]
    simp [f, Algebra.smul_def]
    left; left
    exact (map_ofNat _ 4).symm
  rw [← hy']
  exact hy

/-- A prime `p ∤ 4k` does not divide the Kummer–Dedekind exponent of `√k` (PROVED). -/
theorem not_dvd_exponent {p : ℕ} [hp : Fact p.Prime] (hpk : ¬ (p : ℤ) ∣ 4 * k) :
    ¬ p ∣ RingOfIntegers.exponent (genInt pb hpb) := by
  rw [RingOfIntegers.not_dvd_exponent_iff, codisjoint_iff, Ideal.eq_top_iff_one]
  have hcop : IsCoprime (p : ℤ) (4 * k) :=
    (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp.out)).mpr hpk
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : (4 * k) ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) (conductor ℤ (genInt pb hpb)) :=
    four_k_mem_conductor pb hpb
  have h2 : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.subset_span rfl
  rw [← huv]
  exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_left _ u h2))
    (Ideal.mem_sup_left (Ideal.mul_mem_left _ v h1))

/-- Kummer–Dedekind: the number of primes of `𝓞 K` above `p ∤ 4k` is the number of distinct monic
irreducible factors of `X² − k` mod `p` (PROVED, from Mathlib's
`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`). -/
theorem card_primesOver_eq {p : ℕ} [Fact p.Prime] (hpk : ¬ (p : ℤ) ∣ 4 * k) :
    Nat.card ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) =
      (UniqueFactorizationMonoid.normalizedFactors
        (X ^ 2 - C ((k : ℤ) : ZMod p))).toFinset.card := by
  rw [Nat.card_congr (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
    (not_dvd_exponent pb hpb hpk))]
  rw [Nat.card_eq_finsetCard]
  simp [RingOfIntegers.monicFactorsMod, minpoly_genInt pb hpb]


omit [NumberField K] in
omit hpb in
/-- `X² − a` has two distinct monic irreducible factors over `𝔽_p` (`p` odd) when `a` is a
nonzero square (PROVED, helper). -/
theorem card_factors_of_isSquare {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0)
    (hsq : IsSquare a) :
    (UniqueFactorizationMonoid.normalizedFactors (X ^ 2 - C a)).toFinset.card = 2 := by
  classical
  obtain ⟨s, rfl⟩ := hsq
  have hs0 : s ≠ 0 := by rintro rfl; simp at ha
  have hne : s ≠ -s := by
    intro h
    have h2 : (2 : ZMod p) * s = 0 := by linear_combination h
    have h20 : (2 : ZMod p) ≠ 0 := by
      intro h20
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h20
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
    exact hs0 ((mul_eq_zero.mp h2).resolve_left h20)
  have hfac : (X ^ 2 - C (s * s) : (ZMod p)[X]) = (X - C s) * (X - C (-s)) := by
    simp only [C_mul, C_neg]
    ring
  rw [hfac, UniqueFactorizationMonoid.normalizedFactors_mul (X_sub_C_ne_zero s)
    (X_sub_C_ne_zero (-s)),
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C s),
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C (-s)),
    (monic_X_sub_C s).normalize_eq_self, (monic_X_sub_C (-s)).normalize_eq_self]
  rw [Multiset.toFinset_add, Multiset.toFinset_singleton, Multiset.toFinset_singleton]
  rw [Finset.card_union_of_disjoint]
  · simp
  · rw [Finset.disjoint_singleton]
    intro h
    exact hne (C_inj.mp (sub_right_injective h))

omit [NumberField K] in
omit hpb in
/-- `X² − a` is irreducible over `𝔽_p` when `a` is a nonsquare (PROVED, helper). -/
theorem card_factors_of_not_isSquare {p : ℕ} [Fact p.Prime] {a : ZMod p} (hsq : ¬ IsSquare a) :
    (UniqueFactorizationMonoid.normalizedFactors (X ^ 2 - C a)).toFinset.card = 1 := by
  classical
  have hirr : Irreducible (X ^ 2 - C a : (ZMod p)[X]) := by
    refine irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · rw [natDegree_X_pow_sub_C]; decide
    · intro x hx
      apply hsq
      refine ⟨x, ?_⟩
      have := hx
      simp [IsRoot, sub_eq_zero] at this
      rw [← this]; ring
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hirr,
    (monic_X_pow_sub_C a (by norm_num)).normalize_eq_self]
  simp

omit [NumberField K] in
omit hpb in
/-- An odd prime not dividing `k` does not divide `4k` (PROVED, helper). -/
theorem not_dvd_four_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpk : ¬ (p : ℤ) ∣ k) :
    ¬ (p : ℤ) ∣ 4 * k := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  intro h
  rcases hpz.dvd_or_dvd h with h4 | hk
  · have h4' : p ∣ 2 * 2 := by exact_mod_cast h4
    rcases (Nat.Prime.dvd_mul hp).mp h4' with h | h <;>
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  · exact hpk hk

/-- **The splitting criterion in `ℚ(√k)`, counting primes** (lane RC3's GLUE "an odd prime `p ∤ k`
splits in `K = ℚ(√k)` iff `(k/p) = 1`", the reading of "`K`-split" in Lemma `ex:sec7-ksplit-seed`,
tex 2628–2654, and Proposition `ex:app-nonempty-seeds`, tex 10259–10507): for `K` with a power
basis whose generator has minimal polynomial `X² − k`, and an odd prime `p ∤ k`, there are exactly
two primes of `𝓞 K` above `p` iff `(k/p) = 1`. Kind: PROVED (from Mathlib's Kummer–Dedekind
theorem `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`). Consumer: lane RC3's reading of
`jacobiSym k p = 1` in `AppGCongruence`, `exists_ksplit_prime_v2_eq_two`, `ksplit_seed`. -/
theorem card_primesOver_eq_two_iff {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hpk : ¬ (p : ℤ) ∣ k) :
    Nat.card ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) = 2 ↔ jacobiSym k p = 1 := by
  have hp4k : ¬ (p : ℤ) ∣ 4 * k := not_dvd_four_mul hp.out hp2 hpk
  have hk0 : ((k : ℤ) : ZMod p) ≠ 0 := fun h =>
    hpk ((ZMod.intCast_zmod_eq_zero_iff_dvd k p).mp h)
  rw [card_primesOver_eq pb hpb hp4k, ← jacobiSym.legendreSym.to_jacobiSym,
    legendreSym.eq_one_iff p hk0]
  constructor
  · intro h
    by_contra hsq
    rw [card_factors_of_not_isSquare hsq] at h
    exact absurd h (by norm_num)
  · intro hsq
    exact card_factors_of_isSquare hp2 hk0 hsq

/-- **The inert case**: for an odd prime `p ∤ k` there is exactly one prime of `𝓞 K` above `p` iff
`(k/p) = −1` (lane RC3's GLUE, complementary case; PROVED, Kummer–Dedekind). -/
theorem card_primesOver_eq_one_iff {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hpk : ¬ (p : ℤ) ∣ k) :
    Nat.card ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) = 1 ↔ jacobiSym k p = -1 := by
  have hp4k : ¬ (p : ℤ) ∣ 4 * k := not_dvd_four_mul hp.out hp2 hpk
  have hk0 : ((k : ℤ) : ZMod p) ≠ 0 := fun h =>
    hpk ((ZMod.intCast_zmod_eq_zero_iff_dvd k p).mp h)
  rw [card_primesOver_eq pb hpb hp4k, ← jacobiSym.legendreSym.to_jacobiSym,
    legendreSym.eq_neg_one_iff p]
  constructor
  · intro h hsq
    rw [card_factors_of_isSquare hp2 hk0 hsq] at h
    exact absurd h (by norm_num)
  · intro hsq
    exact card_factors_of_not_isSquare hsq


omit [NumberField K] in
omit hpb in
/-- The normalized factors of `(X − r)(X − s)` over `𝔽_p` (PROVED, helper). -/
theorem normalizedFactors_two {p : ℕ} [Fact p.Prime] (r s : ZMod p) :
    UniqueFactorizationMonoid.normalizedFactors ((X - C r) * (X - C s)) = {X - C r} + {X - C s} := by
  rw [UniqueFactorizationMonoid.normalizedFactors_mul (X_sub_C_ne_zero r) (X_sub_C_ne_zero s),
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C r),
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C s),
    (monic_X_sub_C r).normalize_eq_self, (monic_X_sub_C s).normalize_eq_self]


end Criterion

/-- **Two distinct roots mod `p` give a splitting** `p𝓞_K = (p, θ − r)(p, θ − s)` with distinct
maximal ideals (the shared top layer's `CST.SplitsIn`), for an algebraic integer `θ` whose
minimal polynomial is `≡ (X − r)(X − s) mod p` with `r ≢ s`, and `p` prime to the Kummer–Dedekind
exponent of `θ`. Kind: PROVED (Kummer–Dedekind for the maximality and distinctness, an explicit
ideal computation for the product). -/
theorem splitsIn_of_roots {K : Type} [Field K] [NumberField K] {θ : 𝓞 K} {P : ℤ[X]}
    (hP : minpoly ℤ θ = P) {p : ℕ} [hp : Fact p.Prime]
    (hexp : ¬ p ∣ RingOfIntegers.exponent θ) {r s : ℤ}
    (hfac : P.map (Int.castRingHom (ZMod p)) = (X - C (r : ZMod p)) * (X - C (s : ZMod p)))
    (hrs : (r : ZMod p) ≠ s) : SplitsIn K p := by
  classical
  have hmem : ∀ t : ℤ, (t : ZMod p) = r ∨ (t : ZMod p) = s →
      (X - C t : ℤ[X]).map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod θ p := by
    intro t ht
    have hmapC : (X - C t : ℤ[X]).map (Int.castRingHom (ZMod p)) = X - C (t : ZMod p) := by
      rw [Polynomial.map_sub, map_X, map_C]; rfl
    rw [hmapC]
    simp only [RingOfIntegers.monicFactorsMod, hP, hfac, normalizedFactors_two,
      Multiset.toFinset_add, Multiset.toFinset_singleton, Finset.mem_union,
      Finset.mem_singleton]
    rcases ht with h | h
    · left; rw [h]
    · right; rw [h]
  have hr := hmem r (Or.inl rfl)
  have hs := hmem s (Or.inr rfl)
  have hpr := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span hexp hr
  have hps := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span hexp hs
  refine ⟨_, _, Ideal.primesOver.isMaximal
    ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm ⟨_, hr⟩),
    Ideal.primesOver.isMaximal
    ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm ⟨_, hs⟩), ?_, ?_⟩
  · intro h
    have h1 := (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm.injective
      (Subtype.ext h)
    have h2 := congrArg (fun q : RingOfIntegers.monicFactorsMod θ p => (q : (ZMod p)[X]).coeff 0) h1
    simp at h2
    exact hrs h2
  · rw [hpr, hps]
    simp only [map_sub, aeval_X, aeval_C, algebraMap_int_eq, Int.coe_castRingHom]
    -- the factor relation in `ℤ[X]`
    have hzero : (P - (X - C r) * (X - C s)).map (Int.castRingHom (ZMod p)) = 0 := by
      rw [Polynomial.map_sub, hfac, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_sub,
        map_X, map_C, map_C]
      simp
    have hdiv : C (p : ℤ) ∣ P - (X - C r) * (X - C s) := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have h := congrArg (fun q : (ZMod p)[X] => q.coeff i) hzero
      simp only [Polynomial.coeff_map, coeff_zero] at h
      exact h
    obtain ⟨G, hG⟩ := hdiv
    have h0 : aeval θ P = 0 := by rw [← hP]; exact minpoly.aeval ℤ θ
    have hG' := congrArg (aeval θ) hG
    simp only [map_sub, map_mul, aeval_X, aeval_C, algebraMap_int_eq, Int.coe_castRingHom, h0,
      zero_sub] at hG'
    push_cast at hG'
    have hθ : (θ - r) * (θ - s) = -(p * aeval θ G) := by
      linear_combination -hG'
    apply le_antisymm
    · rw [Ideal.span_singleton_le_iff_mem]
      have hndvd : ¬ (p : ℤ) ∣ s - r := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        exact sub_ne_zero.mpr (Ne.symm hrs)
      obtain ⟨t, u, hut⟩ :=
        (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp.out)).mpr hndvd
      -- `t * p + u * (s - r) = 1`
      have hut' : ((t * p + u * (s - r) : ℤ) : 𝓞 K) = 1 := by rw [hut]; simp
      push_cast at hut'
      have key : (p : 𝓞 K) = u * ((θ - r) * p) - u * (p * (θ - s)) + t * (p * p) := by
        linear_combination (-(p : 𝓞 K)) * hut'
      have hmem' : (u * ((θ - r) * p) - u * (p * (θ - s)) + t * (p * p) : 𝓞 K) ∈
          Ideal.span {(p : 𝓞 K), θ - r} * Ideal.span {(p : 𝓞 K), θ - s} := by
        refine Ideal.add_mem _ (Ideal.sub_mem _ ?_ ?_) ?_
        · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul (Ideal.subset_span (by simp))
            (Ideal.subset_span (by simp)))
        · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul (Ideal.subset_span (by simp))
            (Ideal.subset_span (by simp)))
        · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul (Ideal.subset_span (by simp))
            (Ideal.subset_span (by simp)))
      rw [← key] at hmem'
      exact hmem'
    · rw [Ideal.mul_le]
      intro x hx y hy
      obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hx
      obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.mp hy
      rw [Ideal.mem_span_singleton']
      refine ⟨a * c * p + a * d * (θ - s) + b * c * (θ - r) - b * d * aeval θ G, ?_⟩
      linear_combination (-(b * d)) * hθ


section Split

variable {K : Type} [Field K] [NumberField K] {k : ℤ} (pb : PowerBasis ℚ K)
  (hpb : minpoly ℚ pb.gen = X ^ 2 - C (k : ℚ))
include hpb

/-- **`(k/p) = 1` gives `p𝓞_K = 𝔭𝔮`** (lane RC3's GLUE, the direction used to read "`K`-split";
`CST.SplitsIn` of the shared top layer): for an odd prime `p ∤ k`. Kind: PROVED. -/
theorem splitsIn_of_jacobiSym_eq_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hpk : ¬ (p : ℤ) ∣ k) (hJ : jacobiSym k p = 1) : SplitsIn K p := by
  have hk0 : ((k : ℤ) : ZMod p) ≠ 0 := fun h =>
    hpk ((ZMod.intCast_zmod_eq_zero_iff_dvd k p).mp h)
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p hk0] at hJ
  obtain ⟨s, hs⟩ := hJ
  obtain ⟨s', rfl⟩ := ZMod.intCast_surjective s
  have hs0 : (s' : ZMod p) ≠ 0 := by
    intro h; rw [h, mul_zero] at hs; exact hk0 hs
  refine splitsIn_of_roots (minpoly_genInt pb hpb)
    (not_dvd_exponent pb hpb (not_dvd_four_mul hp.out hp2 hpk)) (r := s') (s := -s') ?_ ?_
  · rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    change X ^ 2 - C ((k : ℤ) : ZMod p) = _
    rw [hs]
    push_cast
    simp only [C_mul, C_neg]
    ring
  · push_cast
    intro h
    have h2 : (2 : ZMod p) * s' = 0 := by linear_combination h
    have h20 : (2 : ZMod p) ≠ 0 := by
      intro h20
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h20
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
    exact hs0 ((mul_eq_zero.mp h2).resolve_left h20)

/-- **`p𝓞_K = 𝔭𝔮` gives `(k/p) = 1`** (lane RC3's GLUE, converse direction): for an odd prime
`p ∤ k`, both factors lie over `p`, so there are two primes above `p`, which excludes the inert
case. Kind: PROVED. -/
theorem jacobiSym_eq_one_of_splitsIn {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hpk : ¬ (p : ℤ) ∣ k) (hS : SplitsIn K p) : jacobiSym k p = 1 := by
  obtain ⟨𝔭, 𝔮, h𝔭, h𝔮, hne, hspan⟩ := hS
  have hmem : ∀ 𝔯 : Ideal (𝓞 K), 𝔯.IsMaximal → Ideal.span {(p : 𝓞 K)} ≤ 𝔯 →
      𝔯 ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
    intro 𝔯 h𝔯 hle
    refine ⟨h𝔯.isPrime, ?_⟩
    rw [Ideal.liesOver_iff]
    refine (Int.ideal_span_isMaximal_of_prime p).eq_of_le ?_ ?_
    · exact Ideal.comap_ne_top _ h𝔯.ne_top
    · rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      show algebraMap ℤ (𝓞 K) p ∈ 𝔯
      simpa using hle (Ideal.mem_span_singleton_self _)
  have h1 := hmem 𝔭 h𝔭 (hspan ▸ Ideal.mul_le_left)
  have h2 := hmem 𝔮 h𝔮 (hspan ▸ Ideal.mul_le_right)
  have hk0 : ((k : ℤ) : ZMod p) ≠ 0 := fun h =>
    hpk ((ZMod.intCast_zmod_eq_zero_iff_dvd k p).mp h)
  by_contra hJ
  have hJ' : jacobiSym k p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff p]
    intro hsq
    exact hJ (by rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p hk0]; exact hsq)
  have hcard := (card_primesOver_eq_one_iff pb hpb hp2 hpk).mpr hJ'
  have hsub := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact hne (congrArg Subtype.val
    (Subsingleton.elim (α := (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) ⟨𝔭, h1⟩ ⟨𝔮, h2⟩))

/-- **The splitting criterion in `ℚ(√k)`** (lane RC3's GLUE, tex 2628–2654, 10259–10507: "an odd
prime `p ∤ k` splits in `K` iff `(k/p) = 1`"), with splitting in the sense of the shared top layer
(`CST.SplitsIn`: `p𝓞_K = 𝔭𝔮`, `𝔭 ≠ 𝔮` maximal). Kind: PROVED (Kummer–Dedekind). Consumer: lane
RC3's reading of "`K`-split" as `jacobiSym k p = 1`. -/
theorem splitsIn_iff_jacobiSym_eq_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpk : ¬ (p : ℤ) ∣ k) : SplitsIn K p ↔ jacobiSym k p = 1 :=
  ⟨jacobiSym_eq_one_of_splitsIn pb hpb hp2 hpk, splitsIn_of_jacobiSym_eq_one pb hpb hp2 hpk⟩

end Split

/-! ### The model `ℚ(√k) = ℚ[X]/(X² − k)` -/

/-- `ℚ(√k)`: the number field `ℚ[X]/(X² − k)` (a field when `X² − k` is irreducible, i.e. `k` is
not a rational square). -/
abbrev QuadField (k : ℤ) : Type := AdjoinRoot (X ^ 2 - C (k : ℚ))

/-- `X² − k ≠ 0` (PROVED, helper). -/
theorem X_sq_sub_C_ne_zero (k : ℤ) : (X ^ 2 - C (k : ℚ)) ≠ 0 :=
  X_pow_sub_C_ne_zero (by norm_num) _

/-- The power basis `1, √k` of `ℚ(√k)`. -/
noncomputable def quadPowerBasis (k : ℤ) [Fact (Irreducible (X ^ 2 - C (k : ℚ)))] :
    PowerBasis ℚ (QuadField k) :=
  AdjoinRoot.powerBasis (X_sq_sub_C_ne_zero k)

/-- The generator of `quadPowerBasis k` has minimal polynomial `X² − k` (PROVED, helper). -/
theorem minpoly_quadPowerBasis (k : ℤ) [Fact (Irreducible (X ^ 2 - C (k : ℚ)))] :
    minpoly ℚ (quadPowerBasis k).gen = X ^ 2 - C (k : ℚ) := by
  rw [quadPowerBasis, AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.minpoly_root (X_sq_sub_C_ne_zero k)).trans (by
    rw [(monic_X_pow_sub_C _ (by norm_num)).leadingCoeff, inv_one, C_1, mul_one])

/-- An integer divisible by a prime to the first power only is not a rational square (PROVED,
helper). -/
theorem not_isSquare_of_squarefree {k : ℤ} (hk : Squarefree k) {q : ℕ} (hq : q.Prime)
    (hqk : (q : ℤ) ∣ k) : ¬ IsSquare (k : ℚ) := by
  rw [Rat.isSquare_intCast_iff]
  rintro ⟨n, rfl⟩
  have hqz : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have h1 : (q : ℤ) ∣ n := by
    rcases hqz.dvd_or_dvd hqk with h | h <;> exact h
  exact hqz.not_isUnit (hk _ (mul_dvd_mul h1 h1))

/-- `X² − k` is irreducible over `ℚ` when `k` is not a rational square (PROVED, helper). -/
theorem irreducible_X_sq_sub_C {k : ℤ} (hk : ¬ IsSquare (k : ℚ)) :
    Irreducible (X ^ 2 - C (k : ℚ)) := by
  refine irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [natDegree_X_pow_sub_C]; decide
  · intro x hx
    apply hk
    refine ⟨x, ?_⟩
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hx
    rw [← hx]; ring

/-- Lane RC3's hypotheses on `k` (squarefree, with a prime divisor `q₀`) make `ℚ(√k)` a field
(PROVED). -/
theorem fact_irreducible_of_squarefree {k : ℤ} (hk : Squarefree k) {q : ℕ} (hq : q.Prime)
    (hqk : (q : ℤ) ∣ k) : Fact (Irreducible (X ^ 2 - C (k : ℚ))) :=
  ⟨irreducible_X_sq_sub_C (not_isSquare_of_squarefree hk hq hqk)⟩

/-- **The splitting criterion for `ℚ(√k)`, counting primes** (lane RC3's GLUE, tex 2628–2654,
10259–10507). Kind: PROVED. Consumer: lane RC3's reading of "`K`-split"; discharger:
`card_primesOver_eq_two_iff` (Kummer–Dedekind). -/
theorem quadField_card_primesOver_eq_two_iff (k : ℤ) [Fact (Irreducible (X ^ 2 - C (k : ℚ)))]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpk : ¬ (p : ℤ) ∣ k) :
    Nat.card ((Ideal.span {(p : ℤ)}).primesOver (𝓞 (QuadField k))) = 2 ↔ jacobiSym k p = 1 :=
  card_primesOver_eq_two_iff (quadPowerBasis k) (minpoly_quadPowerBasis k) hp2 hpk

/-- **The splitting criterion for `ℚ(√k)`** (lane RC3's GLUE, tex 2628–2654, 10259–10507), with
`CST.SplitsIn`. Kind: PROVED. Consumer: lane RC3's reading of "`K`-split"; discharger:
`splitsIn_iff_jacobiSym_eq_one`. -/
theorem quadField_splitsIn_iff (k : ℤ) [Fact (Irreducible (X ^ 2 - C (k : ℚ)))] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hpk : ¬ (p : ℤ) ∣ k) :
    SplitsIn (QuadField k) p ↔ jacobiSym k p = 1 :=
  splitsIn_iff_jacobiSym_eq_one (quadPowerBasis k) (minpoly_quadPowerBasis k) hp2 hpk

/-! ### Lane RC3's statements with genuine splitting -/

/-- A prime `p ∤ 6kℓ` is odd and prime to `k` (PROVED, helper). -/
theorem odd_not_dvd_of_not_dvd_six {k : ℤ} {ℓ : ℕ} {p : ℕ} (hp6 : ¬ (p : ℤ) ∣ 6 * (k * ℓ)) :
    p ≠ 2 ∧ ¬ (p : ℤ) ∣ k := by
  refine ⟨fun h => hp6 (by rw [h]; exact ⟨3 * (k * ℓ), by push_cast; ring⟩), fun h => hp6 ?_⟩
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h _) 6

/-- **The `K`-split prime of the seed argument splits in `ℚ(√k)`** (Lemma `ex:sec7-ksplit-seed`,
tex 2643–2653, and tex 10482–10500): lane RC3's `exists_ksplit_prime_v2_eq_two` with the reading
`jacobiSym k p = 1` replaced by genuine splitting (`p𝓞_K = 𝔭𝔮`, two primes above `p`). Kind:
PROVED, from lane RC3's hypotheses (`Fact (Irreducible (X² − k))` follows from them,
`fact_irreducible_of_squarefree`). Consumer: lane RC3's `exists_ksplit_prime_v2_eq_two`;
discharger of its GLUE reading: `quadField_splitsIn_iff`, `quadField_card_primesOver_eq_two_iff`. -/
theorem exists_split_prime_v2_eq_two {ℓ : ℕ} (hℓ_pos : 0 < ℓ) (hℓ_sf : Squarefree ℓ)
    (hℓ12 : ℓ % 12 = 11) {k : ℤ} [Fact (Irreducible (X ^ 2 - C (k : ℚ)))] (hk_odd : Odd k)
    (hk_sf : Squarefree k) {q₀ : ℕ} (hq₀ : q₀.Prime) (hq₀k : (q₀ : ℤ) ∣ k)
    (hq₀ℓ : ¬ q₀ ∣ 2 * ℓ) (n : ℕ) :
    ∃ p : ℕ, n < p ∧ p.Prime ∧ p % 4 = 1 ∧ jacobiSym (ℓ : ℤ) p = -1 ∧
      SplitsIn (QuadField k) p ∧
      Nat.card ((Ideal.span {(p : ℤ)}).primesOver (𝓞 (QuadField k))) = 2 ∧
      ¬ (p : ℤ) ∣ 6 * (k * ℓ) ∧
      (4 : ℤ) ∣ (p : ℤ) + 1 - (ZInQ.Manuscript.curve ((k * ℓ : ℤ) : ℚ)).LFunction p ∧
      ¬ (8 : ℤ) ∣ (p : ℤ) + 1 - (ZInQ.Manuscript.curve ((k * ℓ : ℤ) : ℚ)).LFunction p := by
  obtain ⟨p, hpn, hp, hp4, hJℓ, hJk, hp6, h4, h8⟩ :=
    ZInQ.Manuscript.RC.KSplit.exists_ksplit_prime_v2_eq_two hℓ_pos hℓ_sf hℓ12 hk_odd hk_sf hq₀
      hq₀k hq₀ℓ n
  have := Fact.mk hp
  obtain ⟨hp2, hpk⟩ := odd_not_dvd_of_not_dvd_six hp6
  exact ⟨p, hpn, hp, hp4, hJℓ, (quadField_splitsIn_iff k hp2 hpk).mpr hJk,
    (quadField_card_primesOver_eq_two_iff k hp2 hpk).mpr hJk, hp6, h4, h8⟩

/-- **The App G congruence over the primes split in `ℚ(√k)`** (tex 2636–2641, 10319–10481, with
"`K`-split" read as genuine splitting `CST.SplitsIn`). Kind: definition. Under lane RC3's
hypotheses it is FALSE for every finite `S` (`not_appGCongruenceSplit`), exactly as lane RC3's
`AppGCongruence` (refuted in the same file by `not_appGCongruence`); Elliot's step is the
implication from the absence of a seed. -/
def AppGCongruenceSplit (ℓ : ℕ) (k : ℤ) [Fact (Irreducible (X ^ 2 - C (k : ℚ)))]
    (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ 6 * (k * ℓ) → SplitsIn (QuadField k) p →
    (8 : ℤ) ∣ (p : ℤ) + 1 - (ZInQ.Manuscript.curve ((k * ℓ : ℤ) : ℚ)).LFunction p

/-- **The genuine-splitting App G congruence is lane RC3's `AppGCongruence`** (tex 2636–2641,
10319–10481): the two readings of "`K`-split" agree at every prime of the range. Kind: PROVED
(from `quadField_splitsIn_iff`). Consumer: lane RC3's `AppGCongruence` (Seed.lean). -/
theorem appGCongruenceSplit_iff (ℓ : ℕ) (k : ℤ) [Fact (Irreducible (X ^ 2 - C (k : ℚ)))]
    (S : Finset ℕ) :
    AppGCongruenceSplit ℓ k S ↔ ZInQ.Manuscript.RC.KSplit.AppGCongruence ℓ k S := by
  refine forall_congr' fun p => ?_
  refine ⟨fun h hp hpS hp6 hJ => ?_, fun h hp hpS hp6 hS => ?_⟩
  · have := Fact.mk hp
    obtain ⟨hp2, hpk⟩ := odd_not_dvd_of_not_dvd_six hp6
    exact h hp hpS hp6 ((quadField_splitsIn_iff k hp2 hpk).mpr hJ)
  · have := Fact.mk hp
    obtain ⟨hp2, hpk⟩ := odd_not_dvd_of_not_dvd_six hp6
    exact h hp hpS hp6 ((quadField_splitsIn_iff k hp2 hpk).mp hS)

/-- **The genuine-splitting App G congruence fails for every finite `S`** (status record of lane
RC3's `AppGCongruence`, refuted in the same file by `not_appGCongruence`, tex 2643–2651). Kind:
PROVED, from lane RC3's hypotheses. -/
theorem not_appGCongruenceSplit {ℓ : ℕ} (hℓ_pos : 0 < ℓ) (hℓ_sf : Squarefree ℓ)
    (hℓ12 : ℓ % 12 = 11) {k : ℤ} [Fact (Irreducible (X ^ 2 - C (k : ℚ)))] (hk_odd : Odd k)
    (hk_sf : Squarefree k) {q₀ : ℕ} (hq₀ : q₀.Prime) (hq₀k : (q₀ : ℤ) ∣ k)
    (hq₀ℓ : ¬ q₀ ∣ 2 * ℓ) (S : Finset ℕ) : ¬ AppGCongruenceSplit ℓ k S := by
  rw [appGCongruenceSplit_iff]
  exact ZInQ.Manuscript.RC.KSplit.not_appGCongruence hℓ_pos hℓ_sf hℓ12 hk_odd hk_sf hq₀ hq₀k
    hq₀ℓ S

end ZInQ.Manuscript.RC.GlueSweep.Sym
