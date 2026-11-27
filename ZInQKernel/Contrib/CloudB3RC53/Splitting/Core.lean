import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Glue
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind

/-!
# Splitting in a quadratic field, part 1: a quadratic generator and Kummer–Dedekind

For a number field `K` of degree two and an algebraic integer `θ` with
`minpoly ℚ θ = X² + uX + v` (`u v ∈ ℤ`):

* `minpolyZ_eq`: `minpoly ℤ θ = X² + uX + v`;
* `pbOf`: the power basis `(1, θ)` of `K/ℚ`, and `discr_pbOf`: its discriminant is `u² − 4v`;
* `disc_mem_conductor`: `u² − 4v` lies in the conductor of `ℤ[θ]` in `𝓞_K` (Mathlib's
  `Algebra.discr_mul_isIntegral_mem_adjoin`), so a prime `p ∤ u² − 4v` does not divide the
  exponent of `θ` (`not_dvd_exponent`);
* `splitsIn_of_factor`: if moreover `X² + uX + v ≡ (X − a)(X − b) (mod p)` with `a ≢ b`, then `p`
  splits in `K` in the sense of `CST.SplitsIn` (Mathlib's Kummer–Dedekind correspondence
  `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` for the two primes
  `𝔭 = (p, θ − a)`, `𝔮 = (p, θ − b)`, and `p 𝓞_K = 𝔭 𝔮` by a direct computation).

All statements are PROVED.
-/

noncomputable section

open Polynomial NumberField Ideal IntermediateField

namespace ZInQ.Contrib.CloudB3RC53.Splitting

variable {K : Type} [Field K] [NumberField K]

section Gen

theorem natDegree_quad (u v : ℤ) : (X ^ 2 + C (u : ℚ) * X + C (v : ℚ)).natDegree = 2 := by
  compute_degree!

theorem coeff_quad_one (u v : ℤ) : (X ^ 2 + C (u : ℚ) * X + C (v : ℚ)).coeff 1 = (u : ℚ) := by
  simp only [coeff_add, coeff_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

variable (θ : 𝓞 K) (u v : ℤ)

/-- The minimal polynomial over `ℤ` is the one over `ℚ`. -/
theorem minpolyZ_eq (hmin : minpoly ℚ (θ : K) = X ^ 2 + C (u : ℚ) * X + C (v : ℚ)) :
    minpoly ℤ θ = X ^ 2 + C u * X + C v := by
  have h := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (RingOfIntegers.isIntegral_coe θ)
  rw [RingOfIntegers.minpoly_coe, hmin] at h
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  rw [← h]
  simp

variable {θ u v}

theorem isIntegral_rat (θ : 𝓞 K) : IsIntegral ℚ (θ : K) :=
  (RingOfIntegers.isIntegral_coe θ).tower_top

/-- `θ` generates `K` over `ℚ`. -/
theorem adjoin_eq_top (hK : Module.finrank ℚ K = 2)
    (hmin : minpoly ℚ (θ : K) = X ^ 2 + C (u : ℚ) * X + C (v : ℚ)) :
    Algebra.adjoin ℚ {(θ : K)} = ⊤ := by
  have hdeg : (minpoly ℚ (θ : K)).natDegree = 2 := by
    rw [hmin]; exact natDegree_quad u v
  have h1 : Module.finrank ℚ ℚ⟮(θ : K)⟯ = 2 := by
    rw [IntermediateField.adjoin.finrank (isIntegral_rat θ), hdeg]
  have h2 : ℚ⟮(θ : K)⟯ = ⊤ := IntermediateField.eq_of_le_of_finrank_eq le_top
    (by rw [h1, IntermediateField.finrank_top', hK])
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (isIntegral_rat θ).isAlgebraic, h2,
    IntermediateField.top_toSubalgebra]

/-- The power basis `(1, θ)` of `K/ℚ`. -/
def pbOf (hK : Module.finrank ℚ K = 2)
    (hmin : minpoly ℚ (θ : K) = X ^ 2 + C (u : ℚ) * X + C (v : ℚ)) : PowerBasis ℚ K :=
  PowerBasis.ofAdjoinEqTop' (isIntegral_rat θ) (adjoin_eq_top hK hmin)

theorem pbOf_gen (hK : Module.finrank ℚ K = 2)
    (hmin : minpoly ℚ (θ : K) = X ^ 2 + C (u : ℚ) * X + C (v : ℚ)) :
    (pbOf hK hmin).gen = (θ : K) :=
  PowerBasis.ofAdjoinEqTop'_gen _ _

theorem pbOf_dim (hK : Module.finrank ℚ K = 2)
    (hmin : minpoly ℚ (θ : K) = X ^ 2 + C (u : ℚ) * X + C (v : ℚ)) :
    (pbOf hK hmin).dim = 2 := by
  rw [pbOf, PowerBasis.ofAdjoinEqTop'_dim, hmin]; exact natDegree_quad u v

/-- **The discriminant of `(1, θ)` is `u² − 4v`.** -/
theorem discr_pbOf (hK : Module.finrank ℚ K = 2)
    (hmin : minpoly ℚ (θ : K) = X ^ 2 + C (u : ℚ) * X + C (v : ℚ)) :
    Algebra.discr ℚ (pbOf hK hmin).basis = ((u ^ 2 - 4 * v : ℤ) : ℚ) := by
  set pb := pbOf hK hmin
  have hgen : pb.gen = (θ : K) := pbOf_gen hK hmin
  have hdim : pb.dim = 2 := pbOf_dim hK hmin
  have hroot : (θ : K) ^ 2 = -(u : K) * θ - v := by
    have := minpoly.aeval ℚ (θ : K)
    rw [hmin] at this
    simp only [map_add, map_pow, aeval_X, map_mul, aeval_C, eq_ratCast, Rat.cast_intCast] at this
    linear_combination this
  have htr1 : Algebra.trace ℚ K 1 = 2 := by
    rw [show (1 : K) = algebraMap ℚ K 1 by simp, Algebra.trace_algebraMap, hK]; simp
  have htrθ : Algebra.trace ℚ K θ = -u := by
    rw [← hgen, PowerBasis.trace_gen_eq_nextCoeff_minpoly, hgen, hmin,
      Polynomial.nextCoeff_of_natDegree_pos (by rw [natDegree_quad]; norm_num), natDegree_quad]
    simp only [show (2 : ℕ) - 1 = 1 from rfl, coeff_quad_one]
  have htrθ2 : Algebra.trace ℚ K ((θ : K) ^ 2) = u ^ 2 - 2 * v := by
    rw [hroot, map_sub, show -(u : K) * θ = (-(u : ℚ)) • (θ : K) by simp [Algebra.smul_def],
      show (v : K) = algebraMap ℚ K v by simp, LinearMap.map_smul, Algebra.trace_algebraMap, hK,
      htrθ]
    simp; ring
  let e : Fin pb.dim ≃ Fin 2 := finCongr hdim
  rw [← Algebra.discr_reindex ℚ pb.basis e, Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Function.comp_apply,
    PowerBasis.coe_basis, hgen, e, finCongr_symm, finCongr_apply, Fin.cast]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one, ← sq, htrθ,
    htrθ2, one_pow]
  rw [htr1]
  push_cast
  ring

end Gen

section Conductor

variable {θ : 𝓞 K} {u v : ℤ}

/-- **The discriminant `u² − 4v` lies in the conductor of `ℤ[θ]`** (Mathlib's
`Algebra.discr_mul_isIntegral_mem_adjoin`). -/
theorem disc_mem_conductor (hK : Module.finrank ℚ K = 2)
    (hmin : minpoly ℚ (θ : K) = X ^ 2 + C (u : ℚ) * X + C (v : ℚ)) :
    ((u ^ 2 - 4 * v : ℤ) : 𝓞 K) ∈ conductor ℤ θ := by
  rw [mem_conductor_iff]
  intro z
  have h := Algebra.discr_mul_isIntegral_mem_adjoin (R := ℤ) (K := ℚ) (L := K)
    (B := pbOf hK hmin) (by rw [pbOf_gen]; exact RingOfIntegers.isIntegral_coe θ)
    (RingOfIntegers.isIntegral_coe z)
  rw [discr_pbOf, pbOf_gen] at h
  -- transport from `K` to `𝓞 K`
  have hmap : (Algebra.adjoin ℤ {θ}).map (IsScalarTower.toAlgHom ℤ (𝓞 K) K) =
      Algebra.adjoin ℤ {(θ : K)} := by
    rw [AlgHom.map_adjoin, Set.image_singleton]; rfl
  rw [← hmap, Subalgebra.mem_map] at h
  obtain ⟨y, hy, hyz⟩ := h
  have : y = ((u ^ 2 - 4 * v : ℤ) : 𝓞 K) * z := by
    apply RingOfIntegers.coe_injective
    change IsScalarTower.toAlgHom ℤ (𝓞 K) K y = _
    rw [hyz, Algebra.smul_def, map_mul, map_intCast, map_intCast]
  rw [← this]; exact hy

/-- A prime `p ∤ u² − 4v` does not divide the exponent of `θ`. -/
theorem not_dvd_exponent (hK : Module.finrank ℚ K = 2)
    (hmin : minpoly ℚ (θ : K) = X ^ 2 + C (u : ℚ) * X + C (v : ℚ)) {p : ℕ} [hp : Fact p.Prime]
    (hpd : ¬ (p : ℤ) ∣ u ^ 2 - 4 * v) : ¬ p ∣ RingOfIntegers.exponent θ := by
  rw [RingOfIntegers.not_dvd_exponent_iff, codisjoint_iff, Ideal.eq_top_iff_one]
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  obtain ⟨x, y, hxy⟩ := (Irreducible.coprime_iff_not_dvd hprime.irreducible).mpr hpd
  have h1 : (u ^ 2 - 4 * v : ℤ) ∈ comap (algebraMap ℤ (𝓞 K)) (conductor ℤ θ) := by
    rw [Ideal.mem_comap]; simpa using disc_mem_conductor hK hmin
  have h2 : (p : ℤ) ∈ (span {(p : ℤ)} : Ideal ℤ) := mem_span_singleton_self _
  have : (1 : ℤ) = y * (u ^ 2 - 4 * v) + x * p := by linear_combination hxy.symm
  rw [this]
  exact add_mem (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ h1))
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ h2))

end Conductor

section Split

variable {θ : 𝓞 K} {u v : ℤ}

attribute [local instance] Int.ideal_span_isMaximal_of_prime

/-- **The splitting criterion from a factorization modulo `p`** (Kummer–Dedekind): if
`minpoly ℚ θ = X² + uX + v`, `p ∤ u² − 4v`, `u ≡ −(a + b)`, `v ≡ ab (mod p)` and `a ≢ b (mod p)`,
then `p 𝓞_K = 𝔭 𝔮` with `𝔭 ≠ 𝔮` maximal. -/
theorem splitsIn_of_factor (hK : Module.finrank ℚ K = 2)
    (hmin : minpoly ℚ (θ : K) = X ^ 2 + C (u : ℚ) * X + C (v : ℚ)) {p : ℕ} [hp : Fact p.Prime]
    (hpd : ¬ (p : ℤ) ∣ u ^ 2 - 4 * v) (a b : ℤ) (hu : (p : ℤ) ∣ u + a + b)
    (hv : (p : ℤ) ∣ v - a * b) (hab : ¬ (p : ℤ) ∣ b - a) : CST.SplitsIn K p := by
  classical
  have hexp := not_dvd_exponent hK hmin hpd
  have hminZ := minpolyZ_eq θ u v hmin
  -- the factorization of `minpoly` modulo `p`
  have hfact : map (Int.castRingHom (ZMod p)) (minpoly ℤ θ) =
      (X - C (a : ZMod p)) * (X - C (b : ZMod p)) := by
    have hu' : ((u : ℤ) : ZMod p) = -((a : ZMod p) + b) := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hu
      push_cast at this; linear_combination this
    have hv' : ((v : ℤ) : ZMod p) = (a : ZMod p) * b := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hv
      push_cast at this; linear_combination this
    rw [hminZ, Polynomial.map_add, Polynomial.map_add, Polynomial.map_pow, map_X,
      Polynomial.map_mul, map_X, map_C, map_C, eq_intCast, eq_intCast, hu', hv', map_neg, map_add,
      map_mul]
    ring
  have hne0 : map (Int.castRingHom (ZMod p)) (minpoly ℤ θ) ≠ 0 :=
    map_monic_ne_zero (minpoly.monic θ.isIntegral)
  have hmem : ∀ c : ℤ, (c = a ∨ c = b) →
      (X - C c : ℤ[X]).map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod θ p := by
    intro c hc
    rw [Multiset.mem_toFinset, Polynomial.map_sub, map_X, map_C, eq_intCast, hfact,
      UniqueFactorizationMonoid.normalizedFactors_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
      UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C _),
      UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C _),
      (monic_X_sub_C _).normalize_eq_self, (monic_X_sub_C _).normalize_eq_self]
    rcases hc with rfl | rfl <;> simp
  set 𝔭 := (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm
    ⟨_, hmem a (Or.inl rfl)⟩
  set 𝔮 := (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm
    ⟨_, hmem b (Or.inr rfl)⟩
  have h𝔭 : (𝔭 : Ideal (𝓞 K)) = span {(p : 𝓞 K), (θ - a)} := by
    rw [NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span]
    simp
  have h𝔮 : (𝔮 : Ideal (𝓞 K)) = span {(p : 𝓞 K), (θ - b)} := by
    rw [NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span]
    simp
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hmax : ∀ P : primesOver (span {(p : ℤ)}) (𝓞 K), (P : Ideal (𝓞 K)).IsMaximal := by
    intro P
    have : (P : Ideal (𝓞 K)).IsPrime := P.2.1
    refine Ideal.IsPrime.isMaximal inferInstance ?_
    intro h
    have := P.2.2
    have hover := Ideal.LiesOver.over (P := (P : Ideal (𝓞 K))) (p := span {(p : ℤ)})
    have h1 : (p : ℤ) ∈ (P : Ideal (𝓞 K)).comap (algebraMap ℤ (𝓞 K)) := by
      change (p : ℤ) ∈ Ideal.under ℤ (P : Ideal (𝓞 K))
      rw [← hover]
      exact mem_span_singleton_self _
    rw [Ideal.mem_comap, h, Ideal.mem_bot] at h1
    exact hp0 (by simpa using h1)
  refine ⟨𝔭, 𝔮, hmax 𝔭, hmax 𝔮, fun h => ?_, ?_⟩
  · -- distinct factors give distinct primes
    have h' : 𝔭 = 𝔮 := Subtype.ext h
    have hpoly := congrArg Subtype.val
      ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm.injective h')
    have h0 := congrArg (fun q : (ZMod p)[X] => q.coeff 0) hpoly
    simp only [Polynomial.coeff_map, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, map_neg,
      eq_intCast, neg_inj, Polynomial.intCast_coeff_zero] at h0
    apply hab
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [sub_eq_zero]
    exact_mod_cast h0.symm
  · -- `p 𝓞_K = 𝔭 𝔮`
    rw [h𝔭, h𝔮]
    have hroot : (θ : 𝓞 K) ^ 2 + (u : 𝓞 K) * θ + v = 0 := by
      have := minpoly.aeval ℤ θ
      rw [hminZ] at this
      simpa using this
    obtain ⟨k, hk⟩ := hu
    obtain ⟨l, hl⟩ := hv
    have hxy : (θ - a) * (θ - b) = (p : 𝓞 K) * (-(k : 𝓞 K) * θ - l) := by
      have hk' : (u : 𝓞 K) = p * k - a - b := by
        have := congrArg (Int.cast : ℤ → 𝓞 K) hk; push_cast at this; linear_combination this
      have hl' : (v : 𝓞 K) = p * l + a * b := by
        have := congrArg (Int.cast : ℤ → 𝓞 K) hl; push_cast at this; linear_combination this
      rw [hk', hl'] at hroot
      linear_combination hroot
    apply le_antisymm
    · -- `p ∈ 𝔭 𝔮` by Bézout on `b − a`
      rw [span_le, Set.singleton_subset_iff, SetLike.mem_coe]
      have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
      obtain ⟨e, f, hef⟩ := (Irreducible.coprime_iff_not_dvd hprime.irreducible).mpr hab
      have hpp : (p : 𝓞 K) = f * ((θ - a) * p - p * (θ - b)) + e * (p * p) := by
        have := congrArg (Int.cast : ℤ → 𝓞 K) hef
        push_cast at this
        linear_combination (-(p : 𝓞 K)) * this
      suffices hmem' : (f : 𝓞 K) * ((θ - a) * p - p * (θ - b)) + e * (p * p) ∈
          span {(p : 𝓞 K), θ - a} * span {(p : 𝓞 K), θ - b} by rwa [← hpp] at hmem'
      refine add_mem (mul_mem_left _ _ (sub_mem (mul_mem_mul ?_ ?_) (mul_mem_mul ?_ ?_)))
        (mul_mem_left _ _ (mul_mem_mul ?_ ?_))
      all_goals first
        | exact subset_span (Set.mem_insert _ _)
        | exact subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · -- `𝔭 𝔮 ⊆ p 𝓞_K`
      rw [Ideal.mul_le]
      intro r hr s hs
      obtain ⟨c₁, d₁, rfl⟩ := mem_span_pair.mp hr
      obtain ⟨c₂, d₂, rfl⟩ := mem_span_pair.mp hs
      rw [mem_span_singleton]
      refine ⟨c₁ * c₂ * p + c₁ * d₂ * (θ - b) + d₁ * c₂ * (θ - a) +
        d₁ * d₂ * (-(k : 𝓞 K) * θ - l), ?_⟩
      linear_combination d₁ * d₂ * hxy

end Split

end ZInQ.Contrib.CloudB3RC53.Splitting
