import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalRational
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.RationalModel

/-!
# GenusOdd: two lemmas for the inert clause at a prime of bad reduction

* `valued_iota_eq_exp`: at a prime `𝔭 ∣ p` unramified over `p`, a nonzero rational `z` has
  `v_𝔭(z) = exp(−v_p(z))`; hence (`mem_pow_iff_of_rat`) for integral lifts `r ∈ 𝓞_𝔭`, `r' ∈ 𝓞_𝔮` of
  the same rational at two such primes, `r ∈ 𝔪_𝔭ⁿ ↔ r' ∈ 𝔪_𝔮ⁿ`.
* `splits_map_of_card_sq`: a polynomial of degree `≤ 2` over a finite field `k` splits over any
  field `L ⊇ k` with `|L| = |k|²` (an irreducible quadratic divides `X^{|k|²} − X`, which splits in
  `L`).

Classification: PROVED.
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

section Valuation

variable {K : Type} [Field K] [NumberField K] {p : ℕ} {𝔭 : HeightOneSpectrum (𝓞 K)}

/-- `v_𝔭(n) = exp(−v_p(n))` for a nonzero integer `n`, at `𝔭 ∣ p` unramified (PROVED). -/
theorem intValuation_intCast_eq_exp (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p)
    (hu : UnramifiedOver 𝔭 p) {n : ℤ} (hn : n ≠ 0) :
    𝔭.intValuation ((n : ℤ) : 𝓞 K) = exp (-(padicValInt p n : ℤ)) := by
  have : Fact p.Prime := ⟨hp⟩
  set k := padicValInt p n with hk
  obtain ⟨m, hm⟩ := padicValInt_dvd (p := p) n
  rw [← hk] at hm
  have hpm : ¬ (p : ℤ) ∣ m := by
    rintro ⟨c, hc⟩
    have h := (padicValInt_dvd_iff (p := p) (k + 1) n).mp ⟨c, by rw [hm, hc, pow_succ]; ring⟩
    rcases h with h | h
    · exact hn h
    · omega
  conv_lhs => rw [hm]
  rw [Int.cast_mul, Int.cast_pow, map_mul, map_pow, intValuation_prime_eq hp h𝔭 hu,
    (intValuation_intCast_eq_one_iff hp h𝔭 m).mpr hpm, mul_one, ← exp_nsmul]
  congr 1
  simp

/-- **`v_𝔭(z) = exp(−v_p(z))`** for a nonzero rational `z`, at `𝔭 ∣ p` unramified (PROVED). -/
theorem valued_iota_eq_exp (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p) (hu : UnramifiedOver 𝔭 p)
    (ι : ℚ →+* 𝔭.adicCompletion K) {z : ℚ} (hz : z ≠ 0) :
    Valued.v (ι z) = exp (-padicValRat p z) := by
  rw [valued_iota, valuation_ratCast, intValuation_intCast_eq_exp hp h𝔭 hu (Rat.num_ne_zero.mpr hz),
    intValuation_intCast_eq_exp hp h𝔭 hu (by exact_mod_cast z.den_ne_zero), ← exp_sub, padicValRat,
    padicValInt.of_nat]
  congr 1
  ring

end Valuation

section Transfer

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] {p : ℕ}
  {𝔭 : HeightOneSpectrum (𝓞 K)} {𝔮 : HeightOneSpectrum (𝓞 L)}

/-- **Membership of lifts of a rational in `𝔪ⁿ` agrees at unramified primes above `p`**
(PROVED). -/
theorem mem_pow_iff_of_rat (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p) (hu : UnramifiedOver 𝔭 p)
    (h𝔮 : 𝔮 ∈ primesAbove L p) (hu' : UnramifiedOver 𝔮 p) (ι : ℚ →+* 𝔭.adicCompletion K)
    (ι' : ℚ →+* 𝔮.adicCompletion L) {z : ℚ} {r : 𝔭.adicCompletionIntegers K}
    {r' : 𝔮.adicCompletionIntegers L} (hr : (r : 𝔭.adicCompletion K) = ι z)
    (hr' : (r' : 𝔮.adicCompletion L) = ι' z) (n : ℕ) :
    r ∈ IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) ^ n ↔
      r' ∈ IsLocalRing.maximalIdeal (𝔮.adicCompletionIntegers L) ^ n := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_maximalIdeal_pow_iff,
    IsDedekindDomain.HeightOneSpectrum.mem_maximalIdeal_pow_iff, hr, hr']
  by_cases hz : z = 0
  · simp [hz]
  · rw [valued_iota_eq_exp hp h𝔭 hu ι hz, valued_iota_eq_exp hp h𝔮 hu' ι' hz]

end Transfer

section Split

variable {k : Type*} [Field k] [Fintype k] {L : Type*} [Field L] [Fintype L]

/-- **A polynomial of degree `≤ 2` over `k` splits over a field with `|k|²` elements** (PROVED). -/
theorem splits_map_of_card_sq (ψ : k →+* L) (hL : Fintype.card L = Fintype.card k ^ 2)
    {f : k[X]} (hf : f.natDegree ≤ 2) : Splits (f.map ψ) := by
  classical
  by_cases hr : ∃ r, f.IsRoot r
  · obtain ⟨r, hr⟩ := hr
    have e := (mul_divByMonic_eq_iff_isRoot (p := f) (a := r)).mpr hr
    rw [← e, Polynomial.map_mul, Polynomial.map_sub, map_X, map_C]
    refine (Splits.X_sub_C _).mul (Splits.of_natDegree_le_one ?_)
    refine (natDegree_map_le).trans ?_
    rw [natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C]
    omega
  · simp only [not_exists] at hr
    by_cases h1 : f.natDegree ≤ 1
    · exact Splits.of_natDegree_le_one ((natDegree_map_le).trans h1)
    have hf0 : f ≠ 0 := by rintro rfl; simp at h1
    have hirr : Irreducible f :=
      irreducible_of_degree_le_three_of_not_isRoot (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) hr
    have : Fact (Irreducible f) := ⟨hirr⟩
    let pb := AdjoinRoot.powerBasis hf0
    have : Module.Finite k (AdjoinRoot f) := pb.finite
    have : Finite (AdjoinRoot f) := Module.finite_of_finite k
    let _ := Fintype.ofFinite (AdjoinRoot f)
    have hcard : Fintype.card (AdjoinRoot f) = Fintype.card k ^ 2 := by
      rw [Module.card_fintype pb.basis, Fintype.card_fin, AdjoinRoot.powerBasis_dim]
      congr 1; omega
    have hdvd : f ∣ X ^ Fintype.card L - X := by
      rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, hL, ← hcard,
        FiniteField.pow_card, sub_self]
    have hq : 1 < Fintype.card L := Fintype.one_lt_card
    have hg0 := FiniteField.X_pow_card_sub_X_ne_zero L hq
    refine Splits.of_dvd ?_ hg0 (by
      have := Polynomial.map_dvd ψ hdvd
      rwa [Polynomial.map_sub, Polynomial.map_pow, map_X] at this)
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq L hq]
    rfl

end Split

section Short

open WeierstrassCurve

variable {K : Type} [Field K] [NumberField K] {p : ℕ} {𝔭 : HeightOneSpectrum (𝓞 K)}

omit [NumberField K] in
/-- `p ∤ 2^a 3^b` for a prime `p ≥ 5` (PROVED). -/
theorem not_dvd_two_pow_mul_three_pow (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (a b : ℕ) :
    ¬ (p : ℤ) ∣ ((2 ^ a * 3 ^ b : ℕ) : ℤ) := by
  rw [Int.natCast_dvd_natCast]
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))

/-- `v(2^a 3^b) = 1` in `K_𝔭` for `𝔭 ∣ p ≥ 5` (PROVED). -/
theorem valued_two_pow_mul_three_pow (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (h𝔭 : 𝔭 ∈ primesAbove K p) (a b : ℕ) :
    Valued.v (((2 ^ a * 3 ^ b : ℕ) : 𝔭.adicCompletion K)) = 1 := by
  have h := (valued_iota_eq_one_iff hp h𝔭 (algebraMap ℚ (𝔭.adicCompletion K))
    ((2 ^ a * 3 ^ b : ℕ) : ℚ)).mpr ⟨by
      rw [Rat.num_natCast]; exact not_dvd_two_pow_mul_three_pow hp hp2 hp3 a b, by
      rw [Rat.den_natCast]; intro h1
      exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1)⟩
  rwa [map_natCast] at h

/-- **At `p ≥ 5`, a minimal model does not have both `v(Δ) ≥ 12` and `v(c₄) ≥ 4`** (the `p ≥ 5`
case of the classical valuation criterion for minimality): otherwise its short Weierstrass form
`y² = x³ − (c₄/48) x − c₆/864`, scaled by `p`, is integral with discriminant `Δ/p¹²`. PROVED. -/
theorem not_mem_pow_twelve_and_mem_pow_four (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (h𝔭 : 𝔭 ∈ primesAbove K p) (hu : UnramifiedOver 𝔭 p)
    (W : WeierstrassCurve (𝔭.adicCompletion K)) (hΔ : W.Δ ≠ 0)
    [hW : IsMinimal (𝔭.adicCompletionIntegers K) W] :
    ¬ ((integralModel (𝔭.adicCompletionIntegers K) W).Δ ∈
        IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) ^ 12 ∧
      (integralModel (𝔭.adicCompletionIntegers K) W).c₄ ∈
        IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) ^ 4) := by
  rintro ⟨hΔm, hcm⟩
  have vΔ : Valued.v W.Δ ≤ exp (-12) := by
    have := (IsDedekindDomain.HeightOneSpectrum.mem_maximalIdeal_pow_iff 𝔭).mp hΔm
    rwa [show (((integralModel (𝔭.adicCompletionIntegers K) W).Δ : 𝔭.adicCompletionIntegers K) :
      𝔭.adicCompletion K) = W.Δ from integralModel_Δ_eq (𝔭.adicCompletionIntegers K) W] at this
  have vc4 : Valued.v W.c₄ ≤ exp (-4) := by
    have := (IsDedekindDomain.HeightOneSpectrum.mem_maximalIdeal_pow_iff 𝔭).mp hcm
    rwa [show (((integralModel (𝔭.adicCompletionIntegers K) W).c₄ : 𝔭.adicCompletionIntegers K) :
      𝔭.adicCompletion K) = W.c₄ from integralModel_c₄_eq (𝔭.adicCompletionIntegers K) W] at this
  have v1728 : Valued.v (1728 : 𝔭.adicCompletion K) = 1 := by
    have := valued_two_pow_mul_three_pow hp hp2 hp3 h𝔭 6 3
    norm_num at this; exact this
  have v48 : Valued.v (48 : 𝔭.adicCompletion K) = 1 := by
    have := valued_two_pow_mul_three_pow hp hp2 hp3 h𝔭 4 1
    norm_num at this; exact this
  have v864 : Valued.v (864 : 𝔭.adicCompletion K) = 1 := by
    have := valued_two_pow_mul_three_pow hp hp2 hp3 h𝔭 5 3
    norm_num at this; exact this
  have vc6 : Valued.v W.c₆ ≤ exp (-6) := by
    have hsq : Valued.v W.c₆ ^ 2 ≤ exp (-12) := by
      have e : W.c₆ ^ 2 = W.c₄ ^ 3 - 1728 * W.Δ := by linear_combination W.c_relation
      rw [← map_pow, e]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
      · rw [map_pow]
        calc Valued.v W.c₄ ^ 3 ≤ exp (-4) ^ 3 := pow_le_pow_left₀ zero_le vc4 3
          _ = exp (-12) := by rw [← exp_nsmul]; rfl
      · rw [map_mul, v1728, one_mul]; exact vΔ
    by_contra h
    rw [not_le] at h
    have h2 := pow_lt_pow_left₀ h zero_le (two_ne_zero)
    rw [← exp_nsmul] at h2
    exact absurd hsq (not_le.mpr (by simpa using h2))
  have hp0 : (p : 𝔭.adicCompletion K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have : Fact p.Prime := ⟨hp⟩
  have vp : Valued.v (p : 𝔭.adicCompletion K) = exp (-1) := by
    have h := valued_iota_eq_exp hp h𝔭 hu (algebraMap ℚ (𝔭.adicCompletion K)) (z := (p : ℚ))
      (by exact_mod_cast hp.ne_zero)
    rwa [map_natCast, padicValRat.self hp.one_lt] at h
  -- the short form, scaled by `p`
  have : Invertible (2 : 𝔭.adicCompletion K) := invertibleOfNonzero two_ne_zero
  have : Invertible (3 : 𝔭.adicCompletion K) := invertibleOfNonzero three_ne_zero
  have hTu : W.toShortNF.u = 1 := by
    change (1 : (𝔭.adicCompletion K)ˣ) * 1 = 1
    exact mul_one 1
  have hW₁ : (W.toShortNF • W).IsShortNF := W.toShortNF_spec
  have hc4₁ : (W.toShortNF • W).c₄ = W.c₄ := by rw [variableChange_c₄, hTu]; simp
  have hc6₁ : (W.toShortNF • W).c₆ = W.c₆ := by rw [variableChange_c₆, hTu]; simp
  have hΔ₁ : (W.toShortNF • W).Δ = W.Δ := by rw [variableChange_Δ, hTu]; simp
  let S : VariableChange (𝔭.adicCompletion K) := ⟨Units.mk0 (p : 𝔭.adicCompletion K) hp0, 0, 0, 0⟩
  have va4 : Valued.v (W.toShortNF • W).a₄ ≤ exp (-4) := by
    have e := c₄_of_isShortNF (W.toShortNF • W)
    rw [hc4₁] at e
    have h : Valued.v W.c₄ = Valued.v (W.toShortNF • W).a₄ := by
      rw [e, Valuation.map_mul, Valuation.map_neg, v48, one_mul]
    rw [← h]; exact vc4
  have va6 : Valued.v (W.toShortNF • W).a₆ ≤ exp (-6) := by
    have e := c₆_of_isShortNF (W.toShortNF • W)
    rw [hc6₁] at e
    have h : Valued.v W.c₆ = Valued.v (W.toShortNF • W).a₆ := by
      rw [e, Valuation.map_mul, Valuation.map_neg, v864, one_mul]
    rw [← h]; exact vc6
  have vpinv : ∀ n : ℕ, Valued.v ((p : 𝔭.adicCompletion K)⁻¹ ^ n) = exp (n : ℤ) := by
    intro n; rw [map_pow, map_inv₀, vp, ← exp_neg, neg_neg, ← exp_nsmul]; simp
  have hSu : ((S.u⁻¹ : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K) = (p : 𝔭.adicCompletion K)⁻¹ := by
    rw [Units.val_inv_eq_inv_val]; rfl
  have e1 : (S • (W.toShortNF • W)).a₁ = 0 := by
    rw [variableChange_a₁, hW₁.a₁]; simp [S]
  have e2 : (S • (W.toShortNF • W)).a₂ = 0 := by
    rw [variableChange_a₂, hW₁.a₁, hW₁.a₂]; simp [S]
  have e3 : (S • (W.toShortNF • W)).a₃ = 0 := by
    rw [variableChange_a₃, hW₁.a₁, hW₁.a₃]; simp [S]
  have e4 : (S • (W.toShortNF • W)).a₄ = (p : 𝔭.adicCompletion K)⁻¹ ^ 4 * (W.toShortNF • W).a₄ := by
    rw [variableChange_a₄, hSu, hW₁.a₁, hW₁.a₂, hW₁.a₃]
    change _ * (_ - 0 * 0 + 2 * 0 * 0 - (0 + 0 * 0) * 0 + 3 * 0 ^ 2 - 2 * 0 * 0) = _
    ring
  have e6 : (S • (W.toShortNF • W)).a₆ = (p : 𝔭.adicCompletion K)⁻¹ ^ 6 * (W.toShortNF • W).a₆ := by
    rw [variableChange_a₆, hSu, hW₁.a₁, hW₁.a₂, hW₁.a₃]
    change _ * (_ + 0 * _ + 0 ^ 2 * 0 + 0 ^ 3 - 0 * 0 - 0 ^ 2 - 0 * 0 * 0) = _
    ring
  have hm4 : (p : 𝔭.adicCompletion K)⁻¹ ^ 4 * (W.toShortNF • W).a₄ ∈ 𝔭.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers, Valuation.map_mul, vpinv]
    calc exp ((4 : ℕ) : ℤ) * Valued.v (W.toShortNF • W).a₄ ≤ exp ((4 : ℕ) : ℤ) * exp (-4) := by
          gcongr
      _ = 1 := by rw [← exp_add]; simp
  have hm6 : (p : 𝔭.adicCompletion K)⁻¹ ^ 6 * (W.toShortNF • W).a₆ ∈ 𝔭.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers, Valuation.map_mul, vpinv]
    calc exp ((6 : ℕ) : ℤ) * Valued.v (W.toShortNF • W).a₆ ≤ exp ((6 : ℕ) : ℤ) * exp (-6) := by
          gcongr
      _ = 1 := by rw [← exp_add]; simp
  have hint : IsIntegral (𝔭.adicCompletionIntegers K) ((S * W.toShortNF) • W) := by
    rw [mul_smul]
    exact isIntegral_of_exists_lift _ ⟨0, by rw [e1]; simp⟩ ⟨0, by rw [e2]; simp⟩
      ⟨0, by rw [e3]; simp⟩ ⟨⟨_, hm4⟩, e4.symm⟩ ⟨⟨_, hm6⟩, e6.symm⟩
  have hmin := ((isMinimal_iff_forall (𝔭.adicCompletionIntegers K) W).mp hW).2 _ hint
  have hSTΔ : ((S * W.toShortNF) • W).Δ = (p : 𝔭.adicCompletion K)⁻¹ ^ 12 * W.Δ := by
    rw [mul_smul, variableChange_Δ, hSu, hΔ₁]
  rw [hSTΔ, map_mul] at hmin
  -- `p ∈ 𝔪`, so `v(p⁻¹) > 1`
  have hpm : ((p : 𝔭.adicCompletionIntegers K)) ∈
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) := by
    have := charP_residueField hp h𝔭
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
  have hvp : valuation (𝔭.adicCompletion K)
      (IsDiscreteValuationRing.maximalIdeal (𝔭.adicCompletionIntegers K)) (p : 𝔭.adicCompletion K)
        < 1 := by
    have h := (valuation_lt_one_iff_mem (K := 𝔭.adicCompletion K)
      (IsDiscreteValuationRing.maximalIdeal (𝔭.adicCompletionIntegers K))
      (p : 𝔭.adicCompletionIntegers K)).mpr hpm
    convert h using 2
    rfl
  have hvΔ : valuation (𝔭.adicCompletion K)
      (IsDiscreteValuationRing.maximalIdeal (𝔭.adicCompletionIntegers K)) W.Δ ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hΔ
  have hgt : 1 < valuation (𝔭.adicCompletion K)
      (IsDiscreteValuationRing.maximalIdeal (𝔭.adicCompletionIntegers K))
        ((p : 𝔭.adicCompletion K)⁻¹ ^ 12) := by
    rw [map_pow, map_inv₀]
    exact one_lt_pow₀ ((one_lt_inv₀ ((Valuation.pos_iff _).mpr hp0)).mpr hvp) (by norm_num)
  exact absurd hmin (not_le.mpr (lt_mul_of_one_lt_left (zero_lt_iff.mpr hvΔ) hgt))

end Short

end ZInQ.Contrib.CloudB3RC53.GenusOdd
