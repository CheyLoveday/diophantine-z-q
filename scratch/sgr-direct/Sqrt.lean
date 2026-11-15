import ZInQKernel.Contrib.OneProof.SGRDirectNV

set_option linter.style.haveILetI false

noncomputable section

open Polynomial GlueDescent.B2Q NumberField
open HDec HDec.G0ModField HDec.PropTSRed LeafQM.AV

namespace SGRDirect

/-- A nonzero rational of `p`-adic valuation `0` has numerator and denominator prime to `p`. -/
theorem not_dvd_num_den_of_padicValRat_eq_zero (p : ℕ) [hp : Fact p.Prime] {u : ℚ} (hu : u ≠ 0)
    (h : padicValRat p u = 0) : ¬ (p : ℤ) ∣ u.num ∧ ¬ p ∣ u.den := by
  have hnum : u.num ≠ 0 := Rat.num_ne_zero.mpr hu
  have hcop : u.num.natAbs.Coprime u.den := u.reduced
  rw [padicValRat_def] at h
  constructor
  · intro hn
    have h1 : p ∣ u.num.natAbs := Int.natCast_dvd.mp hn
    have hd : ¬ p ∣ u.den := fun hd =>
      (Nat.Prime.coprime_iff_not_dvd hp.out).mp (Nat.Coprime.coprime_dvd_left h1 hcop) hd
    have hv1 : padicValNat p u.den = 0 := padicValNat.eq_zero_of_not_dvd hd
    have hv2 : 1 ≤ padicValNat p u.num.natAbs :=
      one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hnum) h1
    rw [padicValInt, hv1] at h
    omega
  · intro hd
    have hn : ¬ p ∣ u.num.natAbs := fun h1 =>
      (Nat.Prime.coprime_iff_not_dvd hp.out).mp (Nat.Coprime.coprime_dvd_left h1 hcop) hd
    have hv1 : padicValNat p u.num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hn
    have hv2 : 1 ≤ padicValNat p u.den := one_le_padicValNat_of_dvd u.den_nz hd
    rw [padicValInt, hv1] at h
    omega

/-- **A square root of `q ∈ ℚ` in a number field unramified at `p` forces `v_p(q)` even.** -/
theorem even_padicValRat_of_sq_mem (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L] (p : ℕ)
    (hp : p.Prime) (hL : UnramifiedAt L p) (q : ℚ) (hq : q ≠ 0) (β : Qbar) (hβ : β ∈ L)
    (hsq : β ^ 2 = algebraMap ℚ Qbar q) : Even (padicValRat p q) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hodd
  rw [Int.not_even_iff_odd] at hodd
  obtain ⟨k, hk⟩ := hodd
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp0' : (p : Qbar) ≠ 0 := by exact_mod_cast hp.ne_zero
  set u : ℚ := q * (p : ℚ) ^ (-(2 * k + 1)) with hu
  have hu0 : u ≠ 0 := mul_ne_zero hq (zpow_ne_zero _ hp0)
  have hvu : padicValRat p u = 0 := by
    rw [hu, padicValRat.mul hq (zpow_ne_zero _ hp0), padicValRat.zpow _ (k := -(2 * k + 1)),
      padicValRat.self hp.one_lt, hk]
    ring
  obtain ⟨hnum, hden⟩ := not_dvd_num_den_of_padicValRat_eq_zero p hu0 hvu
  set γ : Qbar := (u.den : Qbar) * β * (p : Qbar) ^ (-k) with hγdef
  have hγL : γ ∈ L :=
    L.mul_mem (L.mul_mem (L.algebraMap_mem (u.den : ℚ)) hβ) (zpow_mem (L.algebraMap_mem (p : ℚ)) _)
  have hqu : algebraMap ℚ Qbar q = algebraMap ℚ Qbar u * (p : Qbar) ^ (2 * k + 1) := by
    rw [hu, map_mul, map_zpow₀, map_natCast, mul_assoc, ← zpow_add₀ hp0']
    simp
  have hud : (u.den : Qbar) * algebraMap ℚ Qbar u = (u.num : Qbar) := by
    have h := Rat.mul_den_eq_num u
    have := congrArg (algebraMap ℚ Qbar) h
    rw [map_mul, map_natCast, map_intCast] at this
    rw [mul_comm]; exact this
  have hγsq : γ ^ 2 = ((u.den * u.num * p : ℤ) : Qbar) := by
    rw [hγdef, mul_pow, mul_pow, hsq, hqu]
    push_cast
    rw [← zpow_natCast ((p : Qbar) ^ (-k)) 2, ← zpow_mul]
    have e : (u.den : Qbar) ^ 2 * (algebraMap ℚ Qbar u * (p : Qbar) ^ (2 * k + 1)) *
        (p : Qbar) ^ (-k * ((2 : ℕ) : ℤ)) =
        ((u.den : Qbar) * algebraMap ℚ Qbar u) * u.den * ((p : Qbar) ^ (2 * k + 1) *
          (p : Qbar) ^ (-k * ((2 : ℕ) : ℤ))) := by ring
    rw [e, hud, ← zpow_add₀ hp0']
    have e2 : 2 * k + 1 + -k * ((2 : ℕ) : ℤ) = 1 := by push_cast; ring
    rw [e2, zpow_one]
    ring
  -- the integral element `γ` and a prime of `𝓞 L` over `p`
  letI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  set N : ℤ := u.den * u.num * p with hN
  have hγsqL : (⟨γ, hγL⟩ : L) ^ 2 = (N : L) := Subtype.ext (by
    rw [IntermediateField.coe_pow]
    rw [hγsq]
    rfl)
  have hintγ : IsIntegral ℤ (⟨γ, hγL⟩ : L) := by
    refine ⟨X ^ 2 - Polynomial.C N, monic_X_pow_sub_C _ (by norm_num), ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hγsqL, sub_eq_zero]
    simp
  set γL : 𝓞 L := ⟨⟨γ, hγL⟩, hintγ⟩ with hγLdef
  have hγLsq : γL ^ 2 = (N : 𝓞 L) := by
    apply RingOfIntegers.coe_injective
    push_cast
    show (⟨γ, hγL⟩ : L) ^ 2 = _
    rw [hγsqL, map_intCast]
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨P, hP, hPu⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L)
    (Ideal.span {(p : ℤ)}) (by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have : (x : 𝓞 L) = 0 := by simpa using hx
      have hx0 : x = 0 := by exact_mod_cast this
      rw [hx0]; exact Ideal.zero_mem _)
  have hpP : ((p : ℤ) : 𝓞 L) ∈ P := by
    have h1 : (p : ℤ) ∈ P.under ℤ := by rw [hPu]; exact Ideal.mem_span_singleton_self _
    simpa using h1
  have he := hL P hP hpP
  have hγP : γL ∈ P := by
    apply hP.mem_of_pow_mem 2
    rw [hγLsq, hN]
    push_cast
    exact P.mul_mem_left _ hpP
  have hsqP : ((p : ℤ) : 𝓞 L) * ((u.den * u.num : ℤ) : 𝓞 L) ∈ P ^ 2 := by
    have h2 : γL ^ 2 ∈ P ^ 2 := Ideal.pow_mem_pow hγP 2
    rw [hγLsq, hN] at h2
    push_cast at h2 ⊢
    convert h2 using 1
    ring
  have hP0 : P ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpP
    have : ((p : ℤ) : 𝓞 L) ≠ 0 := by exact_mod_cast hp.ne_zero
    exact this hpP
  have hPmax : P.IsMaximal := hP.isMaximal hP0
  have hrad : (P ^ 2).radical = P := by rw [Ideal.radical_pow P two_ne_zero, hP.radical]
  have hprim : (P ^ 2).IsPrimary := Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; exact hPmax)
  rcases (Ideal.isPrimary_iff.mp hprim).2 hsqP with h | h
  · -- `p ∈ P²` contradicts `e(P | p) = 1`
    have hle : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≤ P ^ 2 := by
      rw [Ideal.map_span, Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]
      simpa using h
    haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPu.symm⟩
    have hsp0 : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
    have he' := Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hsp0
    rw [he] at he'
    have h2mem : 2 ∈ {n | Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≤ P ^ n} := hle
    by_cases hbdd : BddAbove {n | Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≤ P ^ n}
    · have := le_csSup hbdd h2mem
      rw [Ideal.ramificationIdx'] at he'
      omega
    · rw [Ideal.ramificationIdx', Nat.sSup_of_not_bddAbove hbdd] at he'
      exact zero_ne_one he'
  · rw [hrad] at h
    have h1 : (u.den * u.num : ℤ) ∈ P.under ℤ := by simpa using h
    rw [hPu, Ideal.mem_span_singleton] at h1
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h1 with h2 | h2
    · exact hden (by exact_mod_cast h2)
    · exact hnum h2

end SGRDirect

#print axioms SGRDirect.even_padicValRat_of_sq_mem
