import ZInQKernel.Contrib.G9.KerTheta

/-! # derham-print: `t = log[ε]` in the kernel's `B_dR^+`, and `B_dR^+[1/t] ≅ B_dR` (development file) -/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace DeRhamPrint.TDict

open Ideal WittVector ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4.Cp ZInQ.Contrib.G9.BdrKer
  ZInQ.Contrib.G9.BdrKer.Cp

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

local notation "O" => (𝓞_ℂ_[p] : Type)

/-! ## 1. Elements of the tilt from compatible sequences -/

/-- `(z₀, z₁, …) ∈ O♭` for a sequence with `z (n+1) ^ p = z n` in `O`. -/
def mkSeq (z : ℕ → O) (hz : ∀ n, z (n + 1) ^ p = z n) : PreTilt O p :=
  ⟨fun n => Ideal.Quotient.mk _ (z n), fun n => by rw [← map_pow, hz]⟩

theorem coeff_mkSeq (z : ℕ → O) (hz : ∀ n, z (n + 1) ^ p = z n) (n : ℕ) :
    PreTilt.coeff n (mkSeq p z hz) = Ideal.Quotient.mk _ (z n) := rfl

theorem pow_seq (z : ℕ → O) (hz : ∀ n, z (n + 1) ^ p = z n) (n : ℕ) : z n ^ p ^ n = z 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, hz, ih]

theorem untilt_mkSeq (z : ℕ → O) (hz : ∀ n, z (n + 1) ^ p = z n) : (mkSeq p z hz).untilt = z 0 := by
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : O)})]
  intro n
  rw [SModEq.sub_mem, mem_span_pow_iff']
  have h1 : root (mkSeq p z hz) n - z n ∈ span {(p : O)} := by
    rw [← Ideal.Quotient.eq, mk_root]; rfl
  have h2 := dvd_sub_pow_of_dvd_sub (Ideal.mem_span_singleton.mp h1) n
  rw [root_pow, pow_seq p z hz] at h2
  obtain ⟨c, hc⟩ := h2
  exact ⟨p * c, by rw [hc]; ring⟩

/-! ## 2. Divisibility in the tilt by comparing absolute values of untilts -/

/-- If `‖c♯‖ ≤ ‖a♯‖` and `a♯ ≠ 0`, then `a ∣ c` in `O♭` (bdr-kertheta's `dvd_of_coeff_zero`, with `p♭`
replaced by any `a`). -/
theorem dvd_of_norm_le (a c : PreTilt O p) (ha : ((a.untilt : O) : ℂ_[p]) ≠ 0)
    (hle : ‖((c.untilt : O) : ℂ_[p])‖ ≤ ‖((a.untilt : O) : ℂ_[p])‖) : ∃ d, c = a * d := by
  have han : ∀ n, ‖((root a n : O) : ℂ_[p])‖ ^ p ^ n = ‖((a.untilt : O) : ℂ_[p])‖ := fun n => by
    have h := congrArg (fun z : O => ‖(z : ℂ_[p])‖) (root_pow a n)
    simpa [norm_pow] using h
  have hcn : ∀ n, ‖((root c n : O) : ℂ_[p])‖ ^ p ^ n = ‖((c.untilt : O) : ℂ_[p])‖ := fun n => by
    have h := congrArg (fun z : O => ‖(z : ℂ_[p])‖) (root_pow c n)
    simpa [norm_pow] using h
  have hne : ∀ n, ((root a n : O) : ℂ_[p]) ≠ 0 := fun n h0 => by
    have := han n
    rw [h0, norm_zero, zero_pow (pow_ne_zero _ hp.out.ne_zero)] at this
    exact ha (norm_eq_zero.mp this.symm)
  have hle' : ∀ n, ‖((root c n : O) : ℂ_[p])‖ ≤ ‖((root a n : O) : ℂ_[p])‖ := fun n => by
    have hpn : p ^ n ≠ 0 := pow_ne_zero _ hp.out.ne_zero
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hpn).mp ?_
    rw [hcn, han]; exact hle
  let e : ℕ → O := fun n => ⟨((root c n : O) : ℂ_[p]) / ((root a n : O) : ℂ_[p]),
    (mem_O_iff p _).mpr (by
      rw [norm_div]; exact div_le_one_of_le₀ (hle' n) (norm_nonneg _))⟩
  have he : ∀ n, e (n + 1) ^ p = e n := fun n => by
    apply Subtype.ext
    simp only [e, SubmonoidClass.coe_pow, div_pow]
    rw [← SubmonoidClass.coe_pow, ← SubmonoidClass.coe_pow, root_succ_pow, root_succ_pow]
  have hce : ∀ n, root c n = root a n * e n := fun n => by
    apply Subtype.ext
    simp only [e, MulMemClass.coe_mul]
    field_simp [hne n]
  let d : PreTilt O p := ⟨fun n => Ideal.Quotient.mk _ (e n), fun n => by
    rw [← map_pow, he]⟩
  refine ⟨d, ?_⟩
  apply Perfection.ext
  intro n
  change PreTilt.coeff n c = PreTilt.coeff n (a * d)
  rw [map_mul]
  change PreTilt.coeff n c = PreTilt.coeff n a * Ideal.Quotient.mk _ (e n)
  rw [← mk_root, ← mk_root, ← map_mul, hce]

/-! ## 3. A system of `p`-power roots of unity, and `‖ζ_{p²} - 1‖^{p(p-1)} ≥ ‖p‖` -/

/-- A compatible system `ζ₀ = 1, ζ₁ ≠ 1, ζ_{n+1}^p = ζ_n` of `p`-power roots of unity in `𝓞_ℂ_p`. -/
structure RootSystem where
  z : ℕ → O
  pow_succ : ∀ n, z (n + 1) ^ p = z n
  zero : z 0 = 1
  one_ne : z 1 ≠ 1

variable {p}

theorem norm_one_sub_pow_le (ζ : O) (k : ℕ) :
    ‖(1 : ℂ_[p]) - (ζ : ℂ_[p]) ^ k‖ ≤ ‖(1 : ℂ_[p]) - (ζ : ℂ_[p])‖ := by
  have h : (1 : O) - ζ ^ k = (1 - ζ) * ∑ i ∈ Finset.range k, ζ ^ i := (mul_neg_geom_sum ζ k).symm
  have h' := congrArg (fun z : O => ‖(z : ℂ_[p])‖) h
  simp only [MulMemClass.coe_mul] at h'
  push_cast at h'
  rw [h', norm_mul]
  have hs := norm_le_one p (∑ i ∈ Finset.range k, ζ ^ i)
  push_cast at hs
  calc ‖(1 : ℂ_[p]) - ζ‖ * ‖∑ i ∈ Finset.range k, (ζ : ℂ_[p]) ^ i‖ ≤ ‖(1 : ℂ_[p]) - ζ‖ * 1 :=
        mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ = _ := mul_one _

theorem isPrimitiveRoot_z2 (Z : RootSystem p) : IsPrimitiveRoot ((Z.z 2 : O) : ℂ_[p]) (p ^ 2) := by
  have h1 : ((Z.z 2 : O) : ℂ_[p]) ^ p ^ 1 ≠ 1 := by
    intro h
    apply Z.one_ne
    apply Subtype.ext
    rw [pow_one] at h
    rw [← Z.pow_succ 1]
    push_cast
    exact h
  have h2 : ((Z.z 2 : O) : ℂ_[p]) ^ p ^ (1 + 1) = 1 := by
    have := pow_seq p Z.z Z.pow_succ 2
    rw [Z.zero] at this
    have := congrArg (fun z : O => (z : ℂ_[p])) this
    simpa using this
  have := orderOf_eq_prime_pow h1 h2
  rw [← this]
  exact IsPrimitiveRoot.orderOf _

theorem norm_p_le (Z : RootSystem p) :
    ‖(p : ℂ_[p])‖ ≤ ‖(1 : ℂ_[p]) - ((Z.z 2 : O) : ℂ_[p])‖ ^ (p * (p - 1)) := by
  set ζ : ℂ_[p] := ((Z.z 2 : O) : ℂ_[p])
  have hprim := isPrimitiveRoot_z2 Z
  have hev : Polynomial.eval 1 (Polynomial.cyclotomic (p ^ (1 + 1)) ℂ_[p]) = p :=
    Polynomial.eval_one_cyclotomic_prime_pow 1
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hprim, Polynomial.eval_prod] at hev
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hev
  rw [← hev, norm_prod]
  have hcard : (primitiveRoots (p ^ 2) ℂ_[p]).card = p * (p - 1) := by
    rw [hprim.card_primitiveRoots, Nat.totient_prime_pow hp.out (by norm_num)]
    simp
  rw [← hcard, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun μ hμ => ?_
  have hp2 : 0 < p ^ 2 := pow_pos hp.out.pos 2
  have : NeZero (p ^ 2) := ⟨hp2.ne'⟩
  have hμ' : μ ^ p ^ 2 = 1 := ((mem_primitiveRoots hp2).mp hμ).pow_eq_one
  obtain ⟨i, -, rfl⟩ := hprim.eq_pow_of_pow_eq_one hμ'
  exact norm_one_sub_pow_le (Z.z 2) i


/-! ## 4. `ε`, `ε^{1/p}` and `ω = Σ_{i<p} [ε^{1/p}]^i` -/

variable (Z : RootSystem p)

/-- `ε = (1, ζ_p, ζ_{p²}, …) ∈ O♭`. -/
def eps : PreTilt O p := mkSeq p Z.z Z.pow_succ

/-- `ε^{1/p} = (ζ_p, ζ_{p²}, …) ∈ O♭`. -/
def eps1 : PreTilt O p := mkSeq p (fun n => Z.z (n + 1)) (fun n => Z.pow_succ (n + 1))

theorem untilt_eps : (eps Z).untilt = 1 := by rw [eps, untilt_mkSeq, Z.zero]

theorem untilt_eps1 : (eps1 Z).untilt = Z.z 1 := untilt_mkSeq _ _ _

theorem eps1_pow : eps1 Z ^ p = eps Z := by
  apply Perfection.ext
  intro n
  change PreTilt.coeff n (eps1 Z ^ p) = PreTilt.coeff n (eps Z)
  rw [map_pow, eps1, eps, coeff_mkSeq, coeff_mkSeq, ← map_pow, Z.pow_succ]

theorem eps1_sub_one_ne_zero : eps1 Z - 1 ≠ 0 := by
  intro h
  have h1 : eps1 Z = 1 := sub_eq_zero.mp h
  have h2 := congrArg PreTilt.untilt h1
  rw [untilt_eps1, map_one] at h2
  exact Z.one_ne h2

theorem geom_eq (e : PreTilt O p) (he : e - 1 ≠ 0) :
    ∑ i ∈ Finset.range p, e ^ i = (e - 1) ^ (p - 1) := by
  have h1 : (∑ i ∈ Finset.range p, e ^ i) * (e - 1) = (e - 1) ^ (p - 1) * (e - 1) := by
    rw [geom_sum_mul, ← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, sub_pow_char, one_pow]
  exact mul_right_cancel₀ he h1

theorem sum_z1_eq_zero : ∑ i ∈ Finset.range p, Z.z 1 ^ i = 0 := by
  have h : (∑ i ∈ Finset.range p, Z.z 1 ^ i) * (Z.z 1 - 1) = 0 := by
    rw [geom_sum_mul, Z.pow_succ 0, Z.zero, sub_self]
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr Z.one_ne)

/-- `‖(ε^{1/p} - 1)♯‖^{p-1} ≥ ‖p‖`. -/
theorem norm_untilt_pow_ge :
    ‖(p : ℂ_[p])‖ ≤ ‖(((eps1 Z - 1) ^ (p - 1)).untilt : ℂ_[p])‖ := by
  set y := eps1 Z - 1
  set r := ‖((Z.z 2 : O) : ℂ_[p]) - 1‖
  have hr : ‖(p : ℂ_[p])‖ ≤ r ^ (p * (p - 1)) := by
    have := norm_p_le Z
    rwa [norm_sub_rev] at this
  have hp1 := norm_p_lt_one p
  have hp0 := norm_p_pos p
  have hrp : ‖(p : ℂ_[p])‖ < r := by
    by_contra hcon
    push Not at hcon
    have h2 : 1 < p * (p - 1) := by
      have := hp.out.two_le
      have h3 : 1 ≤ p - 1 := by omega
      nlinarith
    have := pow_lt_self_of_lt_one₀ hp0 hp1 h2
    have h4 : r ^ (p * (p - 1)) ≤ ‖(p : ℂ_[p])‖ ^ (p * (p - 1)) :=
      pow_le_pow_left₀ (norm_nonneg _) hcon _
    linarith
  -- `root y 1 ≡ ζ_{p²} - 1 (mod p)`
  have hmem : root y 1 - (Z.z 2 - 1) ∈ span {(p : O)} := by
    rw [← Ideal.Quotient.eq, mk_root, map_sub, map_sub, map_one, eps1, coeff_mkSeq, map_one]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hdiff : ‖((root y 1 - (Z.z 2 - 1) : O) : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ := by
    rw [← hc]
    push_cast
    rw [norm_mul]
    have := norm_le_one p c
    nlinarith [norm_nonneg ((c : O) : ℂ_[p]), norm_nonneg (p : ℂ_[p])]
  have hroot : r ≤ ‖((root y 1 : O) : ℂ_[p])‖ := by
    have h1 : ((Z.z 2 : O) : ℂ_[p]) - 1 =
        ((root y 1 : O) : ℂ_[p]) - ((root y 1 - (Z.z 2 - 1) : O) : ℂ_[p]) := by
      push_cast; ring
    have h2 := IsUltrametricDist.norm_add_le_max ((root y 1 : O) : ℂ_[p])
      (-((root y 1 - (Z.z 2 - 1) : O) : ℂ_[p]))
    rw [norm_neg, ← sub_eq_add_neg, ← h1] at h2
    rcases le_max_iff.mp h2 with h | h
    · exact h
    · linarith
  have hy : ‖((y.untilt : O) : ℂ_[p])‖ = ‖((root y 1 : O) : ℂ_[p])‖ ^ p := by
    rw [← root_pow y 1, pow_one]; push_cast; rw [norm_pow]
  rw [map_pow]
  push_cast
  rw [norm_pow, hy, ← pow_mul]
  calc ‖(p : ℂ_[p])‖ ≤ r ^ (p * (p - 1)) := hr
    _ ≤ _ := pow_le_pow_left₀ (le_trans (norm_nonneg _) hrp.le) hroot _

/-- `p♭ = (ε^{1/p} - 1)^{p-1} · d` in `O♭`. -/
theorem pFlat_dvd : ∃ d, pFlat p = (eps1 Z - 1) ^ (p - 1) * d := by
  apply dvd_of_norm_le
  · intro h0
    have := norm_untilt_pow_ge Z
    rw [h0, norm_zero] at this
    linarith [norm_p_pos p]
  · rw [untilt_pFlat]
    exact norm_untilt_pow_ge Z

local notation "W" => WittVector p (PreTilt O p)

/-- `ω = Σ_{i<p} [ε^{1/p}]^i ∈ W(O♭)`. -/
def omega : W := ∑ i ∈ Finset.range p, teichmuller p (eps1 Z) ^ i

theorem theta_omega : fontaineTheta O p (omega Z) = 0 := by
  rw [omega, map_sum]
  simp only [map_pow, fontaineTheta_teichmuller, untilt_eps1]
  exact sum_z1_eq_zero Z

/-- **`ker θ = (ω)`** in `W(O♭)` (Fontaine's generator `ω = ([ε] - 1)/([ε^{1/p}] - 1)`). -/
theorem ker_theta_eq_omega : RingHom.ker (fontaineTheta O p) = span {omega Z} := by
  apply ker_eq_span_of_mod_p p (fontaineTheta O p) (p_regular p) (omega Z) (theta_omega Z)
  intro x hx
  have hx' : x ∈ span {xi p} := by rw [← ker_fontaineTheta_Cp p]; exact hx
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx'
  obtain ⟨d, hd⟩ := pFlat_dvd Z
  have hmem : teichmuller p ((eps1 Z - 1) ^ (p - 1)) - omega Z ∈ span {(p : W)} := by
    have hc : ∀ e : PreTilt O p, constantCoeff (teichmuller p e) = e := fun e => by simp
    rw [← ker_constantCoeff, RingHom.mem_ker, map_sub, omega, map_sum, hc]
    simp only [map_pow, hc]
    rw [geom_eq (eps1 Z) (eps1_sub_one_ne_zero Z), sub_self]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨-(y * teichmuller p d), y - y * w * teichmuller p d, ?_⟩
  rw [xi, hd, map_mul]
  linear_combination (y * teichmuller p d) * hw

theorem xi_mem_span_omega : ∃ v, v * omega Z = xi p := by
  have : xi p ∈ span {omega Z} := by
    rw [← ker_theta_eq_omega Z, ker_fontaineTheta_Cp p]
    exact Ideal.mem_span_singleton_self _
  exact Ideal.mem_span_singleton'.mp this

end

end DeRhamPrint.TDict
