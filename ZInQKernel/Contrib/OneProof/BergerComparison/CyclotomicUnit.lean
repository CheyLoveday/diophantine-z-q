import ZInQKernel.Contrib.OneProof.BergerComparison.ResidueLog

/-! A cyclotomic unit normalization valid also at p = 2. Work at the
second cyclotomic root, where the error modulo p is strictly smaller
than the norm of the root minus one. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst BmaxOne
open ZInQ.Contrib.G9.BdrKer.Cp
open IsUltrametricDist

variable (p : ℕ) [hp : Fact p.Prime]
local notation "O" => (𝓞_ℂ_[p] : Type)
local notation "Cₚ" => (ℂ_[p] : Type)
local notation "T" => (PreTilt O p)
local notation "q" => ‖(p : Cₚ)‖

set_option maxHeartbeats 800000

private theorem p_dvd_of_norm (z : O) (hz : ‖(z : Cₚ)‖ ≤ q) : (p : O) ∣ z := by
  rw [← Ideal.mem_span_singleton, ← pow_one (Ideal.span {(p : O)})]
  apply (HDec.PkgI4.Cp.mem_span_pow_iff p z 1).mpr
  simpa only [pow_one] using hz

private theorem norm_sub_of_p_dvd {x y : O} (h : (p : O) ∣ x - y) :
    ‖(x : Cₚ) - (y : Cₚ)‖ ≤ q := by
  rw [← Ideal.mem_span_singleton, ← pow_one (Ideal.span {(p : O)})] at h
  have hx := (HDec.PkgI4.Cp.mem_span_pow_iff p (x - y) 1).mp h
  rw [pow_one] at hx
  exact hx

private theorem norm_lt_one_of_close {x y : Cₚ} (h : ‖x - y‖ < 1) (hy : ‖y‖ < 1) :
    ‖x‖ < 1 := by
  simpa only [sub_add_cancel] using
    (norm_add_le_max (x - y) y).trans_lt (max_lt h hy)

private theorem norm_eq_of_close {x y : Cₚ} (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  have hxy : (x - y) + y = x := sub_add_cancel x y
  rw [← hxy, norm_add_eq_max_of_norm_ne_norm h.ne, max_eq_right h.le]

/-- The middle terms of the prime-power expansion are p times the
argument, with coefficient 1 in degree one. -/
private theorem prime_binomial (z : O) :
    ∃ b : O, (1 + z)^p = 1 + z^p + (p : O) * z * (1 + z * b) := by
  classical
  let d (i : ℕ) := p.choose (i + 2) / p
  let b : O := ∑ i ∈ Finset.range (p - 2), (d i : O) * z^i
  have hsum :
      (1 + z)^p = 1 + (p : O) * z +
        (∑ i ∈ Finset.range (p - 2), z ^ (i + 2) * (p.choose (i + 2) : O)) + z^p := by
    rw [add_comm 1 z, add_pow, Finset.sum_range_succ]
    simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one]
    have hs : (∑ i ∈ Finset.range p, z^i * (p.choose i : O)) =
        1 + p*z + ∑ i ∈ Finset.range (p-2), z^(i+2) * (p.choose (i+2) : O) := by
      conv_lhs =>
        enter [1]
        rw [show p = (p-2+1)+1 by have := hp.out.two_le; omega]
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [Nat.zero_add, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
        pow_one, Nat.choose_one_right]
      ring
    rw [hs]
  have he :
      (∑ i ∈ Finset.range (p - 2), z ^ (i + 2) * (p.choose (i + 2) : O)) =
        ((p : O) * z * z) * b := by
    dsimp only [b]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hd := Nat.mul_div_cancel' (hp.out.dvd_choose_self (show i + 2 ≠ 0 by omega)
      (by simpa only [Finset.mem_range] using (show i + 2 < p by
        have := Finset.mem_range.mp hi; omega)))
    have hcast : (p.choose (i + 2) : O) = (p : O) * (d i : O) := by
      exact_mod_cast hd.symm
    rw [hcast, pow_add, pow_two]
    ring
  exact ⟨b, by rw [hsum, he]; ring⟩

private theorem norm_pow_sub_lt {x y : Cₚ} {c : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) (hc : 0 < c)
    (hd : ‖x - y‖ ≤ c) : ‖x^n - y^n‖ < c := by
  rw [← (Commute.all x y).mul_geom_sum₂, norm_mul]
  have hsum : ‖∑ i ∈ Finset.range n, x^i * y^(n - 1 - i)‖ < 1 := by
    obtain ⟨i, _, hs⟩ := (isNonarchimedean_norm (R := Cₚ)).finset_image_add_of_nonempty
      (g := fun i => x^i * y^(n - 1 - i)) (Finset.nonempty_range_iff.mpr (by omega : n ≠ 0))
    apply hs.trans_lt
    rw [norm_mul, norm_pow, norm_pow]
    have h₂ : ‖y‖ ^ (n - 1 - i) ≤ 1 := pow_le_one₀ (norm_nonneg _) hy.le
    by_cases h : i = 0
    · rw [h, pow_zero, one_mul]
      exact pow_lt_one₀ (norm_nonneg _) hy (by omega)
    · exact (mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) h₂).trans_lt
        (pow_lt_one₀ (norm_nonneg _) hx h)
  calc
    _ ≤ c * ‖∑ i ∈ Finset.range n, x^i * y^(n - 1 - i)‖ :=
      mul_le_mul_of_nonneg_right hd (norm_nonneg _)
    _ < c := by simpa only [mul_one] using mul_lt_mul_of_pos_left hsum hc

private theorem near_p_root (w : O) (hw : w ≠ 0) (h : (1 + w)^p = 1) :
    ∃ b : O, w^(p - 1) = -(p : O) * (1 + w*b) ∧ ‖(w : Cₚ)‖ < 1 := by
  obtain ⟨b, hb⟩ := prime_binomial p w
  rw [h] at hb
  have hp' := Nat.sub_add_cancel hp.out.one_le
  have hw' : w^(p - 1) = -(p : O) * (1 + w*b) := by
    apply mul_right_cancel₀ hw
    rw [← pow_succ, hp']
    linear_combination -hb
  have hd : (p : O) ∣ w^p := ⟨-(w * (1 + w*b)), by linear_combination -hb⟩
  have hn := norm_sub_of_p_dvd p (x := w^p) (y := 0) (by simpa only [sub_zero] using hd)
  simp only [SubmonoidClass.coe_pow, ZeroMemClass.coe_zero, sub_zero, norm_pow] at hn
  exact ⟨b, hw', (pow_lt_one_iff_of_nonneg (norm_nonneg _) hp.out.ne_zero).mp
    (hn.trans_lt (HDec.PkgI4.Cp.norm_p_lt_one p))⟩

private theorem cyclotomic_power_near_neg_p {ε : T} (hε : IsGenEps p ε)
    (a : O) (ha : (p : O) ∣ a - (root ε 2 - 1)) :
    ‖(a : Cₚ)^(p * (p - 1)) + (p : Cₚ)‖ < q := by
  let w : O := root ε 1 - 1
  let z : O := root ε 2 - 1
  have hw₀ : w ≠ 0 := sub_ne_zero.mpr hε.2
  have hew : 1 + w = root ε 1 := by dsimp [w]; ring
  have hez : 1 + z = root ε 2 := by dsimp [z]; ring
  obtain ⟨b, hb, hw⟩ := near_p_root p w hw₀ (by
    rw [hew, show (1 : ℕ) = 0 + 1 by rfl, root_succ_pow, root]
    simpa using hε.1)
  have hwb : ‖(w : Cₚ) * (b : Cₚ)‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (norm_le_one p b)).trans_lt hw
  have hbC : (w : Cₚ)^(p - 1) = -(p : Cₚ) * (1 + (w : Cₚ) * b) := by
    exact congrArg (fun x : O => (x : Cₚ)) hb
  have hbnear : ‖(w : Cₚ)^(p - 1) + (p : Cₚ)‖ < q := by
    rw [hbC, show -(p : Cₚ) * (1 + (w : Cₚ) * b) + p = -(p : Cₚ) * ((w : Cₚ) * b) by ring,
      norm_mul, norm_neg]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hwb (HDec.PkgI4.Cp.norm_p_pos p)
  obtain ⟨d, hd⟩ := prime_binomial p z
  rw [hez, root_succ_pow] at hd
  have hzw : w = z^p + (p : O)*z*(1 + z*d) := by dsimp [w]; linear_combination hd
  have hzwC : (w : Cₚ) = (z : Cₚ)^p + (p : Cₚ)*(z : Cₚ)*(1 + (z : Cₚ)*d) := by
    exact_mod_cast hzw
  have hzd : ‖((1 + z*d : O) : Cₚ)‖ ≤ 1 := norm_le_one p _
  push_cast at hzd
  have hz : ‖(z : Cₚ)‖ < 1 := by
    have he : (z : Cₚ)^p = (w : Cₚ) - (p : Cₚ)*(z : Cₚ)*(1 + (z : Cₚ)*d) := by
      linear_combination -hzwC
    have hd' : ‖(p : Cₚ)*(z : Cₚ)*(1 + (z : Cₚ)*d)‖ < 1 := by
      rw [norm_mul, norm_mul]
      apply lt_of_le_of_lt _ (HDec.PkgI4.Cp.norm_p_lt_one p)
      exact (mul_le_of_le_one_right (by positivity) hzd).trans
        (mul_le_of_le_one_right (norm_nonneg _) (norm_le_one p z))
    have hz' : ‖(z : Cₚ)^p‖ < 1 := norm_lt_one_of_close p (y := w) (by
      rw [he, sub_sub_cancel_left, norm_neg]
      exact hd') hw
    rw [norm_pow] at hz'
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hp.out.ne_zero).mp hz'
  have hdiff : ‖(z : Cₚ)^p - (w : Cₚ)‖ < q := by
    have he : (z : Cₚ)^p - (w : Cₚ) = -((p : Cₚ)*(z : Cₚ)*(1 + (z : Cₚ)*d)) := by
      linear_combination -hzwC
    rw [he, norm_neg, norm_mul, norm_mul]
    apply lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) hzd)
    simpa only [mul_one] using mul_lt_mul_of_pos_left hz (HDec.PkgI4.Cp.norm_p_pos p)
  have hzp : ‖(z : Cₚ)^p‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hz hp.out.ne_zero
  have he1 : ‖(z : Cₚ)^(p * (p - 1)) - (w : Cₚ)^(p - 1)‖ < q := by
    rw [pow_mul]
    by_cases h : p - 1 = 1
    · simpa only [h, pow_one] using hdiff
    · have := hp.out.two_le
      exact norm_pow_sub_lt p (by omega) hzp hw (HDec.PkgI4.Cp.norm_p_pos p) hdiff.le
  have haz : ‖(a : Cₚ) - (z : Cₚ)‖ ≤ q := norm_sub_of_p_dvd p ha
  have ha' : ‖(a : Cₚ)‖ < 1 := norm_lt_one_of_close p
    (haz.trans_lt (HDec.PkgI4.Cp.norm_p_lt_one p)) hz
  have hpp : 2 ≤ p*(p-1) := by
    have := hp.out.two_le
    calc 2 ≤ p := this
      _ ≤ p * (p-1) := Nat.le_mul_of_pos_right _ (by omega)
  have he2 := norm_pow_sub_lt p hpp ha' hz (HDec.PkgI4.Cp.norm_p_pos p) haz
  calc
    _ = ‖((a : Cₚ)^(p * (p - 1)) - (z : Cₚ)^(p * (p - 1))) +
          (((z : Cₚ)^(p * (p - 1)) - (w : Cₚ)^(p - 1)) +
          ((w : Cₚ)^(p - 1) + p))‖ := by congr 1; ring
    _ ≤ max ‖(a : Cₚ)^(p * (p - 1)) - (z : Cₚ)^(p * (p - 1))‖
          (max ‖(z : Cₚ)^(p * (p - 1)) - (w : Cₚ)^(p - 1)‖
            ‖(w : Cₚ)^(p - 1) + p‖) :=
      (norm_add_le_max _ _).trans (max_le_max_left _ (norm_add_le_max _ _))
    _ < q := max_lt he2 (max_lt he1 hbnear)

/-- For the cyclotomic coordinate ε − 1 there is a unit correction. The
given u has residue close to −1, and the exponent p comes from going
back from the first cyclotomic root to ε − 1. -/
theorem exists_cyclotomic_correction {ε : T} (hε : IsGenEps p ε) :
    ∃ u : T, (ε - 1)^(p - 1) = (pFlat p)^p * u^p ∧
      ‖(u.untilt : Cₚ) + 1‖ < 1 := by
  let y : T := ((frobeniusEquiv T p).symm^[2]) (ε - 1)
  let a : O := y.untilt
  have ha : (p : O) ∣ a - (root ε 2 - 1) := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
    change Ideal.Quotient.mk _ (root (ε - 1) 2) = _
    rw [mk_root, map_sub, map_sub, mk_root, map_one, map_one]
  have h := cyclotomic_power_near_neg_p p hε a ha
  let c := y^(p * (p - 1))
  have hcn : ‖(c.untilt : Cₚ)‖ = q := by
    rw [show c.untilt = a^(p*(p-1)) by exact map_pow PreTilt.untilt _ _, SubmonoidClass.coe_pow]
    have hclose : ‖(a : Cₚ)^(p*(p-1)) - -(p : Cₚ)‖ < ‖-(p : Cₚ)‖ := by
      simpa only [sub_neg_eq_add, norm_neg] using h
    simpa only [norm_neg] using norm_eq_of_close p hclose
  have hc0 : PreTilt.coeff 0 c = 0 := by
    rw [← PreTilt.mk_untilt_eq_coeff_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact p_dvd_of_norm p _ hcn.le
  obtain ⟨u, hu⟩ := dvd_of_coeff_zero p (pFlat p) (untilt_pFlat p) c hc0
  have hpow : y^p^2 = ε - 1 := by
    exact iterate_frobeniusEquiv_symm_pow_p_pow T p (ε - 1) 2
  refine ⟨u, ?_, ?_⟩
  · rw [← mul_pow, ← hu, ← hpow, ← pow_mul]
    change y ^ (p^2 * (p-1)) = (y^(p*(p-1)))^p
    rw [← pow_mul]
    congr 1
    ring
  · have huc := congrArg PreTilt.untilt hu
    rw [map_mul, untilt_pFlat, show c.untilt = a^(p*(p-1)) by exact map_pow PreTilt.untilt _ _] at huc
    have hc : (a : Cₚ)^(p*(p-1)) = (p : Cₚ) * (u.untilt : Cₚ) := by exact_mod_cast huc
    rw [hc, ← mul_add_one, norm_mul] at h
    exact (mul_lt_mul_iff_right₀ (HDec.PkgI4.Cp.norm_p_pos p)).mp (by
      simpa only [one_mul, mul_comm q] using h)

/-- An even power of the correction belongs to the domain of the
near-one logarithm. The even factor eliminates the sign uniformly. -/
theorem exists_small_power_of_correction (u : T) (hu : ‖(u.untilt : Cₚ) + 1‖ < 1) :
    ∃ m : ℕ, 0 < m ∧ (p : O) ∣ (u^m).untilt - 1 := by
  let a : O := (u^2).untilt - 1
  have ha : ‖(a : Cₚ)‖ < 1 := by
    have hu' : ‖(u.untilt : Cₚ) - 1‖ ≤ 1 := by
      simpa only [sub_eq_add_neg, norm_neg, norm_one, max_eq_right (norm_le_one p u.untilt)] using
        norm_add_le_max (u.untilt : Cₚ) (-1)
    have he : (a : Cₚ) = ((u.untilt : Cₚ) + 1) * ((u.untilt : Cₚ) - 1) := by
      change (((u^2).untilt : O) : Cₚ) - 1 = _
      rw [map_pow, SubmonoidClass.coe_pow]
      ring
    rw [he, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hu').trans_lt hu
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (HDec.PkgI4.Cp.norm_p_pos p) ha
  have hNp : N ≤ p^N := by
    clear hN
    induction N with
    | zero => simp
    | succ N ih =>
      rw [pow_succ]
      have hh : 1 ≤ p^N := Nat.one_le_pow _ _ hp.out.pos
      have hpp : 2 ≤ p := hp.out.two_le
      calc
        N + 1 ≤ p^N + p^N := by omega
        _ = p^N * 2 := by ring
        _ ≤ p^N * p := Nat.mul_le_mul_left _ hpp
  have hpa : (p : O) ∣ a^(p^N) := by
    apply p_dvd_of_norm p
    rw [SubmonoidClass.coe_pow, norm_pow]
    calc
      ‖(a : Cₚ)‖ ^ (p^N) = ‖(a : Cₚ)‖ ^ N * ‖(a : Cₚ)‖ ^ (p^N - N) := by
        rw [← pow_add, Nat.add_sub_of_le hNp]
      _ ≤ ‖(a : Cₚ)‖ ^ N := mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) ha.le)
      _ ≤ q := hN.le
  refine ⟨2 * p^N, Nat.mul_pos (by decide) (pow_pos hp.out.pos _), ?_⟩
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  let qmk := Ideal.Quotient.mk (Ideal.span {(p : O)})
  change qmk ((u ^ (2*p^N)).untilt - 1) = 0
  rw [pow_mul, map_pow (PreTilt.untilt (p := p)), map_sub, map_pow, map_one]
  rw [show (1 : O ⧸ Ideal.span {(p : O)}) = 1 ^ p^N by rw [one_pow],
    ← sub_pow_char_pow]
  change Ideal.Quotient.mk _ a ^ (p^N) = 0
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact hpa

/-- There is a positive power of the unit correction to which the
Witt-lift logarithm applies. -/
theorem exists_cyclotomic_small_unit {ε : T} (hε : IsGenEps p ε) :
    ∃ (u : T) (m : ℕ), 0 < m ∧ (ε - 1)^(p - 1) = (pFlat p)^p * u^p ∧
      (p : O) ∣ (u^m).untilt - 1 := by
  obtain ⟨u, he, hsmall⟩ := exists_cyclotomic_correction p hε
  obtain ⟨m, hm, hx⟩ := exists_small_power_of_correction p u hsmall
  exact ⟨u, m, hm, he, hx⟩

/-- A coordinate built from the cyclotomic correction and a near-one
logarithm. Compatibility with a particular branch requires the
independence and multiplication laws for the Witt-lift formula. -/
def cyclotomicCoordinate {ε : T} (hε : IsGenEps p ε) : BdR p :=
  let h := exists_cyclotomic_small_unit p hε
  let u := Classical.choose h
  let m := Classical.choose (Classical.choose_spec h)
  coordinateFromUnit p (u^m) (Classical.choose_spec (Classical.choose_spec h)).2.2 m

theorem cyclotomicCoordinate_adjoin_eq {ε : T} (hε : IsGenEps p ε) :
    Algebra.adjoin ℚ_[p] ((Bmax p : Set (BdR p)) ∪ {cyclotomicCoordinate p hε}) =
      BergerBst.Bst p :=
  coordinateFromUnit_adjoin_eq p _ _ _

end ZInQ.Manuscript.BergerComparison
