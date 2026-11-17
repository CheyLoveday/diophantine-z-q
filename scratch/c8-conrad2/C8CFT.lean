import ZInQKernel.Contrib.OneProof.C8LocAlg

set_option linter.style.longLine false

noncomputable section

namespace HDec.G0Galois.C8Conrad

open _root_.PkgI4 (GaloisRep GaloisChar)

section Torsion

variable (p : ℕ) [Fact p.Prime]

local notation "K" => PadicAlgCl p

theorem norm_natCast_K (n : ℕ) : ‖(n : K)‖ = ‖(n : ℚ_[p])‖ := by
  rw [← PadicAlgCl.norm_extends p (n : ℚ_[p]), map_natCast]

theorem norm_p_K : ‖(p : K)‖ = (p : ℝ)⁻¹ := by rw [norm_natCast_K, Padic.norm_p]

theorem norm_p_K_pos : 0 < ‖(p : K)‖ := by
  rw [norm_p_K]; exact inv_pos.2 (by exact_mod_cast (Fact.out : p.Prime).pos)

theorem norm_p_K_lt_one : ‖(p : K)‖ < 1 := by
  rw [norm_p_K]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

theorem norm_le_one_of_norm_sub_one_lt {x : K} (h : ‖x - 1‖ < 1) : ‖x‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (x - 1) 1
  rw [sub_add_cancel, norm_one] at this
  exact this.trans (max_le h.le le_rfl)

theorem norm_pow_sub_one_le {x : K} (h : ‖x - 1‖ < 1) (i : ℕ) : ‖x ^ i - 1‖ ≤ ‖x - 1‖ := by
  rw [← geom_sum_mul, norm_mul]
  have hs : ‖∑ j ∈ Finset.range i, x ^ j‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_le_one_of_norm_sub_one_lt p h)
  calc ‖∑ j ∈ Finset.range i, x ^ j‖ * ‖x - 1‖ ≤ 1 * ‖x - 1‖ :=
        mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ = ‖x - 1‖ := one_mul _

/-- Prime-to-`p` torsion: `‖x - 1‖ < 1`, `x^n = 1`, `p ∤ n` force `x = 1`. -/
theorem eq_one_of_pow_eq_one_coprime {x : K} (h : ‖x - 1‖ < 1) {n : ℕ} (hn : p.Coprime n)
    (hx : x ^ n = 1) : x = 1 := by
  set S := ∑ j ∈ Finset.range n, x ^ j
  have hS : ‖S - n‖ < 1 := by
    have : S - n = ∑ j ∈ Finset.range n, (x ^ j - 1) := by
      simp [S, Finset.sum_sub_distrib]
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
      fun j _ => norm_pow_sub_one_le p h j) h
  have hn1 : ‖(n : K)‖ = 1 := by rw [norm_natCast_K]; exact Padic.norm_natCast_eq_one_iff.2 hn
  have hS1 : ‖S‖ = 1 := by
    have h2 : ‖S - n‖ ≠ ‖(n : K)‖ := by rw [hn1]; exact hS.ne
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2
    rw [sub_add_cancel, hn1] at this
    rw [this]; exact max_eq_right hS.le
  have h0 : S * (x - 1) = 0 := by rw [geom_sum_mul, hx, sub_self]
  rcases mul_eq_zero.1 h0 with h1 | h1
  · rw [h1, norm_zero] at hS1; exact absurd hS1 zero_ne_one
  · exact sub_eq_zero.1 h1

theorem binom_split {R : Type*} [CommRing R] (y : R) (n q : ℕ) (hq : n = q + 2) :
    (y + 1) ^ n = ∑ k ∈ Finset.range q, y ^ (k + 2) * (n.choose (k + 2) : R) + (n : R) * y + 1 + y ^ n := by
  subst hq
  rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [one_pow, mul_one, pow_zero, pow_one, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.cast_one, Nat.choose_self, zero_add, Nat.sub_self]
  ring

/-- `p`-torsion: `‖x - 1‖ < ‖p‖` and `x^p = 1` force `x = 1`. -/
theorem eq_one_of_pow_p_eq_one {x : K} (h : ‖x - 1‖ < ‖(p : K)‖) (hx : x ^ p = 1) : x = 1 := by
  by_contra hne
  set y := x - 1 with hy_def
  have hy0 : y ≠ 0 := sub_ne_zero.2 hne
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hy1 : ‖y‖ < 1 := h.trans (norm_p_K_lt_one p)
  obtain ⟨q, hq⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := (Fact.out : p.Prime).two_le; omega⟩
  have hexp := binom_split y p q hq
  have hR : ‖∑ k ∈ Finset.range q, y ^ (k + 2) * (p.choose (k + 2) : K)‖ ≤ ‖(p : K)‖ * ‖y‖ ^ 2 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k hk => by
      have hk' : k + 2 < p := by rw [Finset.mem_range] at hk; omega
      obtain ⟨c, hc⟩ := (Fact.out : p.Prime).dvd_choose_self (by omega) hk'
      rw [hc, Nat.cast_mul, norm_mul, norm_mul, norm_pow]
      have hc1 : ‖(c : K)‖ ≤ 1 := by rw [norm_natCast_K]; simpa using Padic.norm_int_le_one (p := p) c
      have hpow : ‖y‖ ^ (k + 2) ≤ ‖y‖ ^ 2 := pow_le_pow_of_le_one (norm_nonneg _) hy1.le (by omega)
      calc ‖y‖ ^ (k + 2) * (‖(p : K)‖ * ‖(c : K)‖) ≤ ‖y‖ ^ 2 * (‖(p : K)‖ * 1) := by gcongr
        _ = ‖(p : K)‖ * ‖y‖ ^ 2 := by ring
  have hyp : ‖y ^ p‖ < ‖(p : K)‖ * ‖y‖ := by
    rw [norm_pow]
    calc ‖y‖ ^ p ≤ ‖y‖ ^ 2 := pow_le_pow_of_le_one (norm_nonneg _) hy1.le (Fact.out : p.Prime).two_le
      _ = ‖y‖ * ‖y‖ := pow_two _
      _ < ‖(p : K)‖ * ‖y‖ := mul_lt_mul_of_pos_right h hyn
  have hsum : ∑ k ∈ Finset.range q, y ^ (k + 2) * (p.choose (k + 2) : K) + (p : K) * y + y ^ p = 0 := by
    have : (y + 1) ^ p = 1 := by rw [hy_def, sub_add_cancel, hx]
    rw [hexp] at this
    linear_combination this
  have hmain : ‖(p : K) * y‖ = ‖(p : K)‖ * ‖y‖ := norm_mul _ _
  have hrest : ‖∑ k ∈ Finset.range q, y ^ (k + 2) * (p.choose (k + 2) : K) + y ^ p‖ < ‖(p : K) * y‖ := by
    rw [hmain]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hyp)
    calc _ ≤ ‖(p : K)‖ * ‖y‖ ^ 2 := hR
      _ < ‖(p : K)‖ * ‖y‖ := by
        rw [pow_two]
        exact mul_lt_mul_of_pos_left (mul_lt_of_lt_one_left hyn hy1) (norm_p_K_pos p)
  have : ‖(p : K) * y + (∑ k ∈ Finset.range q, y ^ (k + 2) * (p.choose (k + 2) : K) + y ^ p)‖ = ‖(p : K) * y‖ := by
    rw [add_comm]
    exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hrest.ne |>.trans (max_eq_right hrest.le)
  have h0 : (p : K) * y + (∑ k ∈ Finset.range q, y ^ (k + 2) * (p.choose (k + 2) : K) + y ^ p) = 0 := by
    linear_combination hsum
  rw [h0, norm_zero, hmain] at this
  exact (mul_pos (norm_p_K_pos p) hyn).ne' this.symm

/-- No nontrivial torsion within `‖x - 1‖ < ‖p‖`. -/
theorem eq_one_of_pow_eq_one_small {x : K} (h : ‖x - 1‖ < ‖(p : K)‖) {m : ℕ} (hm : 0 < m)
    (hx : x ^ m = 1) : x = 1 := by
  obtain ⟨a, b, hb, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p (Fact.out : p.Prime).ne_one
  have h1 : ‖x - 1‖ < 1 := h.trans (norm_p_K_lt_one p)
  have hy : x ^ p ^ a = 1 := by
    refine eq_one_of_pow_eq_one_coprime p (lt_of_le_of_lt (norm_pow_sub_one_le p h1 _) h1)
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hb) ?_
    rw [← pow_mul, hx]
  clear hx hm
  induction a with
  | zero => simpa using hy
  | succ a ih =>
    apply ih
    refine eq_one_of_pow_p_eq_one p (lt_of_le_of_lt (norm_pow_sub_one_le p h1 _) h) ?_
    rw [← pow_mul, ← pow_succ, hy]

/-- The open subgroup `V = {u : ‖u - 1‖ < ‖p‖}` of `ℚ̄_p^×`; it has no nontrivial torsion. -/
def smallUnits : Subgroup (PadicAlgCl p)ˣ where
  carrier := {u | ‖((u : K)) - 1‖ < ‖(p : K)‖}
  one_mem' := by simp [norm_p_K_pos p]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at ha hb ⊢
    have ha1 : ‖(a : K)‖ ≤ 1 := norm_le_one_of_norm_sub_one_lt p (ha.trans (norm_p_K_lt_one p))
    have : (a : K) * b - 1 = a * (b - 1) + (a - 1) := by ring
    rw [this]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ha)
    rw [norm_mul]
    calc ‖(a : K)‖ * ‖(b : K) - 1‖ ≤ 1 * ‖(b : K) - 1‖ := by gcongr
      _ < ‖(p : K)‖ := by rw [one_mul]; exact hb
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have ha1 : ‖(a : K) - 1‖ < 1 := ha.trans (norm_p_K_lt_one p)
    have hna : ‖(a : K)‖ = 1 := by
      have h2 : ‖(a : K) - 1‖ ≠ ‖(1 : K)‖ := by rw [norm_one]; exact ha1.ne
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2
      rw [sub_add_cancel, norm_one] at this
      rw [this]; exact max_eq_right ha1.le
    have : ((a⁻¹ : (PadicAlgCl p)ˣ) : K) - 1 = (a⁻¹ : (PadicAlgCl p)ˣ) * (1 - a) := by
      rw [mul_sub, mul_one, Units.inv_mul]
    rw [this, norm_mul, norm_sub_rev]
    have hinv : ‖((a⁻¹ : (PadicAlgCl p)ˣ) : K)‖ = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, hna, inv_one]
    rw [hinv, one_mul]; exact ha

theorem isOpen_smallUnits : IsOpen ((smallUnits p : Subgroup (PadicAlgCl p)ˣ) : Set (PadicAlgCl p)ˣ) := by
  have : ((smallUnits p : Subgroup (PadicAlgCl p)ˣ) : Set (PadicAlgCl p)ˣ) =
      Units.val ⁻¹' Metric.ball (1 : K) ‖(p : K)‖ := by
    ext u; simp [smallUnits, Metric.mem_ball, dist_eq_norm]
  rw [this]
  exact Metric.isOpen_ball.preimage Units.continuous_val

end Torsion

end HDec.G0Galois.C8Conrad
