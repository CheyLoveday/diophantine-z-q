import ZInQKernel.Contrib.OneProof.T21Proof.LocalPred

/-!
# t21-proof: the global step and the 2-adic obstruction

Task t21-proof.
* `global_step`: a nonzero `γ ∈ B = ℍ[ℚ]` lying in `ℚ_p^× O_{B,p}^×` at every odd prime `p` is
  `q · n` with `n` an integral Hurwitz element of norm `2^k`.
* `two_adic_step`: if moreover `γ⁻¹ β ∈ ℚ_2^× R_2^×` (`R_2 = ℤ_2 + ℤ_2 ω + 4O_{B,2}`) for an
  integral `β` of odd norm, then `μ β ≡ X + Y ω (mod 4O_B)` for a unit `μ` of `O_B`.
* `unitList`: the 24 units of the Hurwitz order (every integral element of norm `1` is in it).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

noncomputable section

namespace ZInQ.Contrib.T21Proof

open scoped Quaternion

/-! ## `p`-adic norms -/

theorem norm_le_inv_of_lt_one {p : ℕ} [hp : Fact p.Prime] {x : ℚ_[p]} (h : ‖x‖ < 1) :
    ‖x‖ ≤ (p : ℝ)⁻¹ := by
  by_cases hx : x = 0
  · rw [hx, norm_zero]; positivity
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [Padic.norm_eq_zpow_neg_valuation hx] at h ⊢
  have hv : 1 ≤ x.valuation := by
    by_contra hv
    push_neg at hv
    have : (1 : ℝ) ≤ (p : ℝ) ^ (-x.valuation) := one_le_zpow₀ hp1.le (by omega)
    linarith
  calc (p : ℝ) ^ (-x.valuation) ≤ (p : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hp1.le (by omega)
    _ = (p : ℝ)⁻¹ := zpow_neg_one _

/-- The cast of `hur` of an integer vector. -/
def hurZ {R : Type*} [Field R] [CharZero R] (n : H4 ℤ) : ℍ[R] := hur (mapH (Int.castRingHom R) n)

theorem qp_hurZ {p : ℕ} [Fact p.Prime] (n : H4 ℤ) : qp p (hurZ n) = hurZ n := by
  apply hc_injective
  rw [qp, hc_qmap, hurZ, hurZ, hc_hur, hc_hur]
  ext <;> simp [mapH]

theorem normSq_hurZ {R : Type*} [Field R] [CharZero R] (n : H4 ℤ) :
    Quaternion.normSq (hurZ n : ℍ[R]) = ((nrdH n : ℤ) : R) := by
  rw [normSq_eq_nrdH, hurZ, hc_hur, ← map_nrdH]; rfl

theorem nrdH_pos {n : H4 ℤ} (hn : n ≠ ⟨0, 0, 0, 0⟩) : 0 < nrdH n := by
  have h4 : 4 * nrdH n = (2 * n.a0 - n.a3) ^ 2 + (2 * n.a1 + n.a3) ^ 2 + (2 * n.a2 + n.a3) ^ 2 +
      n.a3 ^ 2 := by simp only [nrdH]; ring
  by_contra h
  push_neg at h
  have s0 := sq_nonneg (2 * n.a0 - n.a3)
  have s1 := sq_nonneg (2 * n.a1 + n.a3)
  have s2 := sq_nonneg (2 * n.a2 + n.a3)
  have s3 := sq_nonneg n.a3
  have h0 : n.a3 = 0 := by nlinarith
  have h1 : n.a0 = 0 := by nlinarith
  have h2 : n.a1 = 0 := by nlinarith
  have h3 : n.a2 = 0 := by nlinarith
  exact hn (by ext <;> assumption)

/-! ## A primitive integer vector -/

theorem exists_primitive (γ : ℍ[ℚ]) (hγ : γ ≠ 0) : ∃ (q : ℚ) (n : H4 ℤ), q ≠ 0 ∧
    γ = q • hurZ n ∧ n ≠ ⟨0, 0, 0, 0⟩ ∧
    ∀ d : ℤ, d ∣ n.a0 → d ∣ n.a1 → d ∣ n.a2 → d ∣ n.a3 → IsUnit d := by
  set x := hc γ with hx
  set D : ℕ := x.a0.den * x.a1.den * x.a2.den * x.a3.den with hD
  have hDpos : 0 < D := by positivity
  have hint : ∀ r : ℚ, r.den ∣ D → ∃ m : ℤ, (m : ℚ) = r * D := fun r hr => by
    obtain ⟨e, he⟩ := hr
    refine ⟨r.num * e, ?_⟩
    rw [he]; push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  obtain ⟨m0, e0⟩ := hint x.a0 ⟨x.a1.den * x.a2.den * x.a3.den, by rw [hD]; ring⟩
  obtain ⟨m1, e1⟩ := hint x.a1 ⟨x.a0.den * x.a2.den * x.a3.den, by rw [hD]; ring⟩
  obtain ⟨m2, e2⟩ := hint x.a2 ⟨x.a0.den * x.a1.den * x.a3.den, by rw [hD]; ring⟩
  obtain ⟨m3, e3⟩ := hint x.a3 ⟨x.a0.den * x.a1.den * x.a2.den, by rw [hD]; ring⟩
  set g : ℤ := ((Int.gcd m0 (Int.gcd m1 (Int.gcd m2 m3) : ℤ)) : ℤ) with hg
  have hm_ne : ¬ (m0 = 0 ∧ m1 = 0 ∧ m2 = 0 ∧ m3 = 0) := by
    rintro ⟨h0, h1, h2, h3⟩
    apply hγ
    apply hc_injective
    have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    rw [h0] at e0; rw [h1] at e1; rw [h2] at e2; rw [h3] at e3
    simp only [Int.cast_zero] at e0 e1 e2 e3
    have : hc (0 : ℍ[ℚ]) = ⟨0, 0, 0, 0⟩ := by ext <;> simp [hc]
    rw [this]
    ext
    · exact (mul_eq_zero.mp e0.symm).resolve_right hD0
    · exact (mul_eq_zero.mp e1.symm).resolve_right hD0
    · exact (mul_eq_zero.mp e2.symm).resolve_right hD0
    · exact (mul_eq_zero.mp e3.symm).resolve_right hD0
  have hg0 : g ≠ 0 := by
    intro h
    rw [hg, Int.natCast_eq_zero, Int.gcd_eq_zero_iff] at h
    obtain ⟨h0, h⟩ := h
    rw [Int.natCast_eq_zero, Int.gcd_eq_zero_iff] at h
    obtain ⟨h1, h⟩ := h
    rw [Int.natCast_eq_zero, Int.gcd_eq_zero_iff] at h
    exact hm_ne ⟨h0, h1, h.1, h.2⟩
  have d0 : g ∣ m0 := Int.gcd_dvd_left _ _
  have d1 : g ∣ m1 := (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_left _ _)
  have d2 : g ∣ m2 := ((Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right _ _)).trans
    (Int.gcd_dvd_left _ _)
  have d3 : g ∣ m3 := ((Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right _ _)).trans
    (Int.gcd_dvd_right _ _)
  clear_value g
  obtain ⟨n0, rfl⟩ := d0
  obtain ⟨n1, rfl⟩ := d1
  obtain ⟨n2, rfl⟩ := d2
  obtain ⟨n3, rfl⟩ := d3
  refine ⟨(g : ℚ) / D, ⟨n0, n1, n2, n3⟩, ?_, ?_, ?_, ?_⟩
  · have : (g : ℚ) ≠ 0 := by exact_mod_cast hg0
    exact div_ne_zero this (by exact_mod_cast hDpos.ne')
  · apply hc_injective
    rw [hc_smul, hurZ, hc_hur]
    have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    push_cast at e0 e1 e2 e3
    ext <;> simp only [mapH, eq_intCast]
    · rw [← hx]; field_simp; linarith
    · rw [← hx]; field_simp; linarith
    · rw [← hx]; field_simp; linarith
    · rw [← hx]; field_simp; linarith
  · intro h
    simp only [H4.mk.injEq] at h
    apply hm_ne
    simp [h.1, h.2.1, h.2.2.1, h.2.2.2]
  · intro d h0 h1 h2 h3
    have hdg : g * d ∣ g := by
      have := Int.dvd_coe_gcd (mul_dvd_mul_left g h0) (Int.dvd_coe_gcd (mul_dvd_mul_left g h1)
        (Int.dvd_coe_gcd (mul_dvd_mul_left g h2) (mul_dvd_mul_left g h3)))
      rw [← hg] at this
      exact this
    obtain ⟨e, he⟩ := hdg
    have hde : d * e = 1 := by
      have : g * 1 = g * (d * e) := by rw [mul_one]; nth_rewrite 1 [he]; ring
      exact (mul_left_cancel₀ hg0 this).symm
    exact ⟨⟨d, e, hde, by rw [mul_comm]; exact hde⟩, rfl⟩

end ZInQ.Contrib.T21Proof
