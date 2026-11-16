import ZInQKernel.Contrib.OneProof.HfxProof.Order1
import ZInQKernel.Contrib.OneProof.HfxProof.Finite1

/-!
# hfx-proof: the test vector for `n ≡ 1 (mod 8)`

Task hfx-proof. For squarefree `n ≡ 1 (mod 8)` and admissible `τ`, `π_ℤ^{U_n}` has a nonzero generator
(`testVector_one8`): `ω = τ(√−n) = a i + b j + c k`, `K_{n,2} = ℚ_2(ω)` is ramified with uniformizer
`1 + ω`, and the table `tab1` gives the three orbits of `K_{n,2}^×` on TYZ's 8 classes (sizes 2, 2, 4);
the generator is `1, −1, 0` on them.
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.HfxProof

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.T21Proof IsDedekindDomain NumberField
open scoped Quaternion
open ZInQ.RouteK.Rank5b

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-! ## Rank one -/

theorem val1_inj : ∀ i j : Fin 3, val1 i = val1 j → i = j := by decide

theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide

theorem sum_three (c : T8 → Fin 3) (w : T8 → ℤ) (g : Fin 3 → ℤ) :
    ∑ t, w t * g (c t) = g 0 * (∑ t, if c t = 0 then w t else 0) +
      g 1 * (∑ t, if c t = 1 then w t else 0) + g 2 * (∑ t, if c t = 2 then w t else 0) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rcases fin3_cases (c t) with h | h | h <;> simp [h, mul_comm]

theorem rank1_three (c : T8 → Fin 3) (G : T8 → ℤ) {r0 r1 r2 : T8} (h0 : c r0 = 0) (h1 : c r1 = 1)
    (h2 : c r2 = 2)
    (hN0 : (∑ t, if c t = 0 then (1 : ℤ) else 0) = 2) (hN1 : (∑ t, if c t = 1 then (1 : ℤ) else 0) = 2)
    (hN2 : (∑ t, if c t = 2 then (1 : ℤ) else 0) = 4)
    (hM0 : (∑ t, if c t = 0 then chi0Z t else 0) = 2) (hM1 : (∑ t, if c t = 1 then chi0Z t else 0) = 2)
    (hM2 : (∑ t, if c t = 2 then chi0Z t else 0) = -4)
    (hG : ∀ t t', val1 (c t) = val1 (c t') → G t = G t') (hGs : ∑ t, G t = 0)
    (hGc : ∑ t, chi0Rep t * G t = 0) : ∃ k : ℤ, ∀ t, G t = k * val1 (c t) := by
  set g : Fin 3 → ℤ := ![G r0, G r1, G r2] with hg
  have hGg : ∀ t, G t = g (c t) := by
    intro t
    rcases fin3_cases (c t) with h | h | h
    · rw [h]; exact hG t r0 (by rw [h, h0])
    · rw [h]; exact hG t r1 (by rw [h, h1])
    · rw [h]; exact hG t r2 (by rw [h, h2])
  have e1 := sum_three c (fun _ => 1) g
  have e2 := sum_three c chi0Z g
  simp only [one_mul] at e1
  rw [Finset.sum_congr rfl (fun t _ => hGg t)] at hGs
  rw [Finset.sum_congr rfl (fun t _ => by rw [hGg t, chi0Rep_eq])] at hGc
  rw [hGs, hN0, hN1, hN2] at e1
  rw [hGc, hM0, hM1, hM2] at e2
  have hg2 : g 2 = 0 := by linarith
  have hg1 : g 1 = -g 0 := by linarith
  refine ⟨g 0, fun t => ?_⟩
  rw [hGg t]
  rcases fin3_cases (c t) with h | h | h <;> rw [h]
  · simp [val1]
  · rw [hg1]; simp [val1]
  · rw [hg2]; simp [val1]

/-! ## Data -/

/-- Hurwitz coordinates of `a i + b j + c k`. -/
def ωH1 (a b c : ℤ) : H4 ℤ := ⟨c, a - c, b - c, 2 * c⟩

theorem hurZ_ωH1 (a b c : ℤ) :
    (hurZ (ωH1 a b c) : ℍ[ℚ]) = ⟨0, (a : ℚ), (b : ℚ), (c : ℚ)⟩ := by
  ext <;> simp [hurZ, hur, ωH1, mapH] <;> ring

theorem hurZ_ϖH1 (a b c : ℤ) :
    (hurZ (⟨1 + c, a - c, b - c, 2 * c⟩ : H4 ℤ) : ℍ[ℚ]) = 1 + ⟨0, (a : ℚ), (b : ℚ), (c : ℚ)⟩ := by
  ext <;> simp [hurZ, hur, mapH] <;> ring

theorem zmod8_four_mul (x : ZMod 8) : 4 * x = 0 ∨ 4 * x = 4 := by revert x; decide

theorem dvd_of_val_mod {z : ℤ} {m : ℕ} (hm : m ∣ 8) (h : ((z : ZMod 8)).val % m = 0) : (m : ℤ) ∣ z := by
  have hv : (((z : ZMod 8).val : ℕ) : ℤ) = z % 8 := ZMod.val_intCast z
  have h1 : (m : ℤ) ∣ z % 8 := by
    rw [← hv]; exact_mod_cast Nat.dvd_of_mod_eq_zero h
  have h2 : (m : ℤ) ∣ 8 * (z / 8) := Dvd.dvd.mul_right (by exact_mod_cast hm) _
  have := dvd_add h1 h2
  have e := Int.emod_add_mul_ediv z 8
  rw [e] at this; exact this

theorem exists_smulH_of_divB {E : H4 ℤ} {b : Fin 2}
    (h : DivB b (mapH (Int.castRingHom (ZMod 8)) E)) : ∃ C : H4 ℤ, E = smulH (4 * 2 ^ b.val) C := by
  have hm : 4 * 2 ^ b.val ∣ 8 := by fin_cases b <;> decide
  obtain ⟨h0, h1, h2, h3⟩ := h
  obtain ⟨c0, e0⟩ := dvd_of_val_mod hm h0
  obtain ⟨c1, e1⟩ := dvd_of_val_mod hm h1
  obtain ⟨c2, e2⟩ := dvd_of_val_mod hm h2
  obtain ⟨c3, e3⟩ := dvd_of_val_mod hm h3
  refine ⟨⟨c0, c1, c2, c3⟩, ?_⟩
  ext <;> simp only [smulH] <;> push_cast at e0 e1 e2 e3 ⊢
  · exact e0
  · exact e1
  · exact e2
  · exact e3

theorem natCast_val_zmod8 (x : ZMod 8) : (((x.val : ℕ) : ℤ) : ZMod 8) = x := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem to4_intCast (m : ℤ) : to4 (m : ZMod 8) = (m : ZMod 4) := map_intCast to4 m

theorem pairs1_cover : ∀ i j : Fin 3, i ≠ j →
    (root1 i, root1 j) ∈ pairs1 ∨ (root1 j, root1 i) ∈ pairs1 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [root1, pairs1]

/-! ## The centralizer at `2` -/

theorem loc_of_commute1 {k : ℕ} {A B C : ℚ_[2]}
    (hABC : A ^ 2 + B ^ 2 + C ^ 2 = ((8 * k + 1 : ℕ) : ℚ_[2]))
    (hω : IsHur (Zp 2) (⟨0, A, B, C⟩ : ℍ[ℚ_[2]])) {y : ℍ[ℚ_[2]]} (hy : y ≠ 0)
    (hc : y * ⟨0, A, B, C⟩ = ⟨0, A, B, C⟩ * y) :
    Loc2OK (⟨0, A, B, C⟩ : ℍ[ℚ_[2]]) y ∨ Loc2OK (⟨0, A, B, C⟩ : ℍ[ℚ_[2]]) (y * (1 + ⟨0, A, B, C⟩)) := by
  set ω' : ℍ[ℚ_[2]] := ⟨0, A, B, C⟩ with hω'
  set N : ℚ_[2] := ((8 * k + 1 : ℕ) : ℚ_[2]) with hNdef
  have hN0 : N ≠ 0 := by
    have : ‖N‖ = 1 := by
      rw [hNdef, show ((8 * k + 1 : ℕ) : ℚ_[2]) = (((8 * k + 1 : ℕ) : ℤ) : ℚ_[2]) by push_cast; rfl]
      exact norm_odd_int ⟨4 * k, by push_cast; ring⟩
    intro h; rw [h, norm_zero] at this; exact zero_ne_one this
  have e1 := congrArg (·.imI) hc
  have e2 := congrArg (·.imJ) hc
  have e3 := congrArg (·.imK) hc
  simp [hω'] at e1 e2 e3
  set lam := (A * y.imI + B * y.imJ + C * y.imK) / N with hlam
  have kI : y.imI * N = (A * y.imI + B * y.imJ + C * y.imK) * A := by
    linear_combination (-y.imI) * hABC + (B / 2) * e3 - (C / 2) * e2
  have kJ : y.imJ * N = (A * y.imI + B * y.imJ + C * y.imK) * B := by
    linear_combination (-y.imJ) * hABC - (A / 2) * e3 + (C / 2) * e1
  have kK : y.imK * N = (A * y.imI + B * y.imJ + C * y.imK) * C := by
    linear_combination (-y.imK) * hABC + (A / 2) * e2 - (B / 2) * e1
  have hdec : y = y.re • (1 : ℍ[ℚ_[2]]) + lam • ω' := by
    ext
    · simp [hω']
    · simp only [hω', QuaternionAlgebra.imI_add, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imI_one,
        smul_eq_mul, mul_zero, zero_add]
      rw [hlam, div_mul_eq_mul_div, eq_div_iff hN0]; exact kI
    · simp only [hω', QuaternionAlgebra.imJ_add, QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imJ_one,
        smul_eq_mul, mul_zero, zero_add]
      rw [hlam, div_mul_eq_mul_div, eq_div_iff hN0]; exact kJ
    · simp only [hω', QuaternionAlgebra.imK_add, QuaternionAlgebra.imK_smul, QuaternionAlgebra.imK_one,
        smul_eq_mul, mul_zero, zero_add]
      rw [hlam, div_mul_eq_mul_div, eq_div_iff hN0]; exact kK
  have hω2 : ω' * ω' = -N • 1 := by
    rw [hω']; ext <;> simp
    · linear_combination (-1 : ℚ_[2]) * hABC
    all_goals ring
  have hnrd : ∀ x z : ℚ_[2], Quaternion.normSq (x • (1 : ℍ[ℚ_[2]]) + z • ω') = x ^ 2 + N * z ^ 2 := by
    intro x z; rw [Quaternion.normSq_def', hω']; simp; linear_combination z ^ 2 * hABC
  set X := y.re
  set Y := lam
  have hXY : X ≠ 0 ∨ Y ≠ 0 := by
    by_contra h; push_neg at h
    apply hy; rw [hdec, h.1, h.2, zero_smul, zero_smul, add_zero]
  have hfin : ∀ (c : ℚ_[2]) (u : ℍ[ℚ_[2]]), c ≠ 0 → y = c • u →
      (Loc2OK ω' u ∨ Loc2OK ω' (u * (1 + ω'))) → Loc2OK ω' y ∨ Loc2OK ω' (y * (1 + ω')) := by
    rintro c u hc0 rfl (h | h)
    · exact Or.inl (Loc2OK.smul_left hc0 h)
    · right; rw [smul_mul_assoc]; exact Loc2OK.smul_left hc0 h
  have h1Z : PadicInt.toZMod (1 : ℤ_[2]) ≠ 0 := by rw [map_one]; exact one_ne_zero
  rcases le_total ‖Y‖ ‖X‖ with hle | hle
  · have hX : X ≠ 0 := by
      rcases hXY with h | h
      · exact h
      · intro hX0; rw [hX0, norm_zero] at hle; exact h (norm_le_zero_iff.mp hle)
    have hYX : ‖Y / X‖ ≤ 1 := by rw [norm_div]; exact div_le_one_of_le₀ hle (norm_nonneg _)
    refine hfin X (((1 : ℤ_[2]) : ℚ_[2]) • 1 + ((⟨Y / X, hYX⟩ : ℤ_[2]) : ℚ_[2]) • ω') hX ?_
      (core1 hω hω2 hnrd 1 ⟨Y / X, hYX⟩ (Or.inl h1Z))
    rw [hdec]; simp only [PadicInt.coe_one, smul_add, smul_smul, mul_one]
    congr 2; field_simp
  · have hY : Y ≠ 0 := by
      rcases hXY with h | h
      · intro hY0; rw [hY0, norm_zero] at hle; exact h (norm_le_zero_iff.mp hle)
      · exact h
    have hXY' : ‖X / Y‖ ≤ 1 := by rw [norm_div]; exact div_le_one_of_le₀ hle (norm_nonneg _)
    refine hfin Y (((⟨X / Y, hXY'⟩ : ℤ_[2]) : ℚ_[2]) • 1 + ((1 : ℤ_[2]) : ℚ_[2]) • ω') hY ?_
      (core1 hω hω2 hnrd ⟨X / Y, hXY'⟩ 1 (Or.inr h1Z))
    rw [hdec]; simp only [PadicInt.coe_one, smul_add, smul_smul, mul_one]
    congr 2; field_simp

/-! ## The local condition `C1` -/

section C1def

variable {ω : ℍ[ℚ]} {k : ℕ}

theorem qp_omega_sq (h2 : ω * ω = -(((8 * k + 1 : ℕ) : ℚ)) • 1) :
    qp 2 ω * qp 2 ω = (0 : ℚ_[2]) • qp 2 ω - (((8 * k + 1 : ℕ) : ℚ) : ℚ_[2]) • 1 := by
  rw [← map_mul, h2, zero_smul, zero_sub, qp_smul, map_one]; push_cast; rw [neg_smul]

theorem qp_star_omega (hst : star ω = -ω) : star (qp 2 ω) = (0 : ℚ_[2]) • 1 - qp 2 ω := by
  rw [qp, ← qmap_star, ← qp, hst, map_neg, zero_smul, zero_sub]

theorem norm_qp_varpi (hϖn : Quaternion.normSq (1 + ω) = ((2 * (4 * k + 1) : ℕ) : ℚ)) :
    ‖Quaternion.normSq (qp 2 (1 + ω))‖ = 1 / 2 := by
  rw [normSq_qp, hϖn]
  have : ((((2 * (4 * k + 1) : ℕ) : ℚ)) : ℚ_[2]) = 2 * ((4 * k + 1 : ℤ) : ℚ_[2]) := by push_cast; ring
  rw [this, norm_mul, show (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) by norm_num, Padic.norm_p,
    norm_odd_int ⟨2 * k, by ring⟩]
  norm_num

/-- `L(ϖ²)`: `ϖ² = 2(−4k + ω)`. -/
theorem loc2OK_varpi_sq (hωZ : IsHurZ ω) (h2 : ω * ω = -(((8 * k + 1 : ℕ) : ℚ)) • 1)
    (hnrd : ∀ x z : ℚ_[2], Quaternion.normSq (x • (1 : ℍ[ℚ_[2]]) + z • qp 2 ω) =
      x ^ 2 + ((8 * k + 1 : ℕ) : ℚ_[2]) * z ^ 2) :
    Loc2OK (qp 2 ω) (qp 2 (1 + ω) * qp 2 (1 + ω)) := by
  have e : qp 2 (1 + ω) * qp 2 (1 + ω) =
      (2 : ℚ_[2]) • ((-(4 * k : ℚ_[2])) • (1 : ℍ[ℚ_[2]]) + (1 : ℚ_[2]) • qp 2 ω) := by
    rw [← map_mul, add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, h2, map_add, map_add, map_add,
      map_one, qp_smul, map_one]
    simp only [smul_add, smul_smul, one_smul]
    push_cast
    module
  refine ⟨2, by norm_num, _, e, ?_, ?_, -(4 * k : ℚ_[2]), 1, ?_, by simp, 0, isHur_zero, by simp⟩
  · refine (isHur_one.smul ?_).add ((isHur_qp_hurZ' hωZ).smul (Zp 2).one_mem)
    rw [mem_Zp, norm_neg]
    have := Padic.norm_int_le_one (p := 2) (4 * k : ℤ); push_cast at this; exact this
  · rw [hnrd]
    have : (-(4 * k : ℚ_[2])) ^ 2 + ((8 * k + 1 : ℕ) : ℚ_[2]) * 1 ^ 2 = (((4 * k + 1) ^ 2 : ℤ) : ℚ_[2]) := by
      push_cast; ring
    rw [this]; exact norm_odd_int (Odd.pow ⟨2 * k, by ring⟩)
  · rw [norm_neg]
    have := Padic.norm_int_le_one (p := 2) (4 * k : ℤ); push_cast at this; exact this

end C1def

/-- `ℚ_2^× R_2^× ∪ ℚ_2^× R_2^× ϖ⁻¹` for `ω² = −n`, `ϖ = 1 + ω`. -/
def C1 (ω : ℍ[ℚ]) (k : ℕ) (hωZ : IsHurZ ω) (h2 : ω * ω = -(((8 * k + 1 : ℕ) : ℚ)) • 1)
    (hst : star ω = -ω) (hϖn : Quaternion.normSq (1 + ω) = ((2 * (4 * k + 1) : ℕ) : ℚ))
    (hnrd : ∀ x z : ℚ_[2], Quaternion.normSq (x • (1 : ℍ[ℚ_[2]]) + z • qp 2 ω) =
      x ^ 2 + ((8 * k + 1 : ℕ) : ℚ_[2]) * z ^ 2) : LocCond where
  P p _ y := Loc2OK (qp p ω) y ∨ Loc2OK (qp p ω) (y * qp p (1 + ω))
  one p _ _ := Or.inl Loc2OK.one
  mul p _ hp y z hy hz := by
    subst hp
    have hn := norm_qp_varpi hϖn
    have h0 : Quaternion.normSq (qp 2 (1 + ω)) ≠ 0 := by
      intro h; rw [h, norm_zero] at hn; norm_num at hn
    have hNZ : ((((8 * k + 1 : ℕ) : ℚ)) : ℚ_[2]) ∈ Zp 2 := by
      rw [mem_Zp]; have := Padic.norm_int_le_one (p := 2) ((8 * k + 1 : ℕ) : ℤ)
      push_cast at this ⊢; exact this
    exact P1_mul (L := Loc2OK (qp 2 ω))
      (fun y z hy hz => Loc2OK.mul' (isHur_qp_hurZ' hωZ) (Zp 2).zero_mem hNZ (qp_omega_sq h2) hy hz)
      (fun y z hy h => Loc2OK.of_mul_eq_one' (Zp 2).zero_mem (qp_star_omega hst) hy h)
      (fun z hz => loc2OK_conj (isHur_qp_hurZ' hωZ)
        (isHur_qp_hurZ' (isHur_one.add hωZ)) hn
        (by rw [← map_mul, ← map_mul, mul_add, add_mul, mul_one, one_mul]) hz)
      (loc2OK_varpi_sq hωZ h2 hnrd) (qinv_mul_self h0) (mul_qinv_self h0) hy hz
  inv p _ hp y z hy h := by
    subst hp
    have hn := norm_qp_varpi hϖn
    have h0 : Quaternion.normSq (qp 2 (1 + ω)) ≠ 0 := by
      intro h; rw [h, norm_zero] at hn; norm_num at hn
    have hNZ : ((((8 * k + 1 : ℕ) : ℚ)) : ℚ_[2]) ∈ Zp 2 := by
      rw [mem_Zp]; have := Padic.norm_int_le_one (p := 2) ((8 * k + 1 : ℕ) : ℤ)
      push_cast at this ⊢; exact this
    exact P1_inv (L := Loc2OK (qp 2 ω))
      (fun y z hy h => Loc2OK.of_mul_eq_one' (Zp 2).zero_mem (qp_star_omega hst) hy h)
      (fun y z hy hz => Loc2OK.mul' (isHur_qp_hurZ' hωZ) (Zp 2).zero_mem hNZ (qp_omega_sq h2) hy hz)
      (fun z hz => loc2OK_conj (isHur_qp_hurZ' hωZ)
        (isHur_qp_hurZ' (isHur_one.add hωZ)) hn
        (by rw [← map_mul, ← map_mul, mul_add, add_mul, mul_one, one_mul]) hz)
      (loc2OK_varpi_sq hωZ h2 hnrd) (mul_qinv_self h0) hy h

/-! ## The main theorem for `n ≡ 1 (mod 8)` -/

theorem hurZ_rhoBetaZ (i : Fin 24) (s b : Fin 2) (t' : T8) :
    (hurZ (rhoBetaZ i s b t') : ℍ[ℚ]) =
      hurZ (if b = 0 then smulH (sg s) (unitList.getD i.val ⟨1, 0, 0, 0⟩)
        else mulH oneI (smulH (sg s) (unitList.getD i.val ⟨1, 0, 0, 0⟩))) * twoRepQ t' := by
  rw [twoRepQ_eq, rhoBetaZ]
  split_ifs
  · rw [hurZ_smulH, hurZ_mulH, hurZ_smulH, smul_mul_assoc]
  · rw [hurZ_mulH, hurZ_smulH, hurZ_mulH, hurZ_mulH, hurZ_smulH]
    simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]

/-- **The test vector for `n ≡ 1 (mod 8)`.** -/
theorem testVector_one8 {n : ℕ} [NeZero n] (hsq : Squarefree n) (h1 : n % 8 = 1)
    {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]} (hτ : AdmissibleTau n τ) :
    ∃ f : ℍ[AQ] → ℤ, IsTestVector n τ f ∧ ∃ x : ℍ[AQ]ˣ, f x ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ := exists_isPlaceTwo
  obtain ⟨a, b, c, hvq, hn, h4⟩ := exists_abc hτ (Or.inl h1)
  obtain ⟨c', rfl⟩ := h4 h1
  set k := n / 8 with hkdef
  have hk : n = 8 * k + 1 := by have := Nat.div_add_mod n 8; rw [h1] at this; omega
  have hnk : ((8 * k + 1 : ℕ) : ℚ) = (a : ℚ) ^ 2 + (b : ℚ) ^ 2 + ((4 * c' : ℤ) : ℚ) ^ 2 := by
    rw [← hk]; exact_mod_cast hn
  set ωZ := ωH1 a b (4 * c') with hωZ
  set ω : ℍ[ℚ] := hurZ ωZ with hωdef
  have hωv : ω = τ (sqrtNeg n) := by rw [hvq, hωdef, hurZ_ωH1]
  have hω2 : ω * ω = -(((8 * k + 1 : ℕ) : ℚ)) • 1 := by
    rw [hωdef, hurZ_ωH1, hnk]; ext <;> simp <;> ring
  have hst : star ω = -ω := by rw [hωdef, hurZ_ωH1]; ext <;> simp
  have hϖn : Quaternion.normSq (1 + ω) = ((2 * (4 * k + 1) : ℕ) : ℚ) := by
    rw [hωdef, hurZ_ωH1, Quaternion.normSq_def']
    have : ((2 * (4 * k + 1) : ℕ) : ℚ) = 1 + ((8 * k + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [this, hnk]; simp; ring
  have hqω : qp 2 ω = ⟨0, ((a : ℚ) : ℚ_[2]), ((b : ℚ) : ℚ_[2]), (((4 * c' : ℤ) : ℚ) : ℚ_[2])⟩ := by
    rw [hωdef, hurZ_ωH1]; ext <;> simp [qp]
  have hABC : ((a : ℚ) : ℚ_[2]) ^ 2 + ((b : ℚ) : ℚ_[2]) ^ 2 + (((4 * c' : ℤ) : ℚ) : ℚ_[2]) ^ 2 =
      ((8 * k + 1 : ℕ) : ℚ_[2]) := by
    have := congrArg (fun q : ℚ => (q : ℚ_[2])) hnk; push_cast at this ⊢; rw [this]
  have hnrd : ∀ x z : ℚ_[2], Quaternion.normSq (x • (1 : ℍ[ℚ_[2]]) + z • qp 2 ω) =
      x ^ 2 + ((8 * k + 1 : ℕ) : ℚ_[2]) * z ^ 2 := by
    intro x z; rw [hqω, Quaternion.normSq_def', ← hABC]; simp; ring
  have hspan : ∀ x : 𝓞 (QNeg n), ∃ m s : ℤ, τ x = (m : ℍ[ℚ]) + (s : ℚ) • ω := by
    intro x; rw [hωv]; exact tau_span1 hsq h1 τ x
  set C := C1 ω k (isHurZ_hurZ _) hω2 hst hϖn hnrd with hCdef
  have hH : HgrpN n τ ≤ SgC v hv C := by
    refine HgrpN_le_SgC hv C (isHurZ_hurZ _) hspan ?_ ?_ ?_
    · intro p _ _ cc hcc; exact Or.inl ⟨cc, hcc, 1, by simp, isHur_one, by simp, InR.one⟩
    · intro p _ _ u hu hnu hR; exact Or.inl ⟨1, one_ne_zero, u, by simp, hu, hnu, hR⟩
    · intro p _ hp y hy hcomm
      subst hp
      rw [← hωv, hqω] at hcomm
      have h := loc_of_commute1 hABC (by rw [← hqω]; exact isHur_qp_hurZ' (isHurZ_hurZ _)) hy hcomm
      show Loc2OK (qp 2 ω) y ∨ Loc2OK (qp 2 ω) (y * qp 2 (1 + ω))
      rw [map_add, map_one, hqω]; exact h
  -- the table entry
  set r := mapH (Int.castRingHom (ZMod 8)) ωZ with hrdef
  obtain ⟨e, he, her⟩ := tab1_complete r.a0 r.a1 r.a2 r.a3
    (by show ((2 * (4 * c') : ℤ) : ZMod 8) = 2 * ((4 * c' : ℤ) : ZMod 8); push_cast; ring)
    (by show ((4 * c' : ℤ) : ZMod 8) = 0 ∨ ((4 * c' : ℤ) : ZMod 8) = 4
        push_cast; exact zmod8_four_mul _)
    (by
      show (((a - 4 * c' : ℤ) : ZMod 8) + ((4 * c' : ℤ) : ZMod 8)) ^ 2 +
        (((b - 4 * c' : ℤ) : ZMod 8) + ((4 * c' : ℤ) : ZMod 8)) ^ 2 + ((4 * c' : ℤ) : ZMod 8) ^ 2 = 1
      have h8 : (((a ^ 2 + b ^ 2 + (4 * c') ^ 2 : ℤ)) : ZMod 8) = 1 := by
        rw [← hn, hk]; push_cast; rw [show (8 : ZMod 8) = 0 from rfl]; ring
      push_cast at h8 ⊢; linear_combination h8)
  have her' : e.r = r := her
  sorry

end ZInQ.Contrib.HfxProof
