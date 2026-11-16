import ZInQKernel.Contrib.OneProof.HfxProof.Case3

/-!
# hfx-proof: the local condition at `2` for `n ≡ 1 (mod 8)` (ramified `K_2`)

Task hfx-proof. Here `ω = τ(√−n)` (`ω² = −n`) and `K_2 = ℚ_2(ω)` is ramified with uniformizer
`ϖ = 1 + ω` (`nrd ϖ = 1 + n`, of valuation one). `K_2^× = ℚ_2^× R_2^× ∪ ℚ_2^× R_2^× ϖ⁻¹`, where
`R_2 = ℤ_2 + ℤ_2ω + 4O_{B,2}`; the condition `C1` (`y ∈ ℚ_2^× R_2^×` or `yϖ ∈ ℚ_2^× R_2^×`) is a group
because conjugation by `ϖ` preserves `O_{B,2}` (`isHur_conj`: `ϖ̄ a ϖ ∈ 2O_{B,2}`, checked mod 2) and
`ϖ² ∈ ℚ_2^× R_2^×`.
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.HfxProof

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.T21Proof IsDedekindDomain NumberField
open scoped Quaternion
open ZInQ.RouteK.Rank5b

/-- Mod 2: an element of even norm `P` has `P̄ A P ≡ 0`. -/
theorem conj_mod_two : ∀ p0 p1 p2 p3 a0 a1 a2 a3 : ZMod 2, nrdH (⟨p0, p1, p2, p3⟩ : H4 (ZMod 2)) = 0 →
    mulH (mulH (starH ⟨p0, p1, p2, p3⟩) ⟨a0, a1, a2, a3⟩) ⟨p0, p1, p2, p3⟩ = (⟨0, 0, 0, 0⟩ : H4 (ZMod 2)) := by
  decide

theorem coords_Z2 {z : ℍ[ℚ_[2]]} (hz : IsHur (Zp 2) z) :
    ∃ Z : H4 ℤ_[2], mapH PadicInt.Coe.ringHom Z = hc z := by
  obtain ⟨h0, h1, h2, h3⟩ := hz
  exact ⟨⟨⟨_, mem_Zp.mp h0⟩, ⟨_, mem_Zp.mp h1⟩, ⟨_, mem_Zp.mp h2⟩, ⟨_, mem_Zp.mp h3⟩⟩, rfl⟩

theorem half_mem_of_toZMod {x : ℤ_[2]} (h : PadicInt.toZMod x = 0) :
    ((1 / 2 : ℚ) : ℚ_[2]) * (x : ℚ_[2]) ∈ Zp 2 := by
  have hm : x ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker]; exact h
  have hlt : ‖(x : ℚ_[2])‖ < 1 := by
    rw [← PadicInt.norm_def]; exact PadicInt.mem_nonunits.mp hm
  have hle := norm_le_inv_of_lt_one hlt
  rw [mem_Zp, norm_mul]
  have : ‖((1 / 2 : ℚ) : ℚ_[2])‖ = 2 := by
    push_cast; rw [norm_div, norm_one, show (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) by norm_num, Padic.norm_p]
    norm_num
  rw [this]; push_cast at hle; linarith

/-- **`ϖ̄ a ϖ ∈ 2O_{B,2}`** for `ϖ` of even norm. -/
theorem isHur_conj {ϖ a : ℍ[ℚ_[2]]} (hϖ : IsHur (Zp 2) ϖ) (hn : ‖Quaternion.normSq ϖ‖ < 1)
    (ha : IsHur (Zp 2) a) : IsHur (Zp 2) (((1 / 2 : ℚ) : ℚ_[2]) • (star ϖ * a * ϖ)) := by
  obtain ⟨Pz, hPz⟩ := coords_Z2 hϖ
  obtain ⟨A, hA⟩ := coords_Z2 ha
  have hnPz : PadicInt.toZMod (nrdH Pz) = 0 := by
    have hm : nrdH Pz ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
      refine PadicInt.mem_nonunits.mpr ?_
      rw [PadicInt.norm_def]
      have : ((nrdH Pz : ℤ_[2]) : ℚ_[2]) = Quaternion.normSq ϖ := by
        rw [normSq_eq_nrdH, ← hPz, ← map_nrdH]; rfl
      rw [this]; exact hn
    rw [← PadicInt.ker_toZMod] at hm; exact hm
  have hzero : mapH PadicInt.toZMod (mulH (mulH (starH Pz) A) Pz) = ⟨0, 0, 0, 0⟩ := by
    rw [mapH_mulH, mapH_mulH, mapH_starH]
    rw [map_nrdH] at hnPz
    exact conj_mod_two _ _ _ _ _ _ _ _ hnPz
  have hc' : hc (star ϖ * a * ϖ) = mapH PadicInt.Coe.ringHom (mulH (mulH (starH Pz) A) Pz) := by
    rw [hc_mul, hc_mul, hc_star, ← hPz, ← hA, mapH_mulH, mapH_mulH, mapH_starH]
  simp only [mapH, H4.mk.injEq] at hzero
  simp only [IsHur, hc_smul, hc', mapH]
  exact ⟨half_mem_of_toZMod hzero.1, half_mem_of_toZMod hzero.2.1, half_mem_of_toZMod hzero.2.2.1,
    half_mem_of_toZMod hzero.2.2.2⟩

/-- **Conjugation by `ϖ` preserves `O_{B,2}`** when `‖nrd ϖ‖ = 1/2`. -/
theorem isHur_qinv_conj {ϖ a : ℍ[ℚ_[2]]} (hϖ : IsHur (Zp 2) ϖ) (hn : ‖Quaternion.normSq ϖ‖ = 1 / 2)
    (ha : IsHur (Zp 2) a) : IsHur (Zp 2) (qinv ϖ * a * ϖ) := by
  have h0 : Quaternion.normSq ϖ ≠ 0 := by intro h; rw [h, norm_zero] at hn; norm_num at hn
  have e : qinv ϖ * a * ϖ = ((Quaternion.normSq ϖ)⁻¹ * 2) • (((1 / 2 : ℚ) : ℚ_[2]) • (star ϖ * a * ϖ)) := by
    rw [smul_smul, qinv, smul_mul_assoc, smul_mul_assoc]
    congr 1; push_cast; field_simp
  rw [e]
  refine IsHur.smul ?_ (isHur_conj hϖ (by rw [hn]; norm_num) ha)
  rw [mem_Zp, norm_mul, norm_inv, hn, show (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) by norm_num, Padic.norm_p]
  norm_num

section C1

variable {ω ϖ : ℍ[ℚ_[2]]} {N : ℚ_[2]}

theorem loc2OK_conj (hω : IsHur (Zp 2) ω) (hϖ : IsHur (Zp 2) ϖ) (hn : ‖Quaternion.normSq ϖ‖ = 1 / 2)
    (hcomm : ω * ϖ = ϖ * ω) {z : ℍ[ℚ_[2]]} (hz : Loc2OK ω z) :
    Loc2OK ω (qinv ϖ * z * ϖ) := by
  have h0 : Quaternion.normSq ϖ ≠ 0 := by intro h; rw [h, norm_zero] at hn; norm_num at hn
  have hQ1 : qinv ϖ * ϖ = 1 := qinv_mul_self h0
  have hQH : ∀ a, IsHur (Zp 2) a → IsHur (Zp 2) (qinv ϖ * a * ϖ) := fun a ha => isHur_qinv_conj hϖ hn ha
  generalize qinv ϖ = Q at hQ1 hQH ⊢
  obtain ⟨c, hc, u, rfl, hu, hnu, x, y, hx, hy, a, ha, rfl⟩ := hz
  have hqω : Q * ω * ϖ = ω := by rw [mul_assoc, hcomm, ← mul_assoc, hQ1, one_mul]
  have hq1 : Q * (1 : ℍ[ℚ_[2]]) * ϖ = 1 := by rw [mul_one, hQ1]
  have hconj : Q * (x • (1 : ℍ[ℚ_[2]]) + y • ω + (4 : ℚ_[2]) • a) * ϖ =
      x • (1 : ℍ[ℚ_[2]]) + y • ω + (4 : ℚ_[2]) • (Q * a * ϖ) := by
    rw [mul_add, mul_add, add_mul, add_mul, mul_smul_comm, mul_smul_comm, mul_smul_comm,
      smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, hq1, hqω]
  refine ⟨c, hc, Q * (x • (1 : ℍ[ℚ_[2]]) + y • ω + (4 : ℚ_[2]) • a) * ϖ,
    by rw [mul_smul_comm, smul_mul_assoc], hQH _ hu, ?_, x, y, hx, hy, Q * a * ϖ, hQH _ ha, hconj⟩
  have hn1 : Quaternion.normSq Q * Quaternion.normSq ϖ = 1 := by rw [← map_mul, hQ1, map_one]
  rw [map_mul, map_mul, mul_comm (Quaternion.normSq Q), mul_assoc, hn1, mul_one, hnu]

end C1

end ZInQ.Contrib.HfxProof
