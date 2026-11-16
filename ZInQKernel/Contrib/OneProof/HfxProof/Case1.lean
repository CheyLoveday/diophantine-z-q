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

end ZInQ.Contrib.HfxProof
