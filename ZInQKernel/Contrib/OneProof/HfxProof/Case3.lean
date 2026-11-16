import ZInQKernel.Contrib.OneProof.HfxProof.Merge
import ZInQKernel.Contrib.OneProof.HfxProof.Finite3

/-!
# hfx-proof: the test vector for `n ≡ 3 (mod 8)`

Task hfx-proof. For squarefree `1 < n ≡ 3 (mod 8)` and admissible `τ`, `π_ℤ^{U_n}` has a nonzero generator
(`testVector_three`): `ω = (1 + τ(√−n))/2 ∈ O_B`, `K_{n,2}^× = ℚ_2^× ℤ_2[ω]^×`, and the table `tab3`
gives the two orbits of `K_{n,2}^×` on TYZ's 8 classes (sizes 2 and 6); the generator is `−3` on the
2-orbit and `1` on the 6-orbit.
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.HfxProof

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.T21Proof IsDedekindDomain NumberField
open scoped Quaternion
open ZInQ.RouteK.Rank5b

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-! ## Rank one -/

theorem sum_two_values (F G : T8 → ℤ) (hF : ∀ t, F t = -3 ∨ F t = 1) (a c : ℤ)
    (hG : ∀ t, G t = if F t = -3 then a else c) :
    ∑ t, G t = a * (Finset.univ.filter (fun t => F t = -3)).card +
      c * (Finset.univ.filter (fun t => ¬ F t = -3)).card := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t => F t = -3)]
  have e1 : ∑ t ∈ Finset.univ.filter (fun t => F t = -3), G t =
      ∑ t ∈ Finset.univ.filter (fun t => F t = -3), a :=
    Finset.sum_congr rfl (fun t ht => by rw [hG t, if_pos (Finset.mem_filter.mp ht).2])
  have e2 : ∑ t ∈ Finset.univ.filter (fun t => ¬ F t = -3), G t =
      ∑ t ∈ Finset.univ.filter (fun t => ¬ F t = -3), c :=
    Finset.sum_congr rfl (fun t ht => by rw [hG t, if_neg (Finset.mem_filter.mp ht).2])
  rw [e1, e2]
  simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem rank1_two (F G : T8 → ℤ) (hF : ∀ t, F t = -3 ∨ F t = 1) (hFs : ∑ t, F t = 0) {t1 : T8}
    (ht1 : F t1 = 1) (hG : ∀ t t', F t = F t' → G t = G t') (hGs : ∑ t, G t = 0) :
    ∃ c : ℤ, ∀ t, G t = c * F t := by
  classical
  have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset T8))
    (p := fun t => F t = -3)
  have hcard8 : (Finset.univ : Finset T8).card = 8 := rfl
  rw [hcard8] at hcard
  have hFs' := sum_two_values F F hF (-3) 1 (fun t => by rcases hF t with h | h <;> simp [h])
  rw [hFs] at hFs'
  have hS : (Finset.univ.filter (fun t => F t = -3)).card = 2 := by
    have : ((Finset.univ.filter (fun t => F t = -3)).card : ℤ) +
        (Finset.univ.filter (fun t => ¬ F t = -3)).card = 8 := by exact_mod_cast hcard
    have h2 : ((Finset.univ.filter (fun t => F t = -3)).card : ℤ) = 2 := by linarith
    exact_mod_cast h2
  obtain ⟨t0, ht0⟩ : (Finset.univ.filter (fun t => F t = -3)).Nonempty :=
    Finset.card_pos.mp (by rw [hS]; norm_num)
  have hF0 : F t0 = -3 := (Finset.mem_filter.mp ht0).2
  have hGs' := sum_two_values F G hF (G t0) (G t1) (fun t => by
    rcases hF t with h | h
    · rw [if_pos h]; exact hG t t0 (h.trans hF0.symm)
    · rw [if_neg (by rw [h]; norm_num)]; exact hG t t1 (h.trans ht1.symm))
  rw [hGs, hS] at hGs'
  have hS' : (Finset.univ.filter (fun t => ¬ F t = -3)).card = 6 := by omega
  rw [hS'] at hGs'
  refine ⟨G t1, fun t => ?_⟩
  rcases hF t with h | h
  · rw [hG t t0 (h.trans hF0.symm), h]; push_cast at hGs'; linarith
  · rw [hG t t1 (h.trans ht1.symm), h, mul_one]

/-! ## `ω` -/

/-- Hurwitz coordinates of `ω = (1 + a i + b j + c k)/2` for `a = 2a'+1`, `b = 2b'+1`, `c = 2c'+1`. -/
def ωH3 (a' b' c' : ℤ) : H4 ℤ := ⟨c' + 1, a' - c', b' - c', 2 * c' + 1⟩

theorem hurZ_ωH3 (a' b' c' : ℤ) :
    (hurZ (ωH3 a' b' c') : ℍ[ℚ]) = (1 / 2 : ℚ) • (1 + ⟨0, ((2 * a' + 1 : ℤ) : ℚ), ((2 * b' + 1 : ℤ) : ℚ),
      ((2 * c' + 1 : ℤ) : ℚ)⟩) := by
  ext <;> simp [hurZ, hur, ωH3, mapH] <;> ring

theorem isHurZ_hurZ (x : H4 ℤ) : IsHurZ (hurZ x : ℍ[ℚ]) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hc_hurZ, mapH] <;> exact mem_ZS.mpr ⟨_, rfl⟩

/-- The norm form `nrd(x + zω) = x² + xz + N z²`, `N` odd, is a unit when `x, z ∈ ℤ_2` are not both even. -/
theorem norm_quad_form {N : ℤ} (hN : Odd N) (t : ℤ_[2]) :
    ‖((1 + t + (N : ℤ_[2]) * t ^ 2 : ℤ_[2]) : ℚ_[2])‖ = 1 ∧
      ‖((t ^ 2 + t + (N : ℤ_[2]) : ℤ_[2]) : ℚ_[2])‖ = 1 := by
  have key : ∀ x : ℤ_[2], PadicInt.toZMod x ≠ 0 → ‖(x : ℚ_[2])‖ = 1 := by
    intro x hx
    rw [← PadicInt.norm_def, ← PadicInt.isUnit_iff]
    by_contra h
    have hm : x ∈ IsLocalRing.maximalIdeal ℤ_[2] := h
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hm
    exact hx hm
  have hN1 : (N : ZMod 2) = 1 := by
    obtain ⟨k, rfl⟩ := hN; push_cast
    rw [show (2 : ZMod 2) = 0 from rfl]; ring
  have h1 : ∀ a : ZMod 2, 1 + a + 1 * a ^ 2 ≠ 0 := by decide
  have h2 : ∀ a : ZMod 2, a ^ 2 + a + 1 ≠ 0 := by decide
  constructor
  · refine key _ ?_
    simp only [map_add, map_one, map_mul, map_pow, map_intCast, hN1]
    exact h1 _
  · refine key _ ?_
    simp only [map_add, map_pow, map_intCast, hN1]
    exact h2 _

end ZInQ.Contrib.HfxProof
