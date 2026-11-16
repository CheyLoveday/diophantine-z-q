import ZInQKernel.Contrib.OneProof.HfxProof.Euclid
import ZInQKernel.Contrib.OneProof.T21Proof.Brandt2

/-!
# hfx-proof: `B̂^× = B^× Ô_B^×` (the Hurwitz order has class number one)

Task hfx-proof. Every unit `x` of `B̂ = ℍ[𝔸ᶠ_ℚ]` is `qι γ · u` with `γ ∈ B^×` and `u ∈ Ô_B^×`
(`exists_global_mul_unit`): scale `x` into `Ô_B`, then divide by global elements of prime norm
(`euclid_prime`) until the reduced norm is a local unit everywhere. Ô_B is read place by place
(`LH`, Hurwitz at every place).
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.HfxProof

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.T21Proof IsDedekindDomain NumberField
open scoped Quaternion
open ZInQ.RouteK.Rank5b

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- `y ∈ Ô_B`, read place by place. -/
def LH (y : ℍ[AQ]) : Prop := ∀ w : HeightOneSpectrum (𝓞 ℚ), IsHur (Zp (Pw w : ℕ)) (piQ w y)

theorem normSq_qmap {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (q : ℍ[A]) :
    Quaternion.normSq (qmap f q) = f (Quaternion.normSq q) := by
  simp [Quaternion.normSq_def', qmap]

theorem normSq_qp {p : ℕ} [Fact p.Prime] (γ : ℍ[ℚ]) :
    Quaternion.normSq (qp p γ) = ((Quaternion.normSq γ : ℚ) : ℚ_[p]) := by
  rw [qp, normSq_qmap]; rfl

theorem qp_inv {p : ℕ} [Fact p.Prime] (γ : ℍ[ℚ]) :
    qp p γ⁻¹ = ((Quaternion.normSq γ : ℚ) : ℚ_[p])⁻¹ • star (qp p γ) := by
  rw [Quaternion.inv_def, qp_smul, qp, qmap_star]; push_cast; rfl

theorem isHur_of_norm_coords {p : ℕ} [Fact p.Prime] {y : ℍ[ℚ_[p]]} (h0 : ‖y.re‖ ≤ 1)
    (h1 : ‖y.imI‖ ≤ 1) (h2 : ‖y.imJ‖ ≤ 1) (h3 : ‖y.imK‖ ≤ 1) : IsHur (Zp p) y := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Zp p).add_mem (mem_Zp.mpr h0) (mem_Zp.mpr h3)
  · exact (Zp p).sub_mem (mem_Zp.mpr h1) (mem_Zp.mpr h3)
  · exact (Zp p).sub_mem (mem_Zp.mpr h2) (mem_Zp.mpr h3)
  · exact (Zp p).mul_mem (by simpa [mem_Zp] using Padic.norm_int_le_one (p := p) 2) (mem_Zp.mpr h3)

/-- The inverse of a Hurwitz element of unit norm is Hurwitz. -/
theorem isHur_inv_of_norm_one {p : ℕ} [Fact p.Prime] {y : ℍ[ℚ_[p]]} (hy : IsHur (Zp p) y)
    (hn : ‖Quaternion.normSq y‖ = 1) : IsHur (Zp p) y⁻¹ := by
  rw [Quaternion.inv_def]; exact isHur_inv_star hy hn

theorem norm_normSq_le_one {p : ℕ} [Fact p.Prime] {y : ℍ[ℚ_[p]]} (hy : IsHur (Zp p) y) :
    ‖Quaternion.normSq y‖ ≤ 1 := hy.normSq_mem

/-- A prime `ℓ ≠ p` power `p^e` is an `ℓ`-adic unit. -/
theorem norm_prime_pow_ne {ℓ p e : ℕ} [Fact ℓ.Prime] (hp : p.Prime) (hne : p ≠ ℓ) :
    ‖((p : ℚ_[ℓ]) ^ e)‖ = 1 := by
  rw [norm_pow]
  have : ‖(p : ℚ_[ℓ])‖ = 1 := by
    have h := Padic.norm_natCast_eq_one_iff (p := ℓ) (n := p)
    exact h.mpr ((Nat.coprime_primes Fact.out hp).mpr hne.symm)
  rw [this, one_pow]

theorem isHur_qp_hurZ' {p : ℕ} [Fact p.Prime] {γ : ℍ[ℚ]} (h : IsHurZ γ) : IsHur (Zp p) (qp p γ) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  obtain ⟨m0, e0⟩ := mem_ZS.mp h0
  obtain ⟨m1, e1⟩ := mem_ZS.mp h1
  obtain ⟨m2, e2⟩ := mem_ZS.mp h2
  obtain ⟨m3, e3⟩ := mem_ZS.mp h3
  simp only [IsHur, qp, hc_qmap, mapH, ← e0, ← e1, ← e2, ← e3, map_intCast, mem_Zp]
  exact ⟨Padic.norm_int_le_one _, Padic.norm_int_le_one _, Padic.norm_int_le_one _,
    Padic.norm_int_le_one _⟩

/-- `Cond m y`: `m / nrd(y_w)` is integral at every place. -/
def Cond (m : ℕ) (y : ℍ[AQ]) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 ℚ), ‖((m : ℤ) : ℚ_[Pw w])‖ ≤ ‖Quaternion.normSq (piQ w y)‖

theorem normSq_piQ_unit_ne_zero (w : HeightOneSpectrum (𝓞 ℚ)) (y : ℍ[AQ]ˣ) :
    Quaternion.normSq (piQ w (y : ℍ[AQ])) ≠ 0 := by
  intro h
  have := congrArg (fun z => Quaternion.normSq (piQ w z)) y.mul_inv
  simp only [map_mul, map_one, h, zero_mul] at this
  exact zero_ne_one this

theorem piQ_unit_inv (w : HeightOneSpectrum (𝓞 ℚ)) (y : ℍ[AQ]ˣ) :
    piQ w ((y⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) =
      (Quaternion.normSq (piQ w (y : ℍ[AQ])))⁻¹ • star (piQ w (y : ℍ[AQ])) := by
  have h : ((1 : ℚ_[Pw w]) • piQ w (y : ℍ[AQ])) * piQ w ((y⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) = 1 := by
    rw [one_smul, ← map_mul, Units.mul_inv, map_one]
  rw [eq_of_mul_eq_one one_ne_zero (normSq_piQ_unit_ne_zero w y) h, inv_one, one_smul]

theorem piQ_unit_ne_zero (w : HeightOneSpectrum (𝓞 ℚ)) (y : ℍ[AQ]ˣ) : piQ w (y : ℍ[AQ]) ≠ 0 := by
  intro h
  have := congrArg (piQ w) y.mul_inv
  rw [map_mul, h, zero_mul, map_one] at this
  exact zero_ne_one this

/-- `qι γ` as a unit. -/
def qιU (γ : ℍ[ℚ]) (hγ : γ ≠ 0) : ℍ[AQ]ˣ :=
  ⟨qι γ, qι γ⁻¹, by rw [← map_mul, mul_inv_cancel₀ hγ, map_one],
    by rw [← map_mul, inv_mul_cancel₀ hγ, map_one]⟩

/-- **The descent step.** Dividing `y` by a global `γ` of norm `p^e` that is integral against `y` at
`p` and with `p^e ∣ m` keeps `y` in `Ô_B` and lowers `m` to `m / p^e`. -/
theorem descent_step {m : ℕ} {y : ℍ[AQ]ˣ} (hy : LH y) (hm : Cond m y) {w₀ : HeightOneSpectrum (𝓞 ℚ)}
    {γ : ℍ[ℚ]} (hγ0 : γ ≠ 0) (hγZ : IsHurZ γ) {e : ℕ}
    (hγn : Quaternion.normSq γ = ((Pw w₀ : ℕ) : ℚ) ^ e)
    (hloc : IsHur (Zp (Pw w₀ : ℕ)) (qp (Pw w₀ : ℕ) γ⁻¹ * piQ w₀ y))
    (hdvd : (Pw w₀ : ℕ) ^ e ∣ m) :
    LH (((qιU γ hγ0)⁻¹ * y : ℍ[AQ]ˣ) : ℍ[AQ]) ∧
      Cond (m / (Pw w₀ : ℕ) ^ e) (((qιU γ hγ0)⁻¹ * y : ℍ[AQ]ˣ) : ℍ[AQ]) := by
  have hcoe : (((qιU γ hγ0)⁻¹ * y : ℍ[AQ]ˣ) : ℍ[AQ]) = qι γ⁻¹ * y := rfl
  rw [hcoe]
  set p : ℕ := (Pw w₀ : ℕ) with hpdef
  have hpp : p.Prime := (Pw w₀).2
  constructor
  · intro w
    rw [map_mul, piQ_qι]
    by_cases hw : w = w₀
    · subst hw; exact hloc
    · have hne : p ≠ (Pw w : ℕ) := by
        intro h; exact hw (eq_of_Pw_eq h.symm)
      refine IsHur.mul ?_ (hy w)
      rw [qp_inv, hγn]
      refine IsHur.smul ?_ (isHur_qp_hurZ' hγZ).star
      rw [mem_Zp, norm_inv]; push_cast; rw [norm_prime_pow_ne hpp hne, inv_one]
  · intro w
    rw [map_mul, map_mul, piQ_qι, normSq_qp, Quaternion.normSq_inv, hγn, norm_mul]
    have hm' := hm w
    obtain ⟨k, hk⟩ := hdvd
    have hdiv : m / p ^ e = k := by
      rw [hk]; exact Nat.mul_div_cancel_left k (pow_pos hpp.pos e)
    rw [hdiv]
    rw [hk] at hm'
    push_cast at hm' ⊢
    rw [norm_mul] at hm'
    have hpe : ‖((p : ℚ_[Pw w]) ^ e)‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; exact pow_ne_zero _ (by exact_mod_cast hpp.ne_zero)
    rw [norm_inv]
    rw [le_inv_mul_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hpe))]
    exact hm'

end ZInQ.Contrib.HfxProof
