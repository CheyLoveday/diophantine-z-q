import ZInQKernel.Contrib.OneProof.EichlerBound.Count

/-! eichler-bound, part B8: inertness when two types occur, and **the count**
`#(Emb(R, 𝒪)/𝒪^×) ≤ 2^{b(k)} · #Pic(R)`. No `sorry`. -/

set_option linter.style.longLine false

noncomputable section

namespace EichlerBound

open LeafQM LeafQM.AV GRCountX6 NumberField

section Emb

variable {k : Type} [Field k] [NumberField k] {R : Subring k} (Bs : QBasis R)

theorem coprime_conductor (hc : Nat.Coprime (conductor R) 6) {ℓ : ℤ} (hℓ : L6 ℓ) :
    IsCoprime (conductor R : ℤ) ℓ := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  rcases hℓ with rfl | rfl
  · have : Nat.Coprime (conductor R) 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hc
    exact_mod_cast this
  · have : Nat.Coprime (conductor R) 3 := Nat.Coprime.coprime_dvd_right (by norm_num) hc
    exact_mod_cast this

include Bs in
/-- An element `z ∈ 𝒪_k` with `Ψ(f z) ∈ P_ℓ` is divisible by `ℓ` in `𝒪_k`, unless `Ψ(ω)` is congruent to an
integer modulo `P_ℓ`. -/
theorem dvd_of_PP (hR : R ≤ (integralClosure ℤ k).toSubring) (hc : Nat.Coprime (conductor R) 6)
    (Ψ : OptEmb k R) {ℓ : ℤ} (hℓ : L6 ℓ) (h : ∀ m : ℤ, ¬ PP ℓ (Ψ.1 Bs.ω - ((m : ℚ) : B)))
    (z : 𝓞 k) (hz : PP ℓ (Ψ.1 ((conductor R : ℤ) • (z : k)))) : ((ℓ : ℤ) : 𝓞 k) ∣ z := by
  have hβ0 := emb_omega_mem Bs Ψ
  have hfz := conductor_smul_mem R (RingOfIntegers.isIntegral_coe z)
  obtain ⟨X, Y, hXY⟩ := Bs.span _ hfz
  have hlin : Ψ.1 ((conductor R : ℤ) • (z : k)) = ((X : ℚ) : B) + ((Y : ℚ) : B) * Ψ.1 Bs.ω := by
    rw [hXY, show ((X : k)) = ((X : ℚ) : k) by push_cast; rfl,
      show ((Y : k)) = ((Y : ℚ) : k) by push_cast; rfl, emb_lin]
  rw [hlin] at hz
  have hY : ℓ ∣ Y := by
    by_contra hnd
    have hc2 : IsCoprime ℓ Y := (Irreducible.coprime_iff_not_dvd (L6_prime hℓ).irreducible).mpr hnd
    obtain ⟨v, u, huv⟩ := hc2
    apply h (-(u * X))
    have huv' : ((v : ℚ) * ℓ + u * Y) = 1 := by exact_mod_cast huv
    have e : Ψ.1 Bs.ω - (((-(u * X) : ℤ) : ℚ) : B) =
        ((u : ℚ) : B) * (((X : ℚ) : B) + ((Y : ℚ) : B) * Ψ.1 Bs.ω) + (ℓ : ℚ) • ((v : ℚ) • Ψ.1 Bs.ω) := by
      refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp
      · linear_combination (-(Ψ.1 Bs.ω).re) * huv'
      · linear_combination (-(Ψ.1 Bs.ω).imI) * huv'
      · linear_combination (-(Ψ.1 Bs.ω).imJ) * huv'
      · linear_combination (-(Ψ.1 Bs.ω).imK) * huv'
    rw [e]
    exact PP_add hℓ (PP_mul_left (intCast_mem u) hz) (PP_of_LO (LO_of_smul (smul_mem_O hβ0 v)))
  obtain ⟨Y', rfl⟩ := hY
  have hX : ℓ ∣ X := by
    apply dvd_of_PP_int hℓ
    have : ((X : ℚ) : B) = (((X : ℚ) : B) + (((ℓ * Y' : ℤ) : ℚ) : B) * Ψ.1 Bs.ω) -
        (ℓ : ℚ) • ((Y' : ℚ) • Ψ.1 Bs.ω) := by
      rw [smul_smul, ← coe_mul_eq_smul]; push_cast; abel
    rw [this]
    exact PP_sub hℓ hz (PP_of_LO (LO_of_smul (smul_mem_O hβ0 Y')))
  obtain ⟨X', rfl⟩ := hX
  obtain ⟨u', v', huv'⟩ := coprime_conductor hc hℓ
  have hrR : (X' : k) + (Y' : k) * Bs.ω ∈ R :=
    R.add_mem (_root_.intCast_mem R X') (R.mul_mem (_root_.intCast_mem R Y') Bs.mem)
  obtain ⟨r', hr'⟩ : ∃ r' : 𝓞 k, (r' : k) = (X' : k) + (Y' : k) * Bs.ω := ⟨⟨_, hR hrR⟩, rfl⟩
  refine ⟨(u' : 𝓞 k) * r' + (v' : 𝓞 k) * z, ?_⟩
  apply RingOfIntegers.ext
  have hf : ((conductor R : ℤ) : k) * (z : k) = (ℓ : k) * ((X' : k) + (Y' : k) * Bs.ω) := by
    rw [← zsmul_eq_mul, hXY]; push_cast; ring
  have huv'' : (u' : k) * (conductor R : ℤ) + (v' : k) * ℓ = 1 := by exact_mod_cast huv'
  show (z : k) = algebraMap (𝓞 k) k (((ℓ : ℤ) : 𝓞 k) * ((u' : 𝓞 k) * r' + (v' : 𝓞 k) * z))
  rw [map_mul, map_add, map_mul, map_mul, map_intCast, map_intCast, map_intCast]
  change (z : k) = (ℓ : k) * ((u' : k) * (r' : k) + (v' : k) * (z : k))
  rw [hr']
  linear_combination (-(z : k)) * huv'' + (u' : k) * hf

include Bs in
/-- **Inertness**: if `Ψ(ω)` is not congruent to an integer modulo `P_ℓ`, then `ℓ 𝒪_k` is prime. -/
theorem inert_of_noint (hR : R ≤ (integralClosure ℤ k).toSubring) (hc : Nat.Coprime (conductor R) 6)
    (Ψ : OptEmb k R) {ℓ : ℤ} (hℓ : L6 ℓ) (h : ∀ m : ℤ, ¬ PP ℓ (Ψ.1 Bs.ω - ((m : ℚ) : B))) :
    (Ideal.span {((ℓ : ℤ) : 𝓞 k)}).IsPrime := by
  have hℓ0 := L6_ne hℓ
  have hℓq : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ0
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨e', he⟩ := hu.exists_right_inv
    have hk : (ℓ : k) * (e' : k) = 1 := by
      have := congrArg (fun x : 𝓞 k => (x : k)) he
      simpa using this
    have he'R : (e' : k) ∈ R := mem_of_ell_mul R hc hℓ (RingOfIntegers.isIntegral_coe e')
      (by rw [hk]; exact R.one_mem)
    have hΨ := (optEmb_mem Ψ _).2 he'R
    have : (e' : k) = (((ℓ : ℚ)⁻¹ : ℚ) : k) := by
      rw [eq_inv_of_mul_eq_one_right hk]; push_cast; rfl
    rw [this, emb_ratCast] at hΨ
    obtain ⟨w, hw⟩ := rat_mem_O hΨ
    have h1 : (ℓ : ℚ) * w = 1 := by rw [← hw, mul_inv_cancel₀ hℓq]
    have h2 : ℓ * w = 1 := by exact_mod_cast h1
    have := Int.eq_one_of_mul_eq_one_right (by rcases hℓ with rfl | rfl <;> norm_num) h2
    rcases hℓ with rfl | rfl <;> norm_num at this
  · intro x y hxy
    rw [Ideal.mem_span_singleton] at hxy ⊢
    rw [Ideal.mem_span_singleton]
    obtain ⟨w, hw⟩ := hxy
    have hwk : (x : k) * (y : k) = (ℓ : k) * (w : k) := by
      have := congrArg (fun t : 𝓞 k => (t : k)) hw
      simpa using this
    have hfx := conductor_smul_mem R (RingOfIntegers.isIntegral_coe x)
    have hfy := conductor_smul_mem R (RingOfIntegers.isIntegral_coe y)
    have hfw := conductor_smul_mem R (RingOfIntegers.isIntegral_coe w)
    have hprod : PP ℓ (Ψ.1 ((conductor R : ℤ) • (x : k)) * Ψ.1 ((conductor R : ℤ) • (y : k))) := by
      apply PP_of_LO
      rw [← map_mul, LO_iff_smul ℓ hℓ0]
      refine ⟨Ψ.1 (((conductor R : ℤ) : k) * ((conductor R : ℤ) • (w : k))),
        (optEmb_mem Ψ _).2 (R.mul_mem (_root_.intCast_mem R _) hfw), ?_⟩
      have e : ((conductor R : ℤ) • (x : k)) * ((conductor R : ℤ) • (y : k)) =
          ((ℓ : ℚ) : k) * (((conductor R : ℤ) : k) * ((conductor R : ℤ) • (w : k))) := by
        simp only [zsmul_eq_mul]; push_cast; linear_combination ((conductor R : k)) ^ 2 * hwk
      rw [e, map_mul, emb_ratCast, coe_mul_eq_smul]
    rcases PP_prime (L6_prime hℓ) ((optEmb_mem Ψ _).2 hfx) ((optEmb_mem Ψ _).2 hfy) hprod with h1 | h1
    · left; exact dvd_of_PP Bs hR hc Ψ hℓ h x h1
    · right; exact dvd_of_PP Bs hR hc Ψ hℓ h y h1

end Emb

end EichlerBound
