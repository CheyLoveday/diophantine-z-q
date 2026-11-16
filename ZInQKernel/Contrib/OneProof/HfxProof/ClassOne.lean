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

/-! ## The induction -/

theorem exists_nat_approx {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : x ∈ Zp p) :
    ∃ k : ℕ, k < p ∧ ‖x - k‖ ≤ (p : ℝ)⁻¹ := by
  obtain ⟨k, hk, hm⟩ := PadicInt.exists_mem_range (⟨x, mem_Zp.mp hx⟩ : ℤ_[p])
  refine ⟨k, hk, norm_le_inv_of_lt_one ?_⟩
  have := PadicInt.mem_nonunits.mp ((IsLocalRing.mem_maximalIdeal _).mp hm)
  rw [PadicInt.norm_def] at this
  exact this

/-- `nrd (a + c b) = nrd a + c (L(a, b) + c nrd b)` in Hurwitz coordinates. -/
def linH {A : Type*} [CommRing A] (a b : H4 A) : A :=
  2 * a.a3 * b.a3 + a.a2 * b.a3 + a.a3 * b.a2 + 2 * a.a2 * b.a2 + a.a1 * b.a3 + a.a3 * b.a1 +
    2 * a.a1 * b.a1 - a.a0 * b.a3 - a.a3 * b.a0 + 2 * a.a0 * b.a0

theorem nrdH_add_smul {A : Type*} [CommRing A] (a b : H4 A) (c : A) :
    nrdH (⟨a.a0 + c * b.a0, a.a1 + c * b.a1, a.a2 + c * b.a2, a.a3 + c * b.a3⟩ : H4 A) =
      nrdH a + c * (linH a b + c * nrdH b) := by
  simp only [nrdH, linH]; ring

/-- `‖nrd (a + p b) - nrd a‖ < 1` for Hurwitz `a`, `b`. -/
theorem norm_normSq_add_smul_sub_lt {p : ℕ} [Fact p.Prime] {a b : ℍ[ℚ_[p]]} (ha : IsHur (Zp p) a)
    (hb : IsHur (Zp p) b) :
    ‖Quaternion.normSq (a + (p : ℚ_[p]) • b) - Quaternion.normSq a‖ < 1 := by
  obtain ⟨A, hA⟩ := isHur_iff.mp ha
  obtain ⟨B, hB⟩ := isHur_iff.mp hb
  have hpZ : (p : ℚ_[p]) ∈ Zp p := by simpa [mem_Zp] using Padic.norm_natCast_le_one (p := p) p
  have hc' : hc (a + (p : ℚ_[p]) • b) = mapH (Zp p).subtype
      ⟨A.a0 + ⟨p, hpZ⟩ * B.a0, A.a1 + ⟨p, hpZ⟩ * B.a1, A.a2 + ⟨p, hpZ⟩ * B.a2, A.a3 + ⟨p, hpZ⟩ * B.a3⟩ := by
    rw [hc_add, hc_smul, hA, hB]; simp [mapH]
  rw [normSq_eq_nrdH, normSq_eq_nrdH, hc', hA, ← map_nrdH, ← map_nrdH, nrdH_add_smul, map_add,
    add_sub_cancel_left, map_mul]
  have h1 : ‖((Zp p).subtype ⟨p, hpZ⟩ : ℚ_[p])‖ < 1 := by
    change ‖(p : ℚ_[p])‖ < 1
    rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have h2 : ‖((Zp p).subtype (linH A B + ⟨p, hpZ⟩ * nrdH B) : ℚ_[p])‖ ≤ 1 := (linH A B + _).2
  rw [norm_mul]
  calc _ ≤ ‖((Zp p).subtype ⟨p, hpZ⟩ : ℚ_[p])‖ * 1 := by gcongr
    _ < 1 := by rw [mul_one]; exact h1

theorem natCast_mul_eq_smul' {R : Type*} [CommRing R] (n : ℕ) (b : ℍ[R]) :
    (n : ℍ[R]) * b = (n : R) • b := by
  rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul R]

theorem qp_natCast {p : ℕ} [Fact p.Prime] (n : ℕ) : qp p (n : ℍ[ℚ]) = (n : ℍ[ℚ_[p]]) := map_natCast _ n

theorem norm_p_lt_one {p : ℕ} [Fact p.Prime] : ‖(p : ℚ_[p])‖ < 1 := by
  rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

/-- **One descent step exists, locally**: for a Hurwitz `z ∈ ℍ[ℚ_p]` of non-unit norm and `m` with
`m / nrd z ∈ ℤ_p`, a global `γ` of norm `p^e` (`e ≥ 1`) with `γ⁻¹ z` Hurwitz and `p^e ∣ m`. -/
theorem exists_descent_local {p : ℕ} [Fact p.Prime] {z : ℍ[ℚ_[p]]} (hz : IsHur (Zp p) z)
    (hlt : ‖Quaternion.normSq z‖ < 1) {m : ℕ} (hm : ‖((m : ℤ) : ℚ_[p])‖ ≤ ‖Quaternion.normSq z‖) :
    ∃ γ : ℍ[ℚ], ∃ _ : γ ≠ 0, IsHurZ γ ∧ ∃ e : ℕ, 1 ≤ e ∧ Quaternion.normSq γ = (p : ℚ) ^ e ∧
      IsHur (Zp p) (qp p γ⁻¹ * z) ∧ p ^ e ∣ m := by
  have hpp : p.Prime := Fact.out
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hpm : (p : ℤ) ∣ (m : ℤ) := Padic.norm_intCast_lt_one_iff.mp (lt_of_le_of_lt hm hlt)
  obtain ⟨h0, h1, h2, h3⟩ := hz
  obtain ⟨k0, hk0, e0⟩ := exists_nat_approx h0
  obtain ⟨k1, hk1, e1⟩ := exists_nat_approx h1
  obtain ⟨k2, hk2, e2⟩ := exists_nat_approx h2
  obtain ⟨k3, hk3, e3⟩ := exists_nat_approx h3
  set β : ℍ[ℚ] := hur ⟨(k0 : ℚ), (k1 : ℚ), (k2 : ℚ), (k3 : ℚ)⟩ with hβdef
  have hcβ : hc (qp p β) = ⟨(k0 : ℚ_[p]), k1, k2, k3⟩ := by
    rw [qp, hc_qmap, hβdef, hc_hur]; simp [mapH]
  set z' : ℍ[ℚ_[p]] := (p : ℚ_[p])⁻¹ • (z - qp p β) with hz'def
  have hzdec : z = qp p β + (p : ℚ_[p]) • z' := by
    rw [hz'def, smul_smul, mul_inv_cancel₀ hp0, one_smul]; abel
  have hpinv : ‖(p : ℚ_[p])⁻¹‖ = p := by rw [norm_inv, Padic.norm_p, inv_inv]
  have hcoord : ∀ (x : ℚ_[p]) (k : ℕ), ‖x - k‖ ≤ (p : ℝ)⁻¹ → (p : ℚ_[p])⁻¹ * (x - k) ∈ Zp p := by
    intro x k hk
    rw [mem_Zp, norm_mul, hpinv]
    have hp0' : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    calc (p : ℝ) * ‖x - k‖ ≤ p * (p : ℝ)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hp0'.ne'
  have hz' : IsHur (Zp p) z' := by
    have : hc z' = ⟨(p : ℚ_[p])⁻¹ * ((hc z).a0 - k0), (p : ℚ_[p])⁻¹ * ((hc z).a1 - k1),
        (p : ℚ_[p])⁻¹ * ((hc z).a2 - k2), (p : ℚ_[p])⁻¹ * ((hc z).a3 - k3)⟩ := by
      rw [hz'def, hc_smul, hc_sub, hcβ]
    simp only [IsHur, this]
    exact ⟨hcoord _ _ e0, hcoord _ _ e1, hcoord _ _ e2, hcoord _ _ e3⟩
  have hβZ : IsHurZ β := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hβdef, hc_hur] <;> exact mem_ZS.mpr ⟨_, by norm_cast⟩
  have hqβ : IsHur (Zp p) (qp p β) := isHur_qp_hurZ' hβZ
  by_cases hk : k0 = 0 ∧ k1 = 0 ∧ k2 = 0 ∧ k3 = 0
  · -- `z ∈ p O_{B,p}`: divide by `p`
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hk
    have hβ0 : β = 0 := by
      rw [hβdef]; apply hc_injective; rw [hc_hur]; ext <;> simp [hc]
    rw [hβ0, map_zero, zero_add] at hzdec
    refine ⟨(p : ℍ[ℚ]), ?_, isHurZ_natCast p, 2, by norm_num, by rw [Quaternion.normSq_natCast], ?_, ?_⟩
    · intro h
      have := congrArg Quaternion.normSq h
      rw [Quaternion.normSq_natCast, map_zero] at this
      exact hpp.ne_zero (by exact_mod_cast pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
    · rw [qp_inv, Quaternion.normSq_natCast, qp_natCast, star_natCast, hzdec, smul_mul_assoc,
        natCast_mul_eq_smul', smul_smul, smul_smul]
      have : ((((p : ℚ) ^ 2 : ℚ) : ℚ_[p]))⁻¹ * (p : ℚ_[p]) * (p : ℚ_[p]) = 1 := by
        push_cast; field_simp
      rw [this, one_smul]; exact hz'
    · have hn : ‖Quaternion.normSq z‖ ≤ (p : ℝ) ^ (-(2 : ℕ) : ℤ) := by
        rw [hzdec, Quaternion.normSq_smul, norm_mul, norm_pow, Padic.norm_p]
        have := hz'.normSq_mem
        rw [mem_Zp] at this
        calc (p : ℝ)⁻¹ ^ 2 * ‖Quaternion.normSq z'‖ ≤ (p : ℝ)⁻¹ ^ 2 * 1 := by gcongr
          _ = (p : ℝ) ^ (-(2 : ℕ) : ℤ) := by rw [mul_one, zpow_neg, zpow_natCast, inv_pow]
      have := (Padic.norm_int_le_pow_iff_dvd (p := p) (m : ℤ) 2).mp (hm.trans hn)
      exact_mod_cast this
  · -- `β ∉ p O_B`: Euclid
    have hnot : ¬ IsHurZ ((p : ℚ)⁻¹ • β) := by
      intro h
      apply hk
      have key : ∀ k : ℕ, k < p → ((p : ℚ)⁻¹ * k) ∈ ZS → k = 0 := by
        intro k hkp hmem
        obtain ⟨j, hj⟩ := mem_ZS.mp hmem
        have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hpp.ne_zero
        have : (k : ℚ) = p * j := by rw [hj]; field_simp
        have hkj : (k : ℤ) = p * j := by exact_mod_cast this
        have : 0 ≤ j := by
          by_contra hneg; push_neg at hneg
          have : (p : ℤ) * j < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hpp.pos) hneg
          omega
        rcases this.lt_or_eq with hj0 | hj0
        · have : (p : ℤ) ≤ p * j := le_mul_of_one_le_right (by positivity) (by omega)
          omega
        · rw [← hj0, mul_zero] at hkj; exact_mod_cast hkj
      obtain ⟨g0, g1, g2, g3⟩ := h
      simp only [hc_smul, hβdef, hc_hur] at g0 g1 g2 g3
      exact ⟨key _ hk0 g0, key _ hk1 g1, key _ hk2 g2, key _ hk3 g3⟩
    have hdvdβ : ∃ k : ℤ, Quaternion.normSq β = (p : ℚ) * k := by
      obtain ⟨N, hN⟩ := hβZ.normSq_int
      have hNp : ‖((N : ℤ) : ℚ_[p])‖ < 1 := by
        have e := norm_normSq_add_smul_sub_lt hqβ hz'
        rw [← hzdec] at e
        have hq : Quaternion.normSq (qp p β) = ((N : ℤ) : ℚ_[p]) := by
          rw [normSq_qp, hN, Rat.cast_intCast]
        rw [hq] at e
        have e' : ‖((N : ℤ) : ℚ_[p]) - Quaternion.normSq z‖ < 1 := by
          rw [← norm_neg, neg_sub]; exact e
        calc ‖((N : ℤ) : ℚ_[p])‖ = ‖(((N : ℤ) : ℚ_[p]) - Quaternion.normSq z) + Quaternion.normSq z‖ := by
              rw [sub_add_cancel]
          _ ≤ max ‖((N : ℤ) : ℚ_[p]) - Quaternion.normSq z‖ ‖Quaternion.normSq z‖ :=
              Padic.nonarchimedean _ _
          _ < 1 := max_lt e' hlt
      obtain ⟨k, hk⟩ := Padic.norm_intCast_lt_one_iff.mp hNp
      exact ⟨k, by rw [hN, hk]; push_cast; ring⟩
    obtain ⟨γ, hγZ, hγn, hγβ, hγp⟩ := euclid_prime hβZ hpp hdvdβ hnot
    have hγ0 : γ ≠ 0 := by
      intro h; rw [h, map_zero] at hγn; exact hpp.ne_zero (by exact_mod_cast hγn.symm)
    refine ⟨γ, hγ0, hγZ, 1, le_rfl, by rw [hγn, pow_one], ?_, by rw [pow_one]; exact_mod_cast hpm⟩
    have : qp p γ⁻¹ * z = qp p (γ⁻¹ * β) + qp p (γ⁻¹ * (p : ℍ[ℚ])) * z' := by
      rw [hzdec, map_mul, map_mul, qp_natCast, mul_add, mul_assoc, natCast_mul_eq_smul']
    rw [this]
    exact (isHur_qp_hurZ' hγβ).add ((isHur_qp_hurZ' hγp).mul hz')

end ZInQ.Contrib.HfxProof
