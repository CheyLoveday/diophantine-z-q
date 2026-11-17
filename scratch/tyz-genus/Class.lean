import ZInQKernel.Contrib.OneProof.TYZGenusFold.Jacobi
import ZInQKernel.Contrib.OneProof.TYZGenusFold.Local
import ZInQKernel.Contrib.OneProof.TYZGenusFold.Ideles

/-!
# tyz-genus: `f_n` vanishes on the classes with `χ_U = Π_{q ∣ n} χ_q = −1` (`n ≡ 1 (mod 8)`), and TYZ Lemma 2.8

For a class `t` take an integral ideal `I ∈ t` with `N I` prime to `2n`, an `α ∈ I` with `(α) = I M`,
`M + (N I) = O`, and the idele `a = aK (N I) α` (class `[I] = t`). If `τ̂(a) ∈ B^× twoRep(t') H`, the reduced
norms give `N I · nrd(twoRep t') ≡ 1 (mod 4)`; genus theory gives `χ_U(t) = χ₄(N I)`. So `χ_U(t) = −1` forces
`t'.2.2 ≠ 0`, where `F = 0` and hence `f_n = ±F = 0`. Then `χ_{T^c} f_n = χ_T f_n` termwise, which is TYZ
Lemma 2.8.
-/

set_option linter.style.longLine false
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.TYZGenusFold

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.TYZDecomp.H29Genus ZInQ.Contrib.T21Proof
  ZInQ.Contrib.HfxProof ZInQ.Contrib.HP23Proof
open ZInQ.RouteK.Redei ZInQ.RouteK.Rank5b
open ZInQ.Contrib.TYZGenus.TYZ35 (gchar divSet sgn2 divSet_div)
open IsDedekindDomain NumberField
open scoped Quaternion nonZeroDivisors

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

variable {n : ℕ} [NeZero n]

/-! ### Ideals prime to `m` -/

theorem coprime_absNorm_of_sup {M : Ideal (𝓞 (QNeg n))} {m : ℕ}
    (h : M ⊔ Ideal.span {((m : ℕ) : 𝓞 (QNeg n))} = ⊤) : Nat.Coprime (Ideal.absNorm M) m := by
  refine Nat.Coprime.symm (Nat.coprime_of_dvd fun k hk hkm hkM => ?_)
  have hle : Ideal.span {((m : ℕ) : 𝓞 (QNeg n))} ≤ Ideal.span {((k : ℕ) : 𝓞 (QNeg n))} := by
    rw [Ideal.span_singleton_le_span_singleton]
    exact_mod_cast (Nat.cast_dvd_cast hkm : ((k : ℕ) : 𝓞 (QNeg n)) ∣ ((m : ℕ) : 𝓞 (QNeg n)))
  have htop : M ⊔ Ideal.span {((k : ℕ) : 𝓞 (QNeg n))} = ⊤ :=
    top_le_iff.mp (h ▸ sup_le_sup_left hle M)
  exact not_dvd_absNorm_of_sup_span_eq_top hk htop hkM

/-- Every class contains an integral ideal with norm prime to a given `m > 1`. -/
theorem exists_mk0_coprime_nat {m : ℕ} (hm : 1 < m) (c : ClassGroup (𝓞 (QNeg n))) :
    ∃ I : (Ideal (𝓞 (QNeg n)))⁰, ClassGroup.mk0 I = c ∧
      Nat.Coprime (Ideal.absNorm (I : Ideal (𝓞 (QNeg n)))) m := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ0 : (J : Ideal (𝓞 (QNeg n))) ≠ 0 := nonZeroDivisors.coe_ne_zero J
  have hq0 : Ideal.span {(m : 𝓞 (QNeg n))} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact natCast_ne_zero_O (by omega)
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
    (I := (J : Ideal (𝓞 (QNeg n))) * Ideal.span {(m : 𝓞 (QNeg n))}) (J := J)
    (Ideal.mul_le_inf.trans inf_le_left) (mul_ne_zero hJ0 hq0)
  have haJ : a ∈ (J : Ideal (𝓞 (QNeg n))) := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨M, hM⟩ := Ideal.dvd_span_singleton.2 haJ
  have hcop : M ⊔ Ideal.span {(m : 𝓞 (QNeg n))} = ⊤ := by
    have h1 : (J : Ideal (𝓞 (QNeg n))) * (Ideal.span {(m : 𝓞 (QNeg n))} ⊔ M) = J * ⊤ := by
      rw [Ideal.mul_sup, ← hM, ha, Ideal.mul_top]
    rw [sup_comm]; exact mul_left_cancel₀ hJ0 h1
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [Ideal.zero_eq_bot, bot_sup_eq, Ideal.span_singleton_eq_top, isUnit_iff_dvd_one,
      show (1 : 𝓞 (QNeg n)) = ((1 : ℕ) : 𝓞 (QNeg n)) by simp, natCast_dvd_natCast_iff] at hcop
    exact hm.ne' (Nat.dvd_one.1 hcop)
  set M' : (Ideal (𝓞 (QNeg n)))⁰ := ⟨M, mem_nonZeroDivisors_of_ne_zero hM0⟩
  refine ⟨M', ?_, coprime_absNorm_of_sup hcop⟩
  have h1 : ClassGroup.mk0 J * ClassGroup.mk0 M' = 1 := by
    rw [← map_mul, ClassGroup.mk0_eq_one_iff (J * M').2]
    have e : ((J * M' : (Ideal (𝓞 (QNeg n)))⁰) : Ideal (𝓞 (QNeg n))) = Ideal.span {a} := by
      rw [Submonoid.coe_mul]; exact hM.symm
    rw [e]
    exact ⟨⟨a, rfl⟩⟩
  rw [hJ] at h1
  exact (inv_mul_eq_one.1 h1).symm

/-- An `α ∈ I` with `(α) = I M`, `M + (N I) = O`. -/
theorem exists_alpha (I : (Ideal (𝓞 (QNeg n)))⁰) :
    ∃ α : 𝓞 (QNeg n), ((α : QNeg n)) ≠ 0 ∧ ∃ M : Ideal (𝓞 (QNeg n)),
      Ideal.span {α} = (I : Ideal (𝓞 (QNeg n))) * M ∧
      M ⊔ Ideal.span {((Ideal.absNorm (I : Ideal (𝓞 (QNeg n))) : ℕ) : 𝓞 (QNeg n))} = ⊤ := by
  set m := Ideal.absNorm (I : Ideal (𝓞 (QNeg n)))
  have hI0 : (I : Ideal (𝓞 (QNeg n))) ≠ 0 := nonZeroDivisors.coe_ne_zero I
  have hm0 : m ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI0
  have hq0 : Ideal.span {(m : 𝓞 (QNeg n))} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact natCast_ne_zero_O hm0
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
    (I := (I : Ideal (𝓞 (QNeg n))) * Ideal.span {(m : 𝓞 (QNeg n))}) (J := I)
    (Ideal.mul_le_inf.trans inf_le_left) (mul_ne_zero hI0 hq0)
  have haI : a ∈ (I : Ideal (𝓞 (QNeg n))) := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨M, hM⟩ := Ideal.dvd_span_singleton.2 haI
  have hcop : M ⊔ Ideal.span {(m : 𝓞 (QNeg n))} = ⊤ := by
    have h1 : (I : Ideal (𝓞 (QNeg n))) * (Ideal.span {(m : 𝓞 (QNeg n))} ⊔ M) = I * ⊤ := by
      rw [Ideal.mul_sup, ← hM, ha, Ideal.mul_top]
    rw [sup_comm]; exact mul_left_cancel₀ hI0 h1
  by_cases ha0 : a = 0
  · -- then `I (m) = I`, so `(m) = O`, `m = 1`, `I = O`: take `α = 1`
    have h1 : (I : Ideal (𝓞 (QNeg n))) * Ideal.span {(m : 𝓞 (QNeg n))} = I * ⊤ := by
      rw [Ideal.mul_top]; rw [ha0, Ideal.span_singleton_eq_bot.mpr rfl, sup_bot_eq] at ha; exact ha
    have hmt : Ideal.span {(m : 𝓞 (QNeg n))} = ⊤ := mul_left_cancel₀ hI0 h1
    have hm1 : m = 1 := by
      rw [Ideal.span_singleton_eq_top, isUnit_iff_dvd_one,
        show (1 : 𝓞 (QNeg n)) = ((1 : ℕ) : 𝓞 (QNeg n)) by simp, natCast_dvd_natCast_iff] at hmt
      exact Nat.dvd_one.1 hmt
    have hItop : (I : Ideal (𝓞 (QNeg n))) = ⊤ := Ideal.absNorm_eq_one_iff.mp hm1
    refine ⟨1, by simp, ⊤, by rw [hItop, Ideal.span_singleton_one, Ideal.top_mul], top_sup_eq _⟩
  · refine ⟨a, ?_, M, hM, hcop⟩
    intro h
    apply ha0
    exact RingOfIntegers.ext (by simpa using h)

/-! ### Reduced norm of `τ(x)` -/

theorem normSq_tau (h1 : n % 8 = 1) {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]} (hτ : AdmissibleTau n τ) (x : QNeg n) :
    Quaternion.normSq (τ x) = Algebra.norm ℚ x := by
  obtain ⟨a, b, c, hτω, hn, -⟩ := exists_abc hτ (Or.inl h1)
  rw [tau_apply, hτω, algNorm_eq n, QuadraticAlgebra.norm_def, Quaternion.normSq_def']
  have hn' : (n : ℚ) = (a : ℚ) ^ 2 + (b : ℚ) ^ 2 + (c : ℚ) ^ 2 := by exact_mod_cast hn
  simp
  linear_combination (-(x.im ^ 2)) * hn'

theorem nrdH_βZ_mod4_one : ∀ t : T8, t.2.2 = 0 → nrdH (βZ t) % 4 = 1 := by decide +kernel

end ZInQ.Contrib.TYZGenusFold
