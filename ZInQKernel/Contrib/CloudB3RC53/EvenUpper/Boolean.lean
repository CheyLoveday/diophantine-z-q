import ZInQKernel.Contrib.OneProof.RC.Boolean.MissingAddress
import ZInQKernel.Contrib.OneProof.RC.Even.EvenSource

/-!
# EvenUpper, part 1: the Boolean comparison on an even cube (clause (iii))

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:sec7-even-upper`, tex 2322–2341, and
App G (F.2), tex 10114–10120: "Choose `M − c_E > B_e`. The constant coefficient of
`2^{c_E} u^{ev} ∈ Λ[G_b]` has sign-value bits of total Boolean degree at most `2^{M−1} − 1`. For a
larger cube dimension, the Boolean comparison in Section 9 gives `x ≠ 0` with
`v₂(u^{ev}_x(0) − u^{ev}_0(0)) ≥ M − c_E`."

`boolean_comparison` (`PROVED`, from lane RC1's `exists_ne_zero_of_coefficient_equalities`: the
Boolean bit-degree lemma and cube parity): for lane RC11's even scalar `u ∈ Λ[1/2][G]`
(group-basis coefficients `u g ∈ ℚ₂[[t]]`, `G = 𝔽₂^b`, `2^c u g ∈ Λ`) and `b > 2^{M−1} − 1`,
some nonzero address `x` has `u_x(0) = u_0(0)` or `v₂(u_x(0) − u_0(0)) ≥ M − c`, where
`u_x = Σ_g x(g) u_g` is RC11's `charEval`.
-/

namespace ZInQ.Contrib.CloudB3RC53.EvenUpper

open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Boolean Finset

/-- RC11's sign character `x(g)` is RC1's `signChar` for the standard pairing. -/
theorem chi_eq_signChar {b : ℕ} (x g : Fin b → ZMod 2) :
    chi x g = signChar (dotPairing b) x g := by
  unfold chi signChar
  have hd : dotPairing b g x = dotProduct x g := by
    simp only [dotPairing, AddMonoidHom.coe_mk, ZeroHom.coe_mk, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hd]
  generalize dotProduct x g = s
  revert s; decide

/-- **The Boolean comparison on an even cube** (tex 2322–2341, App G 10114–10120), `PROVED`. -/
theorem boolean_comparison {b : ℕ} (u : (Fin b → ZMod 2) → PowerSeries ℚ_[2]) (c : ℕ)
    (hint : ∀ g, InLam ((2 : ℚ_[2]) ^ c • u g)) (M : ℕ) (hb : 2 ^ (M - 1) - 1 < b) :
    ∃ x : Fin b → ZMod 2, x ≠ 0 ∧
      (central (charEval u x) = central (charEval u 0) ∨
        (M : ℤ) - c ≤ Padic.valuation (central (charEval u x) - central (charEval u 0))) := by
  classical
  -- the integral constant coefficients `2^c u_g(0) ∈ ℤ₂`
  have hn : ∀ g, ‖(2 : ℚ_[2]) ^ c * PowerSeries.coeff 0 (u g)‖ ≤ 1 := fun g => by
    have := hint g 0
    rwa [PowerSeries.coeff_smul, smul_eq_mul] at this
  let α : (Fin b → ZMod 2) → ℤ_[2] := fun g => ⟨_, hn g⟩
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_of_coefficient_equalities (dotPairing b) {()}
    (fun _ => α) M (by simpa using hb)
  refine ⟨x, hx0, ?_⟩
  have hdvd := hx () (mem_singleton_self _)
  -- `signEval α y = 2^c u_y(0)` in `ℚ₂`
  have hse : ∀ y, ((signEval (dotPairing b) α y : ℤ_[2]) : ℚ_[2]) =
      (2 : ℚ_[2]) ^ c * central (charEval u y) := by
    intro y
    simp only [signEval, central, charEval, map_sum, PowerSeries.coeff_smul, smul_eq_mul,
      PadicInt.coe_sum, PadicInt.coe_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [chi_eq_signChar]
    have hα : ((α g : ℤ_[2]) : ℚ_[2]) = (2 : ℚ_[2]) ^ c * PowerSeries.coeff 0 (u g) := rfl
    push_cast
    rw [hα]
    ring
  by_cases heq : central (charEval u x) = central (charEval u 0)
  · exact Or.inl heq
  · right
    obtain ⟨z, hz⟩ := hdvd
    have hΔ : (2 : ℚ_[2]) ^ c * (central (charEval u x) - central (charEval u 0)) =
        (2 : ℚ_[2]) ^ M * (z : ℚ_[2]) := by
      rw [mul_sub, ← hse, ← hse, ← PadicInt.coe_sub, hz, PadicInt.coe_mul, PadicInt.coe_pow]
      congr 2
    have hne : central (charEval u x) - central (charEval u 0) ≠ 0 := sub_ne_zero.mpr heq
    have hz0 : (z : ℚ_[2]) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hΔ
      exact hne ((mul_eq_zero.mp hΔ).resolve_left (pow_ne_zero _ two_ne_zero))
    have hv := congrArg Padic.valuation hΔ
    rw [Padic.valuation_mul (pow_ne_zero _ two_ne_zero) hne,
      Padic.valuation_mul (pow_ne_zero _ two_ne_zero) hz0, Padic.valuation_pow,
      Padic.valuation_pow] at hv
    have h2 : (2 : ℚ_[2]).valuation = 1 := by simp
    have hzv : 0 ≤ (z : ℚ_[2]).valuation := by
      rw [← Padic.norm_le_one_iff_val_nonneg]; exact z.2
    rw [h2] at hv
    linarith

end ZInQ.Contrib.CloudB3RC53.EvenUpper
