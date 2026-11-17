import ZInQKernel.Contrib.OneProof.PanBergerDict

/-!
# pb-pst (a): `B_max = B_max^+[1/t]` for one `t = log [ε₀]`

bst-construct's `Bmax` inverts `log [ε]` for every `ε ∈ 𝓞_ℂ_p♭` with `ε^♯ = 1`, `ε ≠ 1` (`tInvSet`).
Here: for a generator `ε₀ = (1, ζ_p, ζ_{p²}, …)` (`ζ_p ≠ 1`) every such `log [ε]` is `a · log [ε₀]`
with `a ∈ ℤ_p ∖ 0`, so bst-construct's `Bmax`, `Bst` are `B_max^+[1/t]`, `B_max^+[1/t][log [p̃]]` with
`t = log [ε₀]`.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace BmaxOne

open Module PowerSeries Ideal
open scoped TensorProduct
open BergerBst
open PanBergerSplit (Ainf AinfP theta)

variable (p : ℕ) [Fact p.Prime]

/-! ## §1. `A_inf / ξ^m` is `p`-adically separated -/

theorem theta_xi : theta p (ZInQ.Contrib.G9.BdrKer.Cp.xi p) = 0 := by
  change ZInQ.Contrib.G9.BdrKer.Cp.xi p ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p)
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
  exact Ideal.mem_span_singleton_self _

theorem mem_xi_of_forall (w : Ainf p)
    (h : ∀ k : ℕ, ∃ a b : Ainf p, w = (p : Ainf p) ^ k * a + ZInQ.Contrib.G9.BdrKer.Cp.xi p * b) :
    w ∈ span {ZInQ.Contrib.G9.BdrKer.Cp.xi p} := by
  rw [← ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
  change theta p w = 0
  apply IsHausdorff.haus' (I := span {(p : 𝓞_ℂ_[p])})
  intro k
  obtain ⟨a, b, rfl⟩ := h k
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, map_add, map_mul, map_mul, map_pow, map_natCast, theta_xi, zero_mul,
    add_zero]
  exact dvd_mul_right _ _

/-- `⋂_k (p^k A_inf + ξ^m A_inf) = ξ^m A_inf`. -/
theorem mem_xi_pow_of_forall (m : ℕ) : ∀ w : Ainf p,
    (∀ k : ℕ, ∃ a b : Ainf p, w = (p : Ainf p) ^ k * a + ZInQ.Contrib.G9.BdrKer.Cp.xi p ^ m * b) →
    w ∈ span {ZInQ.Contrib.G9.BdrKer.Cp.xi p ^ m} := by
  induction m with
  | zero => intro w _; rw [pow_zero, Ideal.span_singleton_one]; trivial
  | succ m ih =>
    intro w h
    have h1 : w ∈ span {ZInQ.Contrib.G9.BdrKer.Cp.xi p ^ m} := ih w fun k => by
      obtain ⟨a, b, hab⟩ := h k
      exact ⟨a, ZInQ.Contrib.G9.BdrKer.Cp.xi p * b, by rw [hab, pow_succ]; ring⟩
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp h1
    have h2 : z ∈ span {ZInQ.Contrib.G9.BdrKer.Cp.xi p} := mem_xi_of_forall p z fun k => by
      obtain ⟨a, b, hab⟩ := h k
      rw [pow_succ] at hab
      have ha : (p : Ainf p) ^ k * a ∈ span {ZInQ.Contrib.G9.BdrKer.Cp.xi p ^ m} :=
        Ideal.mem_span_singleton'.mpr ⟨z - ZInQ.Contrib.G9.BdrKer.Cp.xi p * b, by
          linear_combination hab⟩
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (mem_xi_pow_of_p_pow_mul p m k a ha)
      refine ⟨c, b, ?_⟩
      apply mul_left_cancel₀ (pow_ne_zero m (ZInQ.Contrib.G9.BdrKer.Cp.xi_ne_zero p))
      rw [← hc] at hab
      linear_combination hab
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp h2
    exact Ideal.mem_span_singleton'.mpr ⟨d, by rw [pow_succ]; ring⟩

/-! ## §2. `A_max` is `p`-adically separated inside `B_dR^+` -/

theorem ith_pow (m : ℕ) : Ith p ^ m =
    span {algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ m} := by
  rw [Ith, ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineThetaInvertP_Cp, Ideal.span_singleton_pow]
  rfl

/-- Modulo `(ker θ)^m`, `p^m` times an element of `A_max` comes from `A_inf`. -/
theorem amax_mod {y : BDeRhamPlus 𝓞_ℂ_[p] p} (hy : y ∈ Amax p) (m : ℕ) :
    ∃ w : Ainf p, AdicCompletion.evalₐ (Ith p) m ((p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ m * y) =
      Ideal.Quotient.mk _ (algebraMap (Ainf p) (AinfP p) w) := by
  obtain ⟨f, -, rfl⟩ := hy
  refine ⟨∑ i ∈ Finset.range m, PowerSeries.coeff i f * ZInQ.Contrib.G9.BdrKer.Cp.xi p ^ i *
    (p : Ainf p) ^ (m - i), ?_⟩
  change AdicCompletion.evalₐ (Ith p) m ((p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ m *
    evalB p (omegaP_mem p) (PowerSeries.map (algebraMap (Ainf p) (AinfP p)) f)) = _
  rw [map_mul, evalB, evalₐ_psEval, map_pow, map_natCast, ← map_natCast (Ideal.Quotient.mk _),
    ← map_pow, ← map_mul]
  congr 1
  rw [Polynomial.eval, eval₂_trunc_eq_sum_range, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := (Finset.mem_range.mp hi).le
  simp only [RingHom.id_apply, PowerSeries.coeff_map, map_mul, map_pow, map_natCast]
  have hpq : (p : AinfP p) * qpToLoc p ((p : ℚ_[p])⁻¹) = 1 :=
    natCast_mul_qp p p (Fact.out : p.Prime).ne_zero
  have hm : (p : AinfP p) ^ m = (p : AinfP p) ^ (m - i) * (p : AinfP p) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  rw [hm, omegaP]
  change _ = _ * algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ i * _
  have hx : ZInQ.Contrib.G9.BdrKer.Cp.xi' p =
      algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) := rfl
  rw [hx]
  calc (p : AinfP p) ^ (m - i) * (p : AinfP p) ^ i *
        (algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff i f) *
          (algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) *
            qpToLoc p ((p : ℚ_[p])⁻¹)) ^ i)
      = (p : AinfP p) ^ (m - i) * ((p : AinfP p) * qpToLoc p ((p : ℚ_[p])⁻¹)) ^ i *
        (algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff i f) *
          algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ i) := by ring
    _ = _ := by rw [hpq, one_pow]; ring

/-- **`A_max ⊆ B_dR^+` is `p`-adically separated**: an element of `B_dR^+` lying in `p^k A_max`
for every `k` is `0`. -/
theorem amax_sep (x : BDeRhamPlus 𝓞_ℂ_[p] p)
    (h : ∀ k : ℕ, ∃ y ∈ Amax p, x = (p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ k * y) : x = 0 := by
  refine AdicCompletion.ext_evalₐ fun m => ?_
  rw [map_zero]
  choose y hy hxy using h
  choose w hw using fun k => amax_mod p (hy k) m
  have hk : ∀ k, AdicCompletion.evalₐ (Ith p) m ((p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ m * x) =
      Ideal.Quotient.mk _ (algebraMap (Ainf p) (AinfP p) ((p : Ainf p) ^ k * w k)) := by
    intro k
    rw [hxy k, mul_left_comm, map_mul, hw k, map_pow, map_natCast, map_mul, map_pow, map_natCast,
      map_mul, map_pow, map_natCast]
  have hw0 : w 0 ∈ span {ZInQ.Contrib.G9.BdrKer.Cp.xi p ^ m} := by
    refine mem_xi_pow_of_forall p m (w 0) fun k => ?_
    have e := (hk 0).symm.trans (hk k)
    rw [Ideal.Quotient.eq, ← map_sub, ith_pow] at e
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (mem_xi_pow_of_algebraMap p m _ e)
    exact ⟨w k, b, by rw [pow_zero, one_mul] at hb; linear_combination -hb⟩
  have h0 : AdicCompletion.evalₐ (Ith p) m ((p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ m * x) = 0 := by
    rw [hk 0, pow_zero, one_mul, Ideal.Quotient.eq_zero_iff_mem, ith_pow]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hw0
    exact Ideal.mem_span_singleton'.mpr ⟨algebraMap (Ainf p) (AinfP p) c, by
      rw [← hc, map_mul, map_pow]⟩
  rw [map_mul, map_pow, map_natCast] at h0
  have hu : IsUnit ((p : AinfP p ⧸ Ith p ^ m) ^ m) := by
    refine IsUnit.pow _ ?_
    have := IsLocalization.Away.algebraMap_isUnit (S := AinfP p) (p : Ainf p)
    rw [map_natCast] at this
    simpa using this.map (Ideal.Quotient.mk (Ith p ^ m))
  exact (hu.mul_right_eq_zero).mp h0

end BmaxOne
end PkgI4
end HDec
