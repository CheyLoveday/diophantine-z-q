import ZInQKernel.Contrib.OneProof.PanBerger
import ZInQKernel.Contrib.G9.KerTheta

noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace PanBergerSplit

open Ideal

variable (p : ℕ) [Fact p.Prime]

local notation "O" => (𝓞_ℂ_[p] : Type)
local notation "ξ" => ZInQ.Contrib.G9.BdrKer.Cp.xi p

example : IsDomain (Ainf p) := inferInstance
example : IsDomain (AinfP p) := inferInstance
example : IsDomain O := inferInstance
example : IsHausdorff (span {(p : O)}) O := inferInstance

/-- An element of `𝓞_ℂ_p♭` divisible by every power of `p♭` is zero. -/
theorem tilt_eq_zero_of_dvd (ϖ : PreTilt O p) (hϖ : ϖ.untilt = p) (c : PreTilt O p)
    (h : ∀ n, ϖ ^ n ∣ c) : c = 0 := by
  have h0 : c.untilt = 0 := by
    apply IsHausdorff.haus' (I := span {(p : O)})
    intro n
    obtain ⟨d, rfl⟩ := h n
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, map_mul, map_pow, hϖ]
    exact dvd_mul_right _ _
  apply Perfection.ext
  intro n
  change PreTilt.coeff n c = PreTilt.coeff n 0
  rw [← ZInQ.Contrib.G9.BdrKer.Cp.mk_root, map_zero]
  have : ZInQ.Contrib.G9.BdrKer.Cp.root c n ^ p ^ n = 0 := by
    rw [ZInQ.Contrib.G9.BdrKer.Cp.root_pow, h0]
  rw [pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)] at this
  rw [this, map_zero]

/-- `p` is regular modulo `ξ^n` in `A_inf`. -/
theorem mem_xi_pow_of_p_mul (n : ℕ) : ∀ a : Ainf p,
    (p : Ainf p) * a ∈ span {ξ ^ n} → a ∈ span {ξ ^ n} := by
  induction n with
  | zero => intro a _; rw [pow_zero, Ideal.span_singleton_one]; trivial
  | succ n ih =>
    intro a ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
    have hθ : theta p a = 0 := by
      apply ZInQ.Contrib.G9.BdrKer.Cp.p_regular p
      have := congrArg (theta p) hc
      rw [map_mul, map_mul, map_pow, map_natCast] at this
      rw [← this]
      have hx : theta p ξ = 0 := by
        rw [← RingHom.mem_ker]
        change ξ ∈ RingHom.ker (WittVector.fontaineTheta O p)
        rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
        exact Ideal.mem_span_singleton_self _
      rw [hx, zero_pow (Nat.succ_ne_zero n), mul_zero]
    have ha' : a ∈ span {ξ} := by
      rw [← ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
      exact hθ
    obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton'.mp ha'
    have hξ : ξ ≠ 0 := ZInQ.Contrib.G9.BdrKer.Cp.xi_ne_zero p
    have h2 : (p : Ainf p) * a' = c * ξ ^ n := by
      apply mul_left_cancel₀ hξ
      linear_combination hc.symm
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (ih a' (Ideal.mem_span_singleton'.mpr ⟨c, h2.symm⟩))
    exact Ideal.mem_span_singleton'.mpr ⟨d, by rw [← hd, pow_succ]; ring⟩

theorem mem_xi_pow_of_p_pow_mul (n e : ℕ) (a : Ainf p)
    (h : (p : Ainf p) ^ e * a ∈ span {ξ ^ n}) : a ∈ span {ξ ^ n} := by
  induction e generalizing a with
  | zero => simpa using h
  | succ e ih =>
    apply ih
    apply mem_xi_pow_of_p_mul
    rw [pow_succ] at h
    simpa [mul_assoc, mul_comm, mul_left_comm] using h

/-- `A_inf` is `ξ`-adically separated on non-zero elements. -/
theorem exists_not_mem_xi_pow (x : Ainf p) (hx : x ≠ 0) : ∃ n, x ∉ span {ξ ^ n} := by
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul x hx
  by_contra hcon
  push Not at hcon
  apply hb
  have hb' : ∀ n, b ∈ span {ξ ^ n} := fun n => mem_xi_pow_of_p_pow_mul p n m b (hcon n)
  have h0 : WittVector.constantCoeff ξ = -(ZInQ.Contrib.G9.BdrKer.Cp.pFlat p) := by
    rw [ZInQ.Contrib.G9.BdrKer.Cp.xi, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub]
    simp
  apply tilt_eq_zero_of_dvd p (ZInQ.Contrib.G9.BdrKer.Cp.pFlat p)
    (ZInQ.Contrib.G9.BdrKer.Cp.untilt_pFlat p)
  intro n
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hb' n)
  have := congrArg WittVector.constantCoeff hc
  rw [map_mul, map_pow, h0] at this
  refine ⟨(-1) ^ n * WittVector.constantCoeff c, ?_⟩
  change b.coeff 0 = _
  rw [← WittVector.constantCoeff_apply, ← this, neg_pow]
  ring

/-- Every non-zero `x ∈ A_inf` is `ξ^s · w` with `θ(w) ≠ 0`. -/
theorem eq_xi_pow_mul (x : Ainf p) (hx : x ≠ 0) :
    ∃ (s : ℕ) (w : Ainf p), x = ξ ^ s * w ∧ theta p w ≠ 0 := by
  classical
  have hex := exists_not_mem_xi_pow p x hx
  let N := Nat.find hex
  have hN : x ∉ span {ξ ^ N} := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h0; apply hN; rw [h0, pow_zero, Ideal.span_singleton_one]; trivial
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hxM : x ∈ span {ξ ^ M} := by
    have := Nat.find_min hex (show M < N by omega)
    push Not at this
    exact this
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hxM
  refine ⟨M, w, by rw [← hw, mul_comm], fun hθ => hN ?_⟩
  have : w ∈ span {ξ} := by
    rw [← ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]; exact hθ
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp this
  rw [hM, ← hw]
  exact Ideal.mem_span_singleton'.mpr ⟨c, by rw [Nat.succ_eq_add_one, pow_succ]; ring⟩

theorem teich_sub_one_ne_zero {ε : PreTilt O p} (hne : ε ≠ 1) :
    WittVector.teichmuller p ε - 1 ≠ 0 := by
  intro h
  apply hne
  have h1 : WittVector.teichmuller p ε = 1 := sub_eq_zero.mp h
  have := congrArg (fun w => WittVector.coeff w 0) h1
  simpa [WittVector.teichmuller_coeff_zero] using this

/-- `ι(a) ∈ ξ^k A_inf[1/p]` implies `a ∈ ξ^k A_inf`. -/
theorem mem_xi_pow_of_algebraMap (k : ℕ) (a : Ainf p)
    (h : algebraMap (Ainf p) (AinfP p) a ∈ span {algebraMap (Ainf p) (AinfP p) ξ ^ k}) :
    a ∈ span {ξ ^ k} := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp h
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : Ainf p)) y
  obtain ⟨e, he⟩ := s.2
  apply mem_xi_pow_of_p_pow_mul p k e
  have hinj := IsLocalization.injective (AinfP p)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (ZInQ.Contrib.G9.BdrKer.Cp.witt_p_ne_zero p))
  have : (p : Ainf p) ^ e * a = b * ξ ^ k := by
    apply hinj
    have hs := IsLocalization.mk'_spec (AinfP p) b s
    simp only at he
    dsimp only at hy
    rw [map_mul, map_mul, map_pow, ← hy, ← hs, ← he]
    simp only [map_pow]
    ring
  exact Ideal.mem_span_singleton'.mpr ⟨b, this.symm⟩

end PanBergerSplit
end PkgI4
end HDec
