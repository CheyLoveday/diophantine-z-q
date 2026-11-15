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

/-! ### The lattice bound: `N! · A_cris^0 ⊆ A_inf + ξ^N A_inf[1/p]` -/

section Lattice

variable (N : ℕ)

/-- `ξ^N A_inf[1/p]`. -/
abbrev xiIdeal : Ideal (AinfP p) := span {algebraMap (Ainf p) (AinfP p) ξ ^ N}

/-- `A_inf[1/p] / ξ^N`. -/
abbrev Qn := AinfP p ⧸ xiIdeal p N

/-- The class of `ξ^i / i!`. -/
def latGen (i : ℕ) : Qn p N :=
  Ideal.Quotient.mk _ (qpToLoc p ((i.factorial : ℚ_[p])⁻¹) * algebraMap (Ainf p) (AinfP p) ξ ^ i)

/-- The `A_inf`-span of the classes of `ξ^i / i!`. -/
def latG : Submodule (Ainf p) (Qn p N) := Submodule.span (Ainf p) (Set.range (latGen p N))

theorem algebraMap_Qn (a : Ainf p) :
    algebraMap (Ainf p) (Qn p N) a = Ideal.Quotient.mk _ (algebraMap (Ainf p) (AinfP p) a) := rfl

theorem smul_Qn (r : Ainf p) (q : Qn p N) : r • q = algebraMap (Ainf p) (Qn p N) r * q :=
  Algebra.smul_def r q

theorem latGen_mul (i j : ℕ) :
    latGen p N i * latGen p N j = ((i + j).choose j : Ainf p) • latGen p N (i + j) := by
  rw [smul_Qn, latGen, latGen, latGen, algebraMap_Qn, ← map_mul, ← map_mul]
  congr 1
  have key : ((i + j).choose j : ℚ_[p]) * ((i + j).factorial : ℚ_[p])⁻¹ =
      (i.factorial : ℚ_[p])⁻¹ * (j.factorial : ℚ_[p])⁻¹ := by
    have h := Nat.add_choose_mul_factorial_mul_factorial i j
    have hi : (i.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have hj : (j.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hij : ((i + j).factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (i + j)
    field_simp
    rw [← h]
    push_cast
    ring
  have hc : algebraMap (Ainf p) (AinfP p) ((i + j).choose j : Ainf p) =
      qpToLoc p ((i + j).choose j : ℚ_[p]) := by
    rw [map_natCast, map_natCast]
  rw [hc, pow_add]
  calc qpToLoc p (i.factorial : ℚ_[p])⁻¹ * algebraMap (Ainf p) (AinfP p) ξ ^ i *
        (qpToLoc p (j.factorial : ℚ_[p])⁻¹ * algebraMap (Ainf p) (AinfP p) ξ ^ j)
      = qpToLoc p ((i.factorial : ℚ_[p])⁻¹ * (j.factorial : ℚ_[p])⁻¹) *
        (algebraMap (Ainf p) (AinfP p) ξ ^ i * algebraMap (Ainf p) (AinfP p) ξ ^ j) := by
        rw [map_mul]; ring
    _ = _ := by rw [← key, map_mul]; ring

theorem latG_mul_mem {x y : Qn p N} (hx : x ∈ latG p N) (hy : y ∈ latG p N) :
    x * y ∈ latG p N := by
  have h1 : latG p N * latG p N ≤ latG p N := by
    rw [latG, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    show latGen p N i * latGen p N j ∈ latG p N
    rw [latGen_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i + j, rfl⟩)
  exact h1 (Submodule.mul_mem_mul hx hy)

theorem latGen_zero : latGen p N 0 = 1 := by
  rw [latGen, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, inv_one, map_one, map_one]

/-- The subring of `A_inf[1/p]` of elements whose class lies in `latG`. -/
def latSub : Subring (AinfP p) where
  carrier := {z | Ideal.Quotient.mk (xiIdeal p N) z ∈ latG p N}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_mul] at ha hb ⊢
    exact latG_mul_mem p N ha hb
  one_mem' := by
    simp only [Set.mem_ofPred_eq, map_one]
    rw [← latGen_zero]
    exact Submodule.subset_span ⟨0, rfl⟩
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
    exact Submodule.add_mem _ ha hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact Submodule.zero_mem _
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, map_neg] at ha ⊢
    exact Submodule.neg_mem _ ha

theorem acris0_le_latSub : Acris0 p ≤ latSub p N := by
  rw [Acris0, Subring.closure_le]
  rintro z (⟨a, rfl⟩ | ⟨n, x, hx, rfl⟩)
  · show Ideal.Quotient.mk _ _ ∈ latG p N
    rw [← algebraMap_Qn, Algebra.algebraMap_eq_smul_one, ← latGen_zero]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  · have hx' : x ∈ span {ξ} := by
      rw [← ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]; exact hx
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hx'
    show Ideal.Quotient.mk _ _ ∈ latG p N
    have : Ideal.Quotient.mk (xiIdeal p N) (dpow p n (b * ξ)) = b ^ n • latGen p N n := by
      rw [smul_Qn, latGen, algebraMap_Qn, ← map_mul, dpow]
      congr 1
      rw [map_mul, mul_pow, map_pow]
      ring
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

theorem latGen_eq_zero {i : ℕ} (hi : N ≤ i) : latGen p N i = 0 := by
  rw [latGen, Ideal.Quotient.eq_zero_iff_mem]
  apply Ideal.mul_mem_left
  rw [Ideal.mem_span_singleton']
  exact ⟨algebraMap (Ainf p) (AinfP p) ξ ^ (i - N), by rw [← pow_add]; congr 1; omega⟩

theorem latG_bound {q : Qn p N} (hq : q ∈ latG p N) :
    ∃ a : Ainf p, (N.factorial : Qn p N) * q = algebraMap (Ainf p) (Qn p N) a := by
  induction hq using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    by_cases hi : N ≤ i
    · exact ⟨0, by rw [latGen_eq_zero p N hi, mul_zero, map_zero]⟩
    · obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial (show i ≤ N by omega)
      refine ⟨(c : Ainf p) * ξ ^ i, ?_⟩
      rw [algebraMap_Qn, latGen, ← map_natCast (Ideal.Quotient.mk (xiIdeal p N)), ← map_mul]
      congr 1
      have hi0 : (i.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
      have e1 : (N.factorial : AinfP p) * qpToLoc p (i.factorial : ℚ_[p])⁻¹ = (c : AinfP p) := by
        rw [← map_natCast (qpToLoc p), ← map_mul, hc]
        push_cast
        rw [mul_comm (i.factorial : ℚ_[p]), mul_assoc, mul_inv_cancel₀ hi0, mul_one, map_natCast]
      rw [map_mul, map_natCast, map_pow, ← e1]
      ring
  | zero => exact ⟨0, by rw [mul_zero, map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [mul_add, ha, hb, map_add]⟩
  | smul r x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨r * a, ?_⟩
    rw [smul_Qn, mul_left_comm, ha, map_mul]

end Lattice

end PanBergerSplit
end PkgI4
end HDec
