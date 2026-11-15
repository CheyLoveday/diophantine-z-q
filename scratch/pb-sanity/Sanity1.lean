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

/-! ### `p^m · ∏ log [ε_i] ≠ 0` in `A_cris` -/

/-- The `ε` with `ε^♯ = 1`, `ε ≠ 1` (those whose `log [ε]` are inverted in `B_cris`). -/
abbrev TEps := {ε : PreTilt O p // PreTilt.untilt ε = 1 ∧ ε ≠ 1}

/-- `log [ε] ∈ A_cris`. -/
def logOf (e : TEps p) : Acris p := logT p (theta_teich_sub_one p e.2.1)

/-- `Σ_{1 ≤ j ≤ M} (-1)^{j+1} x^{j-1}/j`, so that the partial log sum is `x · Vsum`. -/
def Vsum (x : Ainf p) (M : ℕ) : AinfP p :=
  ∑ j ∈ Finset.Ico 1 (M + 1), (-1) ^ (j + 1) * ((j - 1).factorial : AinfP p) *
    (qpToLoc p ((j.factorial : ℚ_[p])⁻¹) * algebraMap (Ainf p) (AinfP p) x ^ (j - 1))

theorem logPartialVal_eq (x : Ainf p) (M : ℕ) :
    logPartialVal p x M = algebraMap (Ainf p) (AinfP p) x * Vsum p x M := by
  rw [logPartialVal, Vsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [logTerm, dpow, Nat.add_sub_cancel, pow_succ]
  ring

theorem thetaP_algebraMap (a : Ainf p) :
    fontaineThetaInvertP O p (algebraMap (Ainf p) (AinfP p) a) =
      algebraMap O (Localization.Away (p : O)) (theta p a) :=
  IsLocalization.Away.lift_eq (p : Ainf p)
    (by simpa using IsLocalization.Away.algebraMap_isUnit (p : O)) a

theorem thetaP_Vsum {x : Ainf p} (hx : theta p x = 0) {M : ℕ} (hM : 1 ≤ M) :
    fontaineThetaInvertP O p (Vsum p x M) = 1 := by
  have h0 : fontaineThetaInvertP O p (algebraMap (Ainf p) (AinfP p) x) = 0 := by
    rw [thetaP_algebraMap, hx, map_zero]
  rw [Vsum, map_sum, Finset.sum_eq_single 1]
  · simp
  · intro j hj hj1
    rw [Finset.mem_Ico] at hj
    simp only [map_mul, map_pow, h0, zero_pow (show j - 1 ≠ 0 by omega), mul_zero]
  · intro h; exfalso; apply h; rw [Finset.mem_Ico]; omega

theorem algebraMap_O_injective :
    Function.Injective (algebraMap O (Localization.Away (p : O))) :=
  IsLocalization.injective _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (ZInQ.Contrib.G9.BdrKer.Cp.p_ne_zero p))

theorem natCast_O_ne_zero {k : ℕ} (hk : k ≠ 0) : (k : O) ≠ 0 := by
  intro h
  have h1 : ((k : O) : ℂ_[p]) = 0 := by rw [h]; rfl
  push_cast at h1
  exact hk (by exact_mod_cast h1)

theorem theta_xi : theta p ξ = 0 := by
  rw [← RingHom.mem_ker]
  change ξ ∈ RingHom.ker (WittVector.fontaineTheta O p)
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
  exact Ideal.mem_span_singleton_self _

theorem prod_logPartialVal_decomp (l : List (TEps p)) (s : TEps p → ℕ) (w : TEps p → Ainf p)
    (hsw : ∀ e : TEps p, WittVector.teichmuller p e.1 - 1 = ξ ^ s e * w e) (M : ℕ) :
    (l.map fun e => logPartialVal p (WittVector.teichmuller p e.1 - 1) M).prod =
      algebraMap (Ainf p) (AinfP p) ξ ^ (l.map s).sum * algebraMap (Ainf p) (AinfP p) (l.map w).prod *
        (l.map fun e => Vsum p (WittVector.teichmuller p e.1 - 1) M).prod := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [ih, logPartialVal_eq, hsw e]
    simp only [map_mul, map_pow, pow_add]
    ring

/-- **Main lemma.** For every finite family of `ε_i` with `ε_i^♯ = 1`, `ε_i ≠ 1`, and every
`m`, `p^m · ∏ log [ε_i] ≠ 0` in `A_cris`. -/
theorem pow_mul_prod_logOf_ne_zero (l : List (TEps p)) (m : ℕ) :
    (p : Acris p) ^ m * (l.map (logOf p)).prod ≠ 0 := by
  classical
  have hdec : ∀ e : TEps p, ∃ (s : ℕ) (w : Ainf p),
      WittVector.teichmuller p e.1 - 1 = ξ ^ s * w ∧ theta p w ≠ 0 :=
    fun e => eq_xi_pow_mul p _ (teich_sub_one_ne_zero p e.2.2)
  choose s w hsw hw using hdec
  set X := algebraMap (Ainf p) (AinfP p) ξ with hX
  have hX0 : X ≠ 0 := ZInQ.Contrib.G9.BdrKer.Cp.xi'_ne_zero p
  set S := (l.map s).sum with hS
  set N := S + 1 with hN
  have hdecomp : ∀ M : ℕ, (l.map fun e => logPartialVal p (WittVector.teichmuller p e.1 - 1) M).prod
      = X ^ S * algebraMap (Ainf p) (AinfP p) (l.map w).prod *
        (l.map fun e => Vsum p (WittVector.teichmuller p e.1 - 1) M).prod :=
    fun M => prod_logPartialVal_decomp p l s w hsw M
  set c : O := (N.factorial : O) * (p : O) ^ m * (l.map fun e => theta p (w e)).prod with hc
  have hc0 : c ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (natCast_O_ne_zero p (Nat.factorial_ne_zero N))
      (pow_ne_zero _ (ZInQ.Contrib.G9.BdrKer.Cp.p_ne_zero p))) ?_
    intro h0
    rw [List.prod_eq_zero_iff] at h0
    obtain ⟨e, _, he⟩ := List.mem_map.mp h0
    exact hw e he
  intro hP
  have key : ∀ n : ℕ, ∃ a' : Ainf p, c = (p : O) ^ n * theta p a' := by
    intro n
    have hev := congrArg (AdicCompletion.evalₐ (Ideal.span {(p : Acris0 p)}) n) hP
    rw [map_zero, map_mul, map_pow, map_natCast, map_list_prod, List.map_map] at hev
    have hfac : (AdicCompletion.evalₐ (Ideal.span {(p : Acris0 p)}) n) ∘ logOf p =
        fun e => Ideal.Quotient.mk _ (logPartial p (theta_teich_sub_one p e.2.1) (p ^ n)) :=
      funext fun e => evalₐ_logT p _ n
    rw [hfac] at hev
    have hmem : ((p : Acris0 p) ^ m *
        (l.map fun e => logPartial p (theta_teich_sub_one p e.2.1) (p ^ n)).prod) ∈
        (span {(p : Acris0 p)}) ^ n := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_natCast, map_list_prod,
        List.map_map]
      exact hev
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
    obtain ⟨z, hz⟩ := hmem
    have hzAP : (z : AinfP p) * (p : AinfP p) ^ n = (p : AinfP p) ^ m *
        (l.map fun e => logPartialVal p (WittVector.teichmuller p e.1 - 1) (p ^ n)).prod := by
      have := congrArg (Acris0 p).subtype hz
      rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_list_prod, List.map_map] at this
      exact this
    -- the lattice
    obtain ⟨a, ha⟩ := latG_bound p N (acris0_le_latSub p N z.2)
    rw [algebraMap_Qn, ← map_natCast (Ideal.Quotient.mk (xiIdeal p N)), ← map_mul,
      Ideal.Quotient.eq, Ideal.mem_span_singleton'] at ha
    obtain ⟨w0, hw0⟩ := ha
    -- the main identity in `A_inf[1/p]`
    have hmain : (N.factorial : AinfP p) * (p : AinfP p) ^ m * X ^ S *
        algebraMap (Ainf p) (AinfP p) (l.map w).prod *
        (l.map fun e => Vsum p (WittVector.teichmuller p e.1 - 1) (p ^ n)).prod =
        (p : AinfP p) ^ n * (algebraMap (Ainf p) (AinfP p) a + w0 * X ^ N) := by
      have h1 := congrArg (fun y => (N.factorial : AinfP p) * y) hzAP
      rw [hdecomp] at h1
      have h2 : (N.factorial : AinfP p) * (z : AinfP p) =
          algebraMap (Ainf p) (AinfP p) a + w0 * X ^ N := by
        rw [← hX] at hw0
        linear_combination -hw0
      linear_combination -h1 + (p : AinfP p) ^ n * h2
    -- `a ∈ ξ^S A_inf`
    have haS : a ∈ span {ξ ^ S} := by
      apply mem_xi_pow_of_p_pow_mul p S n
      apply mem_xi_pow_of_algebraMap
      rw [Ideal.mem_span_singleton']
      refine ⟨(N.factorial : AinfP p) * (p : AinfP p) ^ m *
        algebraMap (Ainf p) (AinfP p) (l.map w).prod *
        (l.map fun e => Vsum p (WittVector.teichmuller p e.1 - 1) (p ^ n)).prod -
        (p : AinfP p) ^ n * w0 * X, ?_⟩
      rw [map_mul, map_pow, map_natCast]
      rw [hN, pow_succ] at hmain
      linear_combination hmain
    obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton'.mp haS
    refine ⟨a', ?_⟩
    have hcancel : (N.factorial : AinfP p) * (p : AinfP p) ^ m *
        algebraMap (Ainf p) (AinfP p) (l.map w).prod *
        (l.map fun e => Vsum p (WittVector.teichmuller p e.1 - 1) (p ^ n)).prod =
        (p : AinfP p) ^ n * (algebraMap (Ainf p) (AinfP p) a' + w0 * X) := by
      apply mul_left_cancel₀ (pow_ne_zero S hX0)
      rw [hN, pow_succ, map_mul, map_pow] at hmain
      linear_combination hmain
    have hθ := congrArg (fontaineThetaInvertP O p) hcancel
    have hV : fontaineThetaInvertP O p
        (l.map fun e => Vsum p (WittVector.teichmuller p e.1 - 1) (p ^ n)).prod = 1 := by
      rw [map_list_prod, List.map_map]
      apply List.prod_eq_one
      intro y hy
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hy
      exact thetaP_Vsum p (theta_teich_sub_one p e.2.1) (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)
    have hXθ : fontaineThetaInvertP O p X = 0 := by
      rw [hX, thetaP_algebraMap, theta_xi, map_zero]
    simp only [map_mul, map_add, map_pow, map_natCast, hV, hXθ, thetaP_algebraMap, mul_zero,
      add_zero, mul_one] at hθ
    apply algebraMap_O_injective p
    rw [hc, map_mul, map_mul, map_mul, map_pow, map_natCast, map_natCast, map_pow, map_natCast]
    rw [map_list_prod, List.map_map] at hθ
    exact hθ
  apply hc0
  apply IsHausdorff.haus' (I := span {(p : O)})
  intro n
  obtain ⟨a', ha'⟩ := key n
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, ha']
  exact dvd_mul_right _ _

/-! ### Consequences: `B_cris^+`, `B_cris`, `B_st` are not zero; `t` is not nilpotent -/

/-- Every element of `tMonoid` is the image of a finite product of `log [ε_i]`. -/
theorem exists_list_of_mem_tMonoid {y : BcrisPlus p} (hy : y ∈ tMonoid p) :
    ∃ l : List (TEps p), y = algebraMap (Acris p) (BcrisPlus p) (l.map (logOf p)).prod := by
  induction hy using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨ε, h, hne, rfl⟩ := hx
    exact ⟨[⟨ε, h, hne⟩], by rw [List.map_singleton, List.prod_singleton]; rfl⟩
  | one => exact ⟨[], by rw [List.map_nil, List.prod_nil, map_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l₁, rfl⟩ := hx
    obtain ⟨l₂, rfl⟩ := hy
    exact ⟨l₁ ++ l₂, by rw [List.map_append, List.prod_append, map_mul]⟩

theorem algebraMap_prod_logOf_ne_zero (l : List (TEps p)) :
    algebraMap (Acris p) (BcrisPlus p) (l.map (logOf p)).prod ≠ 0 := by
  intro h
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (p : Acris p)) (BcrisPlus p) _).mp h
  exact pow_mul_prod_logOf_ne_zero p l k hk

/-- **`0 ∉ tMonoid`**: no product of the `log [ε]` is zero in `B_cris^+`. -/
theorem zero_notMem_tMonoid : (0 : BcrisPlus p) ∉ tMonoid p := fun h => by
  obtain ⟨l, hl⟩ := exists_list_of_mem_tMonoid p h
  exact algebraMap_prod_logOf_ne_zero p l hl.symm

/-- **`B_cris^+ ≠ 0`.** -/
instance nontrivial_bcrisPlus : Nontrivial (BcrisPlus p) :=
  nontrivial_of_ne 1 0 (by simpa using algebraMap_prod_logOf_ne_zero p [])

/-- **`B_cris ≠ 0`.** -/
instance nontrivial_bcris : Nontrivial (Bcris p) := by
  refine nontrivial_of_ne 1 0 fun h => ?_
  have h' : algebraMap (BcrisPlus p) (Bcris p) 1 = 0 := by rw [map_one]; exact h
  obtain ⟨⟨m, hm⟩, hm1⟩ := (IsLocalization.map_eq_zero_iff (tMonoid p) (Bcris p) _).mp h'
  rw [mul_one] at hm1
  exact zero_notMem_tMonoid p (hm1 ▸ hm)

/-- **`B_st ≠ 0`.** -/
instance nontrivial_bst : Nontrivial (Bst p) := inferInstance

/-- `ℚ_p → B_st` is injective (so `ℚ_p ⊆ B_st^{G_K}` is a genuine subspace). -/
theorem algebraMap_qp_bst_injective : Function.Injective (algebraMap ℚ_[p] (Bst p)) :=
  (algebraMap ℚ_[p] (Bst p)).injective

/-- **`log [ε]` is not nilpotent in `B_cris^+`** (for `ε^♯ = 1`, `ε ≠ 1`). -/
theorem logOf_not_isNilpotent (e : TEps p) :
    ¬ IsNilpotent (algebraMap (Acris p) (BcrisPlus p) (logOf p e)) := by
  rintro ⟨k, hk⟩
  apply algebraMap_prod_logOf_ne_zero p (List.replicate k e)
  rw [List.map_replicate, List.prod_replicate, map_pow, hk]

/-- `log [ε] ≠ 0` in `A_cris`. -/
theorem logOf_ne_zero (e : TEps p) : logOf p e ≠ 0 := by
  have := pow_mul_prod_logOf_ne_zero p [e] 0
  simpa using this

/-- The image of `log [ε]` in `B_cris` is a unit, and `B_cris ≠ 0`, so it is non-zero. -/
theorem isUnit_logOf_bcris (e : TEps p) :
    IsUnit (algebraMap (BcrisPlus p) (Bcris p) (algebraMap (Acris p) (BcrisPlus p) (logOf p e))) :=
  IsLocalization.map_units (Bcris p)
    (⟨_, Submonoid.subset_closure ⟨e.1, e.2.1, e.2.2, rfl⟩⟩ : tMonoid p)

theorem logOf_bcris_ne_zero (e : TEps p) :
    algebraMap (BcrisPlus p) (Bcris p) (algebraMap (Acris p) (BcrisPlus p) (logOf p e)) ≠ 0 :=
  (isUnit_logOf_bcris p e).ne_zero

/-! ### There is an `ε` with `ε^♯ = 1`, `ε ≠ 1` (so `t` exists and `B_cris ≠ B_cris^+[1/1]`) -/

open ZInQ.Contrib.G9.BdrKer.Cp in
/-- If the components of `x ∈ 𝓞_ℂ_p♭` are the classes of a compatible system `c` of `p`-th
power roots, then `x^♯ = c 0`. -/
theorem untilt_eq_of_coeff (c : ℕ → O) (hc : ∀ m, c (m + 1) ^ p = c m) (x : PreTilt O p)
    (hx : ∀ m, PreTilt.coeff m x = Ideal.Quotient.mk _ (c m)) : x.untilt = c 0 := by
  have hpow : ∀ k, c k ^ p ^ k = c 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_mul, hc, ih]
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : O)})]
  intro n
  rw [SModEq.sub_mem, ZInQ.Contrib.G9.BdrKer.mem_span_pow_iff']
  have h1 : root x n - c n ∈ span {(p : O)} := by
    rw [← Ideal.Quotient.eq, mk_root, hx]
  have h2 := dvd_sub_pow_of_dvd_sub (Ideal.mem_span_singleton.mp h1) n
  rw [root_pow, hpow] at h2
  obtain ⟨d, hd⟩ := h2
  exact ⟨p * d, by rw [hd]; ring⟩

open ZInQ.Contrib.G9.BdrKer.Cp in
theorem root_eq_of_coeff (c : ℕ → O) (hc : ∀ m, c (m + 1) ^ p = c m) (x : PreTilt O p)
    (hx : ∀ m, PreTilt.coeff m x = Ideal.Quotient.mk _ (c m)) (n : ℕ) : root x n = c n := by
  have := untilt_eq_of_coeff p (fun m => c (m + n)) (fun m => by
    simpa [Nat.add_right_comm] using hc (m + n)) (((frobeniusEquiv (PreTilt O p) p).symm^[n]) x)
    (fun m => by rw [PreTilt.coeff_iterate_frobeniusEquiv_symm, hx])
  simpa [ZInQ.Contrib.G9.BdrKer.Cp.root] using this

/-- A compatible system `1, ζ_p, ζ_{p²}, …` of `p`-power roots of unity in `ℂ_p`. -/
noncomputable def zetaSeq (ζ : ℂ_[p]) : ℕ → ℂ_[p]
  | 0 => 1
  | 1 => ζ
  | n + 2 => Classical.choose (IsAlgClosed.exists_pow_nat_eq (zetaSeq ζ (n + 1))
      (Fact.out : p.Prime).pos)

theorem zetaSeq_succ_pow (ζ : ℂ_[p]) (hζ : ζ ^ p = 1) (n : ℕ) :
    zetaSeq p ζ (n + 1) ^ p = zetaSeq p ζ n := by
  rcases n with _ | n
  · simpa [zetaSeq] using hζ
  · exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (zetaSeq p ζ (n + 1))
      (Fact.out : p.Prime).pos)

theorem zetaSeq_pow (ζ : ℂ_[p]) (hζ : ζ ^ p = 1) (n : ℕ) : zetaSeq p ζ n ^ p ^ n = 1 := by
  induction n with
  | zero => simp [zetaSeq]
  | succ n ih => rw [pow_succ', pow_mul, zetaSeq_succ_pow p ζ hζ, ih]

theorem norm_zetaSeq_le (ζ : ℂ_[p]) (hζ : ζ ^ p = 1) (n : ℕ) : ‖zetaSeq p ζ n‖ ≤ 1 := by
  have h := congrArg norm (zetaSeq_pow p ζ hζ n)
  rw [norm_pow, norm_one] at h
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _
    (Fact.out : p.Prime).ne_zero)).mp h).le

/-- **There is `ε ∈ 𝓞_ℂ_p♭` with `ε^♯ = 1` and `ε ≠ 1`**: `ε = (1, ζ_p, ζ_{p²}, …)`. -/
theorem nonempty_tEps : Nonempty (TEps p) := by
  have hdeg : (Polynomial.cyclotomic p ℂ_[p]).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic, Nat.totient_prime (Fact.out : p.Prime)]
    have := (Fact.out : p.Prime).two_le
    exact_mod_cast (show p - 1 ≠ 0 by omega)
  obtain ⟨ζ, hroot⟩ := IsAlgClosed.exists_root _ hdeg
  have hprim : IsPrimitiveRoot ζ p :=
    (Polynomial.isRoot_cyclotomic_iff_charZero (Fact.out : p.Prime).pos).mp hroot
  have hζ : ζ ^ p = 1 := hprim.pow_eq_one
  have hζ1 : ζ ≠ 1 := hprim.ne_one (Fact.out : p.Prime).one_lt
  let c : ℕ → O := fun n => ⟨zetaSeq p ζ n,
    (ZInQ.Contrib.G9.PkgI4.Cp.mem_O_iff p _).mpr (norm_zetaSeq_le p ζ hζ n)⟩
  have hc : ∀ m, c (m + 1) ^ p = c m := fun m =>
    Subtype.ext (by simpa [c] using zetaSeq_succ_pow p ζ hζ m)
  let ε : PreTilt O p := ⟨fun n => Ideal.Quotient.mk _ (c n), fun n => by
    rw [← map_pow, hc]⟩
  have hx : ∀ m, PreTilt.coeff m ε = Ideal.Quotient.mk _ (c m) := fun m => rfl
  refine ⟨⟨ε, ?_, ?_⟩⟩
  · rw [untilt_eq_of_coeff p c hc ε hx]
    exact Subtype.ext (by simp [c, zetaSeq])
  · intro h1
    have h2 := root_eq_of_coeff p c hc ε hx 1
    rw [h1] at h2
    apply hζ1
    have h3 : ZInQ.Contrib.G9.BdrKer.Cp.root (1 : PreTilt O p) 1 = 1 := by
      simp [ZInQ.Contrib.G9.BdrKer.Cp.root]
    rw [h3] at h2
    have := congrArg Subtype.val h2
    simpa [c, zetaSeq] using this.symm

/-- So `tMonoid` contains a non-unit generator and `B_cris^+ → B_cris` inverts `t ≠ 0`. -/
theorem exists_t : ∃ e : TEps p, logOf p e ≠ 0 ∧
    ¬ IsNilpotent (algebraMap (Acris p) (BcrisPlus p) (logOf p e)) := by
  obtain ⟨e⟩ := nonempty_tEps p
  exact ⟨e, logOf_ne_zero p e, logOf_not_isNilpotent p e⟩

end PanBergerSplit
end PkgI4
end HDec
