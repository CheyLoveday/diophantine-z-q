import ZInQKernel.Contrib.OneProof.PanBerger
import ZInQKernel.Contrib.G9.KerTheta

/-!
# Sanity checks of pb-bypass's period rings and of `LocalIsPst` (task pb-sanity)

`ZInQKernel/Contrib/OneProof/PanBerger.lean` (task pb-bypass) defines `A_cris`, `B_cris^+`,
`log [ε]`, `B_cris`, `B_st = B_cris[u]` with its action of `G_{ℚ_p}`, and `LocalIsPst`, and splits
the research field `r11r12` into `PanPrinted` and `BergerPrinted`. Those two leaves are genuine only
if the definitions are not degenerate. This file proves, with no `sorry` (only `propext`, `Classical.choice`, `Quot.sound`):

* **Non-degeneracy.** `p^m · ∏ log [ε_i] ≠ 0` in `A_cris` for every finite family with
  `ε_i^♯ = 1`, `ε_i ≠ 1` (`pow_mul_prod_logOf_ne_zero`); hence `0 ∉ tMonoid`, and `B_cris^+`,
  `B_cris`, `B_st` are not the zero ring (`nontrivial_bcrisPlus`, `nontrivial_bcris`,
  `nontrivial_bst`); `log [ε]` is not nilpotent in `B_cris^+` (`logOf_not_isNilpotent`); such `ε`
  exist (`nonempty_tEps`, `ε = (1, ζ_p, ζ_{p²}, …)`); `ℚ_p → B_st` is injective. The argument uses
  only `A_inf`: `ker θ = (ξ)` (`Contrib/G9/KerTheta.lean`), `ξ`-adic separatedness of
  `A_inf`, the lattice bound `N! · A_cris^0 ⊆ A_inf + ξ^N A_inf[1/p]` and the leading
  coefficient under `θ[1/p]`.
* **The action.** `G_{ℚ_p}` acts on `B_cris` by ring automorphisms (`bcrisAut`, a group
  homomorphism); every `σ` acts on `B_st` by a ring automorphism (`stEquiv`), `1` acts trivially
  (`stAct_one`); the group law on `B_st` is equivalent to the cocycle identity for `log [u_σ]`
  (`stAct_mul_iff`) and follows from the additivity of `log` on `{ε : ε^♯ = 1}` (`LogAdditive`,
  stated, not proved here; `stAct_mul`).
* **Semistable representations.** A representation trivial on `G_K` is semistable over `K`
  (`isSemistableOver_of_trivial`, any `K`), so representations with finite image on a finite `K`,
  the trivial `n`-dimensional representation (`localIsPst_one`) and the quadratic characters
  `σ ↦ σ(α)/α` (`isPst_quadChar`) are potentially semistable.

Not proved (see `docs/research/pb-sanity.md`): `B_st^{G_K} = K_0` (in particular its finite
dimensionality, which `IsSemistableOver` needs to mean Fontaine's condition), `LogAdditive`, and a
representation that fails `LocalIsPst`.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace PanBergerSplit

open Ideal

variable (p : ℕ) [Fact p.Prime]



/-- An element of `𝓞_ℂ_p♭` divisible by every power of `p♭` is zero. -/
theorem tilt_eq_zero_of_dvd (ϖ : PreTilt 𝓞_ℂ_[p] p) (hϖ : ϖ.untilt = p) (c : PreTilt 𝓞_ℂ_[p] p)
    (h : ∀ n, ϖ ^ n ∣ c) : c = 0 := by
  have h0 : c.untilt = 0 := by
    apply IsHausdorff.haus' (I := span {(p : 𝓞_ℂ_[p])})
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
    (p : Ainf p) * a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n} → a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n} := by
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
      have hx : theta p (ZInQ.Contrib.G9.BdrKer.Cp.xi p) = 0 := by
        rw [← RingHom.mem_ker]
        change (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p)
        rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
        exact Ideal.mem_span_singleton_self _
      rw [hx, zero_pow (Nat.succ_ne_zero n), mul_zero]
    have ha' : a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p)} := by
      rw [← ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
      exact hθ
    obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton'.mp ha'
    have hξ : (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ≠ 0 := ZInQ.Contrib.G9.BdrKer.Cp.xi_ne_zero p
    have h2 : (p : Ainf p) * a' = c * (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n := by
      apply mul_left_cancel₀ hξ
      linear_combination hc.symm
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (ih a' (Ideal.mem_span_singleton'.mpr ⟨c, h2.symm⟩))
    exact Ideal.mem_span_singleton'.mpr ⟨d, by rw [← hd, pow_succ]; ring⟩

theorem mem_xi_pow_of_p_pow_mul (n e : ℕ) (a : Ainf p)
    (h : (p : Ainf p) ^ e * a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n}) : a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n} := by
  induction e generalizing a with
  | zero => simpa using h
  | succ e ih =>
    apply ih
    apply mem_xi_pow_of_p_mul
    rw [pow_succ] at h
    simpa [mul_assoc, mul_comm, mul_left_comm] using h

/-- `A_inf` is `ξ`-adically separated on non-zero elements. -/
theorem exists_not_mem_xi_pow (x : Ainf p) (hx : x ≠ 0) : ∃ n, x ∉ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n} := by
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul x hx
  by_contra hcon
  push Not at hcon
  apply hb
  have hb' : ∀ n, b ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n} := fun n => mem_xi_pow_of_p_pow_mul p n m b (hcon n)
  have h0 : WittVector.constantCoeff (ZInQ.Contrib.G9.BdrKer.Cp.xi p) = -(ZInQ.Contrib.G9.BdrKer.Cp.pFlat p) := by
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
    ∃ (s : ℕ) (w : Ainf p), x = (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ s * w ∧ theta p w ≠ 0 := by
  classical
  have hex := exists_not_mem_xi_pow p x hx
  let N := Nat.find hex
  have hN : x ∉ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ N} := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h0; apply hN; rw [h0, pow_zero, Ideal.span_singleton_one]; trivial
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hxM : x ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ M} := by
    have := Nat.find_min hex (show M < N by omega)
    push Not at this
    exact this
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hxM
  refine ⟨M, w, by rw [← hw, mul_comm], fun hθ => hN ?_⟩
  have : w ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p)} := by
    rw [← ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]; exact hθ
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp this
  rw [hM, ← hw]
  exact Ideal.mem_span_singleton'.mpr ⟨c, by rw [Nat.succ_eq_add_one, pow_succ]; ring⟩

theorem teich_sub_one_ne_zero {ε : PreTilt 𝓞_ℂ_[p] p} (hne : ε ≠ 1) :
    WittVector.teichmuller p ε - 1 ≠ 0 := by
  intro h
  apply hne
  have h1 : WittVector.teichmuller p ε = 1 := sub_eq_zero.mp h
  have := congrArg (fun w => WittVector.coeff w 0) h1
  simpa [WittVector.teichmuller_coeff_zero] using this

/-- `ι(a) ∈ ξ^k A_inf[1/p]` implies `a ∈ ξ^k A_inf`. -/
theorem mem_xi_pow_of_algebraMap (k : ℕ) (a : Ainf p)
    (h : algebraMap (Ainf p) (AinfP p) a ∈ span {algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ k}) :
    a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ k} := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp h
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : Ainf p)) y
  obtain ⟨e, he⟩ := s.2
  apply mem_xi_pow_of_p_pow_mul p k e
  have hinj := IsLocalization.injective (AinfP p)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (ZInQ.Contrib.G9.BdrKer.Cp.witt_p_ne_zero p))
  have : (p : Ainf p) ^ e * a = b * (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ k := by
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
abbrev xiIdeal : Ideal (AinfP p) := span {algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ N}

/-- `A_inf[1/p] / ξ^N`. -/
abbrev Qn := AinfP p ⧸ xiIdeal p N

/-- The class of `ξ^i / i!`. -/
def latGen (i : ℕ) : Qn p N :=
  Ideal.Quotient.mk _ (qpToLoc p ((i.factorial : ℚ_[p])⁻¹) * algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ i)

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
  calc qpToLoc p (i.factorial : ℚ_[p])⁻¹ * algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ i *
        (qpToLoc p (j.factorial : ℚ_[p])⁻¹ * algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ j)
      = qpToLoc p ((i.factorial : ℚ_[p])⁻¹ * (j.factorial : ℚ_[p])⁻¹) *
        (algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ i * algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ j) := by
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
  · have hx' : x ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p)} := by
      rw [← ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]; exact hx
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hx'
    show Ideal.Quotient.mk _ _ ∈ latG p N
    have : Ideal.Quotient.mk (xiIdeal p N) (dpow p n (b * (ZInQ.Contrib.G9.BdrKer.Cp.xi p))) = b ^ n • latGen p N n := by
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
  exact ⟨algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ (i - N), by rw [← pow_add]; congr 1; omega⟩

theorem latG_bound {q : Qn p N} (hq : q ∈ latG p N) :
    ∃ a : Ainf p, (N.factorial : Qn p N) * q = algebraMap (Ainf p) (Qn p N) a := by
  induction hq using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    by_cases hi : N ≤ i
    · exact ⟨0, by rw [latGen_eq_zero p N hi, mul_zero, map_zero]⟩
    · obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial (show i ≤ N by omega)
      refine ⟨(c : Ainf p) * (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ i, ?_⟩
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
abbrev TEps := {ε : PreTilt 𝓞_ℂ_[p] p // PreTilt.untilt ε = 1 ∧ ε ≠ 1}

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
    fontaineThetaInvertP 𝓞_ℂ_[p] p (algebraMap (Ainf p) (AinfP p) a) =
      algebraMap 𝓞_ℂ_[p] (Localization.Away (p : 𝓞_ℂ_[p])) (theta p a) :=
  IsLocalization.Away.lift_eq (p : Ainf p)
    (by simpa using IsLocalization.Away.algebraMap_isUnit (p : 𝓞_ℂ_[p])) a

theorem thetaP_Vsum {x : Ainf p} (hx : theta p x = 0) {M : ℕ} (hM : 1 ≤ M) :
    fontaineThetaInvertP 𝓞_ℂ_[p] p (Vsum p x M) = 1 := by
  have h0 : fontaineThetaInvertP 𝓞_ℂ_[p] p (algebraMap (Ainf p) (AinfP p) x) = 0 := by
    rw [thetaP_algebraMap, hx, map_zero]
  rw [Vsum, map_sum, Finset.sum_eq_single 1]
  · simp
  · intro j hj hj1
    rw [Finset.mem_Ico] at hj
    simp only [map_mul, map_pow, h0, zero_pow (show j - 1 ≠ 0 by omega), mul_zero]
  · intro h; exfalso; apply h; rw [Finset.mem_Ico]; omega

theorem algebraMap_O_injective :
    Function.Injective (algebraMap 𝓞_ℂ_[p] (Localization.Away (p : 𝓞_ℂ_[p]))) :=
  IsLocalization.injective _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (ZInQ.Contrib.G9.BdrKer.Cp.p_ne_zero p))

theorem natCast_O_ne_zero {k : ℕ} (hk : k ≠ 0) : (k : 𝓞_ℂ_[p]) ≠ 0 := by
  intro h
  have h1 : ((k : 𝓞_ℂ_[p]) : ℂ_[p]) = 0 := by rw [h]; rfl
  push_cast at h1
  exact hk (by exact_mod_cast h1)

theorem theta_xi : theta p (ZInQ.Contrib.G9.BdrKer.Cp.xi p) = 0 := by
  rw [← RingHom.mem_ker]
  change (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p)
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
  exact Ideal.mem_span_singleton_self _

theorem prod_logPartialVal_decomp (l : List (TEps p)) (s : TEps p → ℕ) (w : TEps p → Ainf p)
    (hsw : ∀ e : TEps p, WittVector.teichmuller p e.1 - 1 = (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ s e * w e) (M : ℕ) :
    (l.map fun e => logPartialVal p (WittVector.teichmuller p e.1 - 1) M).prod =
      algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ (l.map s).sum * algebraMap (Ainf p) (AinfP p) (l.map w).prod *
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
      WittVector.teichmuller p e.1 - 1 = (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ s * w ∧ theta p w ≠ 0 :=
    fun e => eq_xi_pow_mul p _ (teich_sub_one_ne_zero p e.2.2)
  choose s w hsw hw using hdec
  set X := algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) with hX
  have hX0 : X ≠ 0 := ZInQ.Contrib.G9.BdrKer.Cp.xi'_ne_zero p
  set S := (l.map s).sum with hS
  set N := S + 1 with hN
  have hdecomp : ∀ M : ℕ, (l.map fun e => logPartialVal p (WittVector.teichmuller p e.1 - 1) M).prod
      = X ^ S * algebraMap (Ainf p) (AinfP p) (l.map w).prod *
        (l.map fun e => Vsum p (WittVector.teichmuller p e.1 - 1) M).prod :=
    fun M => prod_logPartialVal_decomp p l s w hsw M
  set c : 𝓞_ℂ_[p] := (N.factorial : 𝓞_ℂ_[p]) * (p : 𝓞_ℂ_[p]) ^ m * (l.map fun e => theta p (w e)).prod with hc
  have hc0 : c ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (natCast_O_ne_zero p (Nat.factorial_ne_zero N))
      (pow_ne_zero _ (ZInQ.Contrib.G9.BdrKer.Cp.p_ne_zero p))) ?_
    intro h0
    rw [List.prod_eq_zero_iff] at h0
    obtain ⟨e, _, he⟩ := List.mem_map.mp h0
    exact hw e he
  intro hP
  have key : ∀ n : ℕ, ∃ a' : Ainf p, c = (p : 𝓞_ℂ_[p]) ^ n * theta p a' := by
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
    have haS : a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ S} := by
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
    have hθ := congrArg (fontaineThetaInvertP 𝓞_ℂ_[p] p) hcancel
    have hV : fontaineThetaInvertP 𝓞_ℂ_[p] p
        (l.map fun e => Vsum p (WittVector.teichmuller p e.1 - 1) (p ^ n)).prod = 1 := by
      rw [map_list_prod, List.map_map]
      apply List.prod_eq_one
      intro y hy
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hy
      exact thetaP_Vsum p (theta_teich_sub_one p e.2.1) (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)
    have hXθ : fontaineThetaInvertP 𝓞_ℂ_[p] p X = 0 := by
      rw [hX, thetaP_algebraMap, theta_xi, map_zero]
    simp only [map_mul, map_add, map_pow, map_natCast, hV, hXθ, thetaP_algebraMap, mul_zero,
      add_zero, mul_one] at hθ
    apply algebraMap_O_injective p
    rw [hc, map_mul, map_mul, map_mul, map_pow, map_natCast, map_natCast, map_pow, map_natCast]
    rw [map_list_prod, List.map_map] at hθ
    exact hθ
  apply hc0
  apply IsHausdorff.haus' (I := span {(p : 𝓞_ℂ_[p])})
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
theorem untilt_eq_of_coeff (c : ℕ → 𝓞_ℂ_[p]) (hc : ∀ m, c (m + 1) ^ p = c m) (x : PreTilt 𝓞_ℂ_[p] p)
    (hx : ∀ m, PreTilt.coeff m x = Ideal.Quotient.mk _ (c m)) : x.untilt = c 0 := by
  have hpow : ∀ k, c k ^ p ^ k = c 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_mul, hc, ih]
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : 𝓞_ℂ_[p])})]
  intro n
  rw [SModEq.sub_mem, ZInQ.Contrib.G9.BdrKer.mem_span_pow_iff']
  have h1 : root x n - c n ∈ span {(p : 𝓞_ℂ_[p])} := by
    rw [← Ideal.Quotient.eq, mk_root, hx]
  have h2 := dvd_sub_pow_of_dvd_sub (Ideal.mem_span_singleton.mp h1) n
  rw [root_pow, hpow] at h2
  obtain ⟨d, hd⟩ := h2
  exact ⟨p * d, by rw [hd]; ring⟩

open ZInQ.Contrib.G9.BdrKer.Cp in
theorem root_eq_of_coeff (c : ℕ → 𝓞_ℂ_[p]) (hc : ∀ m, c (m + 1) ^ p = c m) (x : PreTilt 𝓞_ℂ_[p] p)
    (hx : ∀ m, PreTilt.coeff m x = Ideal.Quotient.mk _ (c m)) (n : ℕ) : root x n = c n := by
  have := untilt_eq_of_coeff p (fun m => c (m + n)) (fun m => by
    simpa [Nat.add_right_comm] using hc (m + n)) (((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[n]) x)
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
  let c : ℕ → 𝓞_ℂ_[p] := fun n => ⟨zetaSeq p ζ n,
    (ZInQ.Contrib.G9.PkgI4.Cp.mem_O_iff p _).mpr (norm_zetaSeq_le p ζ hζ n)⟩
  have hc : ∀ m, c (m + 1) ^ p = c m := fun m =>
    Subtype.ext (by simpa [c] using zetaSeq_succ_pow p ζ hζ m)
  let ε : PreTilt 𝓞_ℂ_[p] p := ⟨fun n => Ideal.Quotient.mk _ (c n), fun n => by
    rw [← map_pow, hc]⟩
  have hx : ∀ m, PreTilt.coeff m ε = Ideal.Quotient.mk _ (c m) := fun m => rfl
  refine ⟨⟨ε, ?_, ?_⟩⟩
  · rw [untilt_eq_of_coeff p c hc ε hx]
    exact Subtype.ext (by simp [c, zetaSeq])
  · intro h1
    have h2 := root_eq_of_coeff p c hc ε hx 1
    rw [h1] at h2
    apply hζ1
    have h3 : ZInQ.Contrib.G9.BdrKer.Cp.root (1 : PreTilt 𝓞_ℂ_[p] p) 1 = 1 := by
      simp [ZInQ.Contrib.G9.BdrKer.Cp.root]
    rw [h3] at h2
    have := congrArg Subtype.val h2
    simpa [c, zetaSeq] using this.symm

/-- So `tMonoid` contains a non-unit generator and `B_cris^+ → B_cris` inverts `t ≠ 0`. -/
theorem exists_t : ∃ e : TEps p, logOf p e ≠ 0 ∧
    ¬ IsNilpotent (algebraMap (Acris p) (BcrisPlus p) (logOf p e)) := by
  obtain ⟨e⟩ := nonempty_tEps p
  exact ⟨e, logOf_ne_zero p e, logOf_not_isNilpotent p e⟩

/-! ### The action of `G_{ℚ_p}`: a group action by ring automorphisms on `B_cris` -/

section Action

theorem cpAct_mul (σ τ : GQp p) (x : ℂ_[p]) : cpAct p (σ * τ) x = cpAct p σ (cpAct p τ x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_cpAct p _) ((continuous_cpAct p σ).comp (continuous_cpAct p τ))
  | ih a => rw [cpAct_coe, cpAct_coe, cpAct_coe, AlgEquiv.mul_apply]

theorem cpAct_one (x : ℂ_[p]) : cpAct p 1 x = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_cpAct p _) continuous_id
  | ih a => rw [cpAct_coe, AlgEquiv.one_apply]

theorem oAct_mul (σ τ : GQp p) : oAct p (σ * τ) = (oAct p σ).comp (oAct p τ) :=
  RingHom.ext fun x => Subtype.ext (cpAct_mul p σ τ x)

theorem oAct_one : oAct p 1 = RingHom.id _ :=
  RingHom.ext fun x => Subtype.ext (cpAct_one p x)

theorem flatAct_mul (σ τ : GQp p) (x : PreTilt 𝓞_ℂ_[p] p) :
    flatAct p (σ * τ) x = flatAct p σ (flatAct p τ x) := by
  apply Perfection.ext
  intro n
  rw [DR.coeff_preTiltMap, DR.coeff_preTiltMap, DR.coeff_preTiltMap]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Perfection.coeff _ p n x)
  rw [← hy]
  change Ideal.Quotient.mk _ (oAct p (σ * τ) y) = Ideal.Quotient.mk _ (oAct p σ (oAct p τ y))
  rw [oAct_mul]
  rfl

theorem flatAct_one (x : PreTilt 𝓞_ℂ_[p] p) : flatAct p 1 x = x := by
  apply Perfection.ext
  intro n
  rw [DR.coeff_preTiltMap]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Perfection.coeff _ p n x)
  rw [← hy]
  change Ideal.Quotient.mk _ (oAct p 1 y) = Ideal.Quotient.mk _ y
  rw [oAct_one]
  rfl

theorem wittMap_flatAct_mul (σ τ : GQp p) (w : Ainf p) :
    WittVector.map (flatAct p (σ * τ)) w =
      WittVector.map (flatAct p σ) (WittVector.map (flatAct p τ) w) := by
  ext n
  rw [WittVector.map_coeff, WittVector.map_coeff, WittVector.map_coeff, flatAct_mul]

theorem wittMap_flatAct_one (w : Ainf p) : WittVector.map (flatAct p 1) w = w := by
  ext n
  rw [WittVector.map_coeff, flatAct_one]

theorem locAct_mul (σ τ : GQp p) : locAct p (σ * τ) = (locAct p σ).comp (locAct p τ) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : Ainf p))
  ext w
  simp only [RingHom.comp_apply, locAct_algebraMap, wittMap_flatAct_mul]

theorem locAct_one : locAct p 1 = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : Ainf p))
  ext w
  simp only [RingHom.comp_apply, locAct_algebraMap, wittMap_flatAct_one, RingHom.id_apply]

theorem acris0Act_mul (σ τ : GQp p) (x : Acris0 p) :
    acris0Act p (σ * τ) x = acris0Act p σ (acris0Act p τ x) :=
  Subtype.ext (by
    change locAct p (σ * τ) x = locAct p σ (locAct p τ x)
    rw [locAct_mul]; rfl)

theorem acris0Act_one (x : Acris0 p) : acris0Act p 1 x = x :=
  Subtype.ext (by
    change locAct p 1 x = x
    rw [locAct_one]; rfl)

theorem adicMap_comp' {A : Type*} [CommRing A] (J : Ideal A) (g g' g'' : A →+* A)
    (hg : J ≤ J.comap g) (hg' : J ≤ J.comap g') (hg'' : J ≤ J.comap g'')
    (h : ∀ a, g'' a = g' (g a)) (x : AdicCompletion J A) :
    DR.adicMap J J g'' hg'' x = DR.adicMap J J g' hg' (DR.adicMap J J g hg x) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [DR.adicMap_evalₐ, DR.adicMap_evalₐ]
  simp only [DR.adicMapAux, RingHom.comp_apply]
  erw [DR.adicMap_evalₐ]
  simp only [DR.adicMapAux, RingHom.comp_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.quotientMap_mk, h]

theorem adicMap_id' {A : Type*} [CommRing A] (J : Ideal A) (g : A →+* A)
    (hg : J ≤ J.comap g) (h : ∀ a, g a = a) (x : AdicCompletion J A) :
    DR.adicMap J J g hg x = x := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [DR.adicMap_evalₐ]
  simp only [DR.adicMapAux, RingHom.comp_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rw [Ideal.quotientMap_mk, h]

theorem acrisAct_mul (σ τ : GQp p) (x : Acris p) :
    acrisAct p (σ * τ) x = acrisAct p σ (acrisAct p τ x) :=
  adicMap_comp' _ _ _ _ _ _ _ (acris0Act_mul p σ τ) x

theorem acrisAct_one (x : Acris p) : acrisAct p 1 x = x :=
  adicMap_id' _ _ _ (acris0Act_one p) x

theorem bcrisPlusAct_mul (σ τ : GQp p) :
    bcrisPlusAct p (σ * τ) = (bcrisPlusAct p σ).comp (bcrisPlusAct p τ) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : Acris p))
  ext a
  simp only [RingHom.comp_apply, bcrisPlusAct_algebraMap, acrisAct_mul]

theorem bcrisPlusAct_one : bcrisPlusAct p 1 = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : Acris p))
  ext a
  simp only [RingHom.comp_apply, bcrisPlusAct_algebraMap, acrisAct_one, RingHom.id_apply]

theorem bcrisAct_mul (σ τ : GQp p) :
    bcrisAct p (σ * τ) = (bcrisAct p σ).comp (bcrisAct p τ) := by
  apply IsLocalization.ringHom_ext (tMonoid p)
  ext a
  simp only [RingHom.comp_apply, bcrisAct_algebraMap, bcrisPlusAct_mul]

theorem bcrisAct_one : bcrisAct p 1 = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (tMonoid p)
  ext a
  simp only [RingHom.comp_apply, bcrisAct_algebraMap, bcrisPlusAct_one, RingHom.id_apply]

theorem bcrisAct_mul_apply (σ τ : GQp p) (x : Bcris p) :
    bcrisAct p (σ * τ) x = bcrisAct p σ (bcrisAct p τ x) := by
  rw [bcrisAct_mul]; rfl

theorem bcrisAct_inv_apply (σ : GQp p) (x : Bcris p) : bcrisAct p σ⁻¹ (bcrisAct p σ x) = x := by
  rw [← bcrisAct_mul_apply, inv_mul_cancel, bcrisAct_one]; rfl

theorem bcrisAct_apply_inv (σ : GQp p) (x : Bcris p) : bcrisAct p σ (bcrisAct p σ⁻¹ x) = x := by
  rw [← bcrisAct_mul_apply, mul_inv_cancel, bcrisAct_one]; rfl

/-- **`G_{ℚ_p}` acts on `B_cris` by ring automorphisms** (a group homomorphism into
`Aut(B_cris)`), fixing `ℚ_p`. -/
def bcrisAut : GQp p →* (Bcris p ≃+* Bcris p) where
  toFun σ := RingEquiv.ofRingHom (bcrisAct p σ) (bcrisAct p σ⁻¹)
    (RingHom.ext fun x => bcrisAct_apply_inv p σ x) (RingHom.ext fun x => bcrisAct_inv_apply p σ x)
  map_one' := RingEquiv.ext fun x => by
    change bcrisAct p 1 x = x
    rw [bcrisAct_one]; rfl
  map_mul' σ τ := RingEquiv.ext fun x => bcrisAct_mul_apply p σ τ x

theorem bcrisAut_apply (σ : GQp p) (x : Bcris p) : bcrisAut p σ x = bcrisAct p σ x := rfl

/-! ### The action on `B_st = B_cris[u]` -/

theorem stAct_X (σ : GQp p) :
    stAct p σ Polynomial.X = Polynomial.X + Polynomial.C (logU p σ) :=
  Polynomial.eval₂_X _ _

/-- The inverse of `stAct σ`. -/
def stActInv (σ : GQp p) : Bst p →+* Bst p :=
  Polynomial.eval₂RingHom (Polynomial.C.comp (bcrisAct p σ⁻¹))
    (Polynomial.X - Polynomial.C (bcrisAct p σ⁻¹ (logU p σ)))

theorem stActInv_comp (σ : GQp p) : (stActInv p σ).comp (stAct p σ) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, stAct_C, stActInv, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C, bcrisAct_inv_apply, RingHom.id_apply]
  · simp only [RingHom.comp_apply, stAct_X, stActInv, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, RingHom.id_apply]
    ring

theorem stAct_comp_inv (σ : GQp p) : (stAct p σ).comp (stActInv p σ) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, stActInv, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C, stAct_C, bcrisAct_apply_inv, RingHom.id_apply]
  · simp only [RingHom.comp_apply, stActInv, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, map_sub, stAct_X, stAct_C,
      bcrisAct_apply_inv, RingHom.id_apply]
    ring

/-- **Each `σ ∈ G_{ℚ_p}` acts on `B_st` by a ring automorphism** (unconditionally). -/
def stEquiv (σ : GQp p) : Bst p ≃+* Bst p :=
  RingEquiv.ofRingHom (stAct p σ) (stActInv p σ) (stAct_comp_inv p σ) (stActInv_comp p σ)

theorem stEquiv_apply (σ : GQp p) (x : Bst p) : stEquiv p σ x = stAct p σ x := rfl

theorem stAct_bijective (σ : GQp p) : Function.Bijective (stAct p σ) :=
  (stEquiv p σ).bijective

/-- `log [ε] = 0` when `[ε] - 1 = 0`, i.e. `log [1] = 0`. -/
theorem logT_of_eq_zero {x : Ainf p} (hx : theta p x = 0) (h0 : x = 0) : logT p hx = 0 := by
  subst h0
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_logT, map_zero]
  have : logPartial p hx (p ^ n) = 0 := by
    apply Subtype.ext
    change logPartialVal p 0 (p ^ n) = 0
    rw [logPartialVal]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_Ico] at hj
    simp only [logTerm, dpow, map_zero, zero_pow (show j ≠ 0 by omega), mul_zero]
  rw [this, map_zero]

theorem pFlat_untilt : PreTilt.untilt (pFlat p) = (p : 𝓞_ℂ_[p]) :=
  Classical.epsilon_spec (p := fun x : PreTilt 𝓞_ℂ_[p] p => PreTilt.untilt x = (p : 𝓞_ℂ_[p]))
    ⟨ZInQ.Contrib.G9.BdrKer.Cp.pFlat p, ZInQ.Contrib.G9.BdrKer.Cp.untilt_pFlat p⟩

theorem untilt_zero' : PreTilt.untilt (0 : PreTilt 𝓞_ℂ_[p] p) = 0 :=
  untilt_eq_of_coeff p (fun _ => 0) (fun _ => zero_pow (Fact.out : p.Prime).ne_zero) 0
    (fun m => by rw [map_zero, map_zero])

theorem pFlat_ne_zero : pFlat p ≠ 0 := by
  intro h
  have := pFlat_untilt p
  rw [h, untilt_zero'] at this
  exact ZInQ.Contrib.G9.BdrKer.Cp.p_ne_zero p this.symm

theorem uSigma_spec (σ : GQp p) : uSigma p σ * pFlat p = flatAct p σ (pFlat p) := by
  apply Classical.epsilon_spec (p := fun u => u * pFlat p = flatAct p σ (pFlat p))
  -- existence: `σ♭(p♭)/p♭`, via `𝓞_ℂ_p♭` being a valuation-type domain: use `dvd_of_coeff_zero`
  have hu : PreTilt.untilt (flatAct p σ (pFlat p)) = (p : 𝓞_ℂ_[p]) := by
    rw [DR.untilt_preTiltMap, pFlat_untilt, map_natCast]
  obtain ⟨d, hd⟩ := ZInQ.Contrib.G9.BdrKer.Cp.dvd_of_coeff_zero p (pFlat p) (pFlat_untilt p)
    (flatAct p σ (pFlat p)) (by
      rw [← PreTilt.mk_untilt_eq_coeff_zero, hu, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _)
  exact ⟨d, by rw [hd, mul_comm]⟩

theorem untilt_uSigma (σ : GQp p) : PreTilt.untilt (uSigma p σ) = 1 := by
  have h := congrArg PreTilt.untilt (uSigma_spec p σ)
  rw [map_mul, DR.untilt_preTiltMap, pFlat_untilt, map_natCast] at h
  have hp := ZInQ.Contrib.G9.BdrKer.Cp.p_ne_zero p
  exact mul_right_cancel₀ hp (by rw [h, one_mul])

theorem uSigma_one : uSigma p 1 = 1 := by
  have h := uSigma_spec p 1
  rw [flatAct_one] at h
  exact mul_right_cancel₀ (pFlat_ne_zero p) (by rw [h, one_mul])

theorem uSigma_mul (σ τ : GQp p) : uSigma p (σ * τ) = flatAct p σ (uSigma p τ) * uSigma p σ := by
  apply mul_right_cancel₀ (pFlat_ne_zero p)
  rw [uSigma_spec, flatAct_mul, ← uSigma_spec p τ, map_mul, ← uSigma_spec p σ]
  ring

/-- `logU σ` is the image of `log [u_σ]` (the `else` branch never occurs). -/
theorem logU_eq (σ : GQp p) : logU p σ = algebraMap (BcrisPlus p) (Bcris p)
    (algebraMap (Acris p) (BcrisPlus p) (logT p (theta_teich_sub_one p (untilt_uSigma p σ)))) := by
  rw [logU, dite_eq_left_of_eq_true (eq_true (untilt_uSigma p σ))]

theorem logU_one : logU p 1 = 0 := by
  rw [logU_eq, logT_of_eq_zero p _ (by rw [uSigma_one, map_one, sub_self]), map_zero, map_zero]

/-- **`1 ∈ G_{ℚ_p}` acts trivially on `B_st`.** -/
theorem stAct_one : stAct p 1 = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro b; rw [stAct_C, bcrisAct_one]; rfl
  · rw [stAct_X, logU_one, map_zero, add_zero]; rfl

/-- **The group law on `B_st` is exactly the cocycle identity for `σ ↦ log [u_σ]`.** -/
theorem stAct_mul_iff (σ τ : GQp p) :
    stAct p (σ * τ) = (stAct p σ).comp (stAct p τ) ↔
      logU p (σ * τ) = logU p σ + bcrisAct p σ (logU p τ) := by
  constructor
  · intro h
    have hX := congrArg (fun φ : Bst p →+* Bst p => φ Polynomial.X) h
    simp only [RingHom.comp_apply, stAct_X, map_add, stAct_C] at hX
    have := congrArg (Polynomial.coeff · 0) hX
    simpa [add_comm] using this
  · intro h
    apply Polynomial.ringHom_ext
    · intro b
      simp only [RingHom.comp_apply, stAct_C, bcrisAct_mul_apply]
    · simp only [RingHom.comp_apply, stAct_X, map_add, stAct_C, h]
      ring

/-- **`log` is additive on `{ε : ε^♯ = 1}`** (Fontaine; `log [xy] = log [x] + log [y]` in
`A_cris`). Standard (the formal identity `log((1+a)(1+b)) = log(1+a) + log(1+b)` with divided
powers); not proved here. It is the only missing input for the group law of `stAct`. -/
def LogAdditive : Prop :=
  ∀ (x y : PreTilt 𝓞_ℂ_[p] p) (hx : PreTilt.untilt x = 1) (hy : PreTilt.untilt y = 1)
    (hxy : PreTilt.untilt (x * y) = 1),
    logT p (theta_teich_sub_one p hxy) =
      logT p (theta_teich_sub_one p hx) + logT p (theta_teich_sub_one p hy)

theorem logT_congr {x y : Ainf p} (hx : theta p x = 0) (hy : theta p y = 0) (h : x = y) :
    logT p hx = logT p hy := by
  subst h; rfl

theorem logU_mul (hL : LogAdditive p) (σ τ : GQp p) :
    logU p (σ * τ) = logU p σ + bcrisAct p σ (logU p τ) := by
  have h1 : PreTilt.untilt (flatAct p σ (uSigma p τ)) = 1 := by
    rw [DR.untilt_preTiltMap, untilt_uSigma, map_one]
  have h2 : PreTilt.untilt (flatAct p σ (uSigma p τ) * uSigma p σ) = 1 := by
    rw [map_mul, h1, untilt_uSigma, one_mul]
  rw [logU_eq, logU_eq, logU_eq, bcrisAct_algebraMap, bcrisPlusAct_algebraMap,
    acrisAct_logT p σ _ (by rw [theta_wittMap, theta_teich_sub_one p (untilt_uSigma p τ),
      map_zero])]
  have e1 : logT p (theta_teich_sub_one p (untilt_uSigma p (σ * τ))) =
      logT p (theta_teich_sub_one p h2) :=
    logT_congr p _ _ (by rw [uSigma_mul])
  have e2 : logT p (by rw [theta_wittMap, theta_teich_sub_one p (untilt_uSigma p τ), map_zero] :
        theta p (WittVector.map (flatAct p σ) (WittVector.teichmuller p (uSigma p τ) - 1)) = 0) =
      logT p (theta_teich_sub_one p h1) :=
    logT_congr p _ _ (by rw [map_sub, map_one, WittVector.map_teichmuller])
  rw [e1, e2, hL _ _ h1 (untilt_uSigma p σ) h2, RingHom.map_add, RingHom.map_add, add_comm]

/-- **Given `LogAdditive`, `G_{ℚ_p}` acts on `B_st` by ring automorphisms** (group law). -/
theorem stAct_mul (hL : LogAdditive p) (σ τ : GQp p) :
    stAct p (σ * τ) = (stAct p σ).comp (stAct p τ) :=
  (stAct_mul_iff p σ τ).mpr (logU_mul p hL σ τ)

end Action

/-! ### Potentially trivial representations are potentially semistable -/

section Pst

variable {n : ℕ}

theorem finrank_fun_eq {W : Type} [AddCommGroup W] [Module ℚ_[p] W] (N : ℕ) :
    Module.finrank ℚ_[p] (Fin N → W) = N * Module.finrank ℚ_[p] W := by
  rw [Module.finrank, rank_pi, Cardinal.sum_const', Cardinal.toNat_mul, Cardinal.mk_fin,
    Cardinal.toNat_natCast]
  rfl

theorem finrank_linearMap_eq {V W : Type} [AddCommGroup V] [Module ℚ_[p] V]
    [FiniteDimensional ℚ_[p] V] [AddCommGroup W] [Module ℚ_[p] W] :
    Module.finrank ℚ_[p] (V →ₗ[ℚ_[p]] W) =
      Module.finrank ℚ_[p] V * Module.finrank ℚ_[p] W := by
  let b := Module.finBasis ℚ_[p] V
  rw [← (b.constr ℚ_[p]).finrank_eq, finrank_fun_eq]

/-- **A representation trivial on `G_K` is semistable over `K`** (for every `K`, with no
finiteness hypothesis): `D_st,K ≅ Hom(V, B_st^{G_K})`. -/
theorem isSemistableOver_of_trivial (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    {E : Type} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
    (ρ : GQp p →* GL (Fin n) E) (h : ∀ σ ∈ K.fixingSubgroup, ρ σ = 1) :
    IsSemistableOver p K ρ := by
  let F : dstSpace p K ρ →ₗ[ℚ_[p]] ((Fin n → E) →ₗ[ℚ_[p]] bstInv p K) :=
    { toFun := fun φ => LinearMap.codRestrict (bstInv p K)
        (φ : (Fin n → E) →ₗ[ℚ_[p]] Bst p) (fun v σ hσ => by
          have := φ.2 σ hσ v
          rw [h σ hσ, Units.val_one, Matrix.one_mulVec] at this
          exact this.symm)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let G : ((Fin n → E) →ₗ[ℚ_[p]] bstInv p K) →ₗ[ℚ_[p]] dstSpace p K ρ :=
    { toFun := fun ψ => ⟨(bstInv p K).subtype ∘ₗ ψ, fun σ hσ v => by
          rw [h σ hσ, Units.val_one, Matrix.one_mulVec]
          exact ((ψ v).2 σ hσ).symm⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let L : dstSpace p K ρ ≃ₗ[ℚ_[p]] ((Fin n → E) →ₗ[ℚ_[p]] bstInv p K) :=
    LinearEquiv.ofLinearMap F G (LinearMap.ext fun ψ => LinearMap.ext fun v => rfl)
      (LinearMap.ext fun φ => Subtype.ext (LinearMap.ext fun v => rfl))
  rw [IsSemistableOver, L.finrank_eq, finrank_linearMap_eq, finrank_fun_eq, mul_comm]

/-- **A representation trivial on `G_K` for a finite `K` is potentially semistable.** -/
theorem isPst_of_trivial_on {E : Type} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
    (ρ : GQp p →* GL (Fin n) E) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (h : ∀ σ ∈ K.fixingSubgroup, ρ σ = 1) : IsPst p ρ :=
  ⟨K, inferInstance, isSemistableOver_of_trivial p K ρ h⟩

/-- The trivial `n`-dimensional `ℚ̄_p`-representation satisfies `LocalIsPst`. -/
theorem localIsPst_one (n : ℕ) : LocalIsPst p n 1 := by
  refine ⟨⊥, inferInstance, 1, fun σ => by simp, ?_⟩
  exact isPst_of_trivial_on p 1 ⊥ fun _ _ => rfl

/-! #### Quadratic characters -/

variable {p} in
theorem gqp_apply_sq_root {α : PadicAlgCl p} {c : ℚ_[p]} (hα : α ^ 2 = algebraMap ℚ_[p] _ c)
    (σ : GQp p) : σ α = α ∨ σ α = -α := by
  have h : (σ α - α) * (σ α + α) = 0 := by
    have : σ α ^ 2 = α ^ 2 := by rw [← map_pow, hα, AlgEquiv.commutes]
    linear_combination this
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- The quadratic character `σ ↦ σ(α)/α ∈ {±1}` of `α ∈ ℚ̄_p^×` with `α² ∈ ℚ_p`
(unramified when `α²` is a non-square unit, `p` odd). -/
def quadChar {α : PadicAlgCl p} {c : ℚ_[p]} (hα : α ^ 2 = algebraMap ℚ_[p] _ c) (h0 : α ≠ 0) :
    GQp p →* GL (Fin 1) ℚ_[p] where
  toFun σ := haveI := Classical.propDecidable; if σ α = α then 1 else -1
  map_one' := by simp
  map_mul' σ τ := by
    classical
    have hne : -α ≠ α := fun h => h0 (by
      have : (2 : PadicAlgCl p) * α = 0 := by linear_combination -h
      exact (mul_eq_zero.mp this).resolve_left two_ne_zero)
    have hmul : (σ * τ) α = σ (τ α) := rfl
    rcases gqp_apply_sq_root hα τ with hτ | hτ
    · rw [hmul, hτ]; simp
    · rcases gqp_apply_sq_root hα σ with hσ | hσ
      · rw [hmul, hτ, map_neg, hσ]; simp [hne]
      · rw [hmul, hτ, map_neg, hσ, neg_neg]; simp [hne]

/-- **Every quadratic character of `G_{ℚ_p}` of the form `σ(α)/α` is potentially semistable**
(it is trivial on `G_{ℚ_p(α)}`). -/
theorem isPst_quadChar {α : PadicAlgCl p} {c : ℚ_[p]} (hα : α ^ 2 = algebraMap ℚ_[p] _ c)
    (h0 : α ≠ 0) : IsPst p (quadChar p hα h0) := by
  have hint : IsIntegral ℚ_[p] α := Algebra.IsIntegral.isIntegral α
  have : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] {α}) :=
    IntermediateField.adjoin.finiteDimensional hint
  refine isPst_of_trivial_on p _ (IntermediateField.adjoin ℚ_[p] {α}) fun σ hσ => ?_
  have : σ α = α := hσ ⟨α, IntermediateField.mem_adjoin_simple_self ℚ_[p] α⟩
  simp [quadChar, this]

end Pst

/-! ### Summary -/

/-- **Summary of the unconditional sanity checks** of pb-bypass's definitions. -/
theorem panBerger_definitions_nondegenerate :
    Nontrivial (BcrisPlus p) ∧ Nontrivial (Bcris p) ∧ Nontrivial (Bst p) ∧
      (0 : BcrisPlus p) ∉ tMonoid p ∧
      (∃ e : TEps p, logOf p e ≠ 0 ∧
        ¬ IsNilpotent (algebraMap (Acris p) (BcrisPlus p) (logOf p e))) ∧
      Function.Injective (algebraMap ℚ_[p] (Bst p)) ∧
      (∀ σ : GQp p, Function.Bijective (stAct p σ)) ∧ stAct p 1 = RingHom.id _ ∧
      (∀ σ τ : GQp p, bcrisAct p (σ * τ) = (bcrisAct p σ).comp (bcrisAct p τ)) ∧
      (∀ n : ℕ, LocalIsPst p n 1) :=
  ⟨inferInstance, inferInstance, inferInstance, zero_notMem_tMonoid p, exists_t p,
    algebraMap_qp_bst_injective p, stAct_bijective p, stAct_one p, bcrisAct_mul p,
    localIsPst_one p⟩

end PanBergerSplit
end PkgI4
end HDec
