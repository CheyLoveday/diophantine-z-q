import ZInQKernel.Contrib.OneProof.PanBergerPrinted

noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace BergerBst

open Module PowerSeries
open scoped TensorProduct

/-! ## §1. Evaluating a power series at an element of `I` in the `I`-adic completion -/

section PSEval

variable {A : Type*} [CommRing A] (I : Ideal A) {x : A}

theorem eval_mem_pow_of_coeff (hx : x ∈ I) (n : ℕ) (Q : Polynomial A)
    (hQ : ∀ k < n, Q.coeff k = 0) : Q.eval x ∈ I ^ n := by
  have hdvd : (Polynomial.X : Polynomial A) ^ n ∣ Q := by
    rw [Polynomial.X_pow_dvd_iff]
    exact hQ
  obtain ⟨R, rfl⟩ := hdvd
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hx n)

/-- `P(x) ≡ (P mod X^n)(x) mod I^n`. -/
theorem eval_sub_trunc_mem (hx : x ∈ I) (n : ℕ) (P : Polynomial A) :
    P.eval x - (trunc n (P : A⟦X⟧)).eval x ∈ I ^ n := by
  rw [← Polynomial.eval_sub]
  refine eval_mem_pow_of_coeff I hx n _ fun k hk => ?_
  rw [Polynomial.coeff_sub, coeff_trunc, if_pos hk, Polynomial.coeff_coe, sub_self]

theorem trunc_cauchy (hx : x ∈ I) (f : A⟦X⟧) (n : ℕ) :
    (trunc n f).eval x ≡ (trunc (n + 1) f).eval x [SMOD (I ^ n • ⊤ : Submodule A A)] := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Polynomial.eval_sub]
  refine eval_mem_pow_of_coeff I hx n _ fun k hk => ?_
  rw [Polynomial.coeff_sub, coeff_trunc, coeff_trunc, if_pos hk, if_pos (by omega), sub_self]

/-- The `I`-adic limit of the truncations `Σ_{k<n} a_k x^k`. -/
def psEvalFun (hx : x ∈ I) (f : A⟦X⟧) : AdicCompletion I A :=
  AdicCompletion.mk I A (AdicCompletion.AdicCauchySequence.mk I A
    (fun n => (trunc n f).eval x) (trunc_cauchy I hx f))

theorem evalₐ_psEvalFun (hx : x ∈ I) (f : A⟦X⟧) (n : ℕ) :
    AdicCompletion.evalₐ I n (psEvalFun I hx f) = Ideal.Quotient.mk (I ^ n) ((trunc n f).eval x) := by
  unfold psEvalFun
  rw [AdicCompletion.evalₐ_mk]
  rfl

theorem mk_eval_trunc (hx : x ∈ I) (n : ℕ) (P : Polynomial A) :
    Ideal.Quotient.mk (I ^ n) ((trunc n (P : A⟦X⟧)).eval x) = Ideal.Quotient.mk (I ^ n) (P.eval x) := by
  rw [Ideal.Quotient.eq]
  have := eval_sub_trunc_mem I hx n P
  rw [← neg_sub]
  exact Submodule.neg_mem _ this

/-- **Evaluation at `x ∈ I`**, `A⟦X⟧ → Â_I`, `Σ a_k X^k ↦ Σ a_k x^k` (an `I`-adic limit). -/
def psEval (hx : x ∈ I) : A⟦X⟧ →+* AdicCompletion I A where
  toFun := psEvalFun I hx
  map_one' := AdicCompletion.ext_evalₐ fun n => by
    rw [evalₐ_psEvalFun, map_one (AdicCompletion.evalₐ I n), ← Polynomial.coe_one, mk_eval_trunc I hx,
      Polynomial.eval_one, map_one]
  map_mul' f g := AdicCompletion.ext_evalₐ fun n => by
    rw [evalₐ_psEvalFun, map_mul (AdicCompletion.evalₐ I n), evalₐ_psEvalFun, evalₐ_psEvalFun,
      ← trunc_trunc_mul_trunc,
      ← Polynomial.coe_mul, mk_eval_trunc I hx, Polynomial.eval_mul, map_mul]
  map_zero' := AdicCompletion.ext_evalₐ fun n => by
    rw [evalₐ_psEvalFun, map_zero (AdicCompletion.evalₐ I n), map_zero (trunc n),
      Polynomial.eval_zero, map_zero]
  map_add' f g := AdicCompletion.ext_evalₐ fun n => by
    rw [evalₐ_psEvalFun, map_add (AdicCompletion.evalₐ I n), evalₐ_psEvalFun, evalₐ_psEvalFun,
      map_add (trunc n), Polynomial.eval_add, map_add]

theorem evalₐ_psEval (hx : x ∈ I) (f : A⟦X⟧) (n : ℕ) :
    AdicCompletion.evalₐ I n (psEval I hx f) = Ideal.Quotient.mk (I ^ n) ((trunc n f).eval x) :=
  evalₐ_psEvalFun I hx f n

/-- Two evaluations agree if the terms agree: `a_k x^k = b_k y^k` for all `k`. -/
theorem psEval_eq_of_terms {y : A} (hx : x ∈ I) (hy : y ∈ I) (f g : A⟦X⟧)
    (h : ∀ k, PowerSeries.coeff k f * x ^ k = PowerSeries.coeff k g * y ^ k) :
    psEval I hx f = psEval I hy g :=
  AdicCompletion.ext_evalₐ fun n => by
    rw [evalₐ_psEval, evalₐ_psEval, Polynomial.eval, Polynomial.eval, eval₂_trunc_eq_sum_range,
      eval₂_trunc_eq_sum_range]
    simp only [RingHom.id_apply, h]

theorem psEval_C (hx : x ∈ I) (a : A) :
    psEval I hx (C a) = algebraMap A (AdicCompletion I A) a := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_psEval, ← Polynomial.coe_C, mk_eval_trunc I hx, Polynomial.eval_C]
  simp

end PSEval

/-! ## §2. `A_max`, `B_max^+`, `log`, `t`, `log [p̃]`, `B_max` and `B_st` inside `B_dR` -/

section Rings

variable (p : ℕ) [Fact p.Prime]

open PanBergerSplit (Ainf AinfP)

/-- `ker θ ⊆ W(𝓞_ℂ_p♭)[1/p]` (`θ` with `p` inverted), the ideal Mathlib's `B_dR^+` completes at. -/
abbrev Ith : Ideal (AinfP p) := RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)

/-- `B_dR^+ → B_dR`. -/
abbrev toBdR : BDeRhamPlus 𝓞_ℂ_[p] p →+* BdR p := algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p)

/-- Evaluation of a power series over `W(𝓞_ℂ_p♭)[1/p]` at `x ∈ ker θ`, as an element of `B_dR^+`
(Mathlib's `BDeRhamPlus` is by definition the `ker θ`-adic completion). -/
def evalB {x : AinfP p} (hx : x ∈ Ith p) : (AinfP p)⟦X⟧ →+* BDeRhamPlus 𝓞_ℂ_[p] p :=
  psEval (Ith p) hx

theorem xi'_mem : ZInQ.Contrib.G9.BdrKer.Cp.xi' p ∈ Ith p := by
  rw [Ith, ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineThetaInvertP_Cp]
  exact Ideal.mem_span_singleton_self _

/-- `ω/p` with `ω = ξ = p − [p̃]`, the generator of `ker θ ⊆ A_inf` of bdr-kertheta. -/
def omegaP : AinfP p := ZInQ.Contrib.G9.BdrKer.Cp.xi' p * qpToLoc p ((p : ℚ_[p])⁻¹)

theorem omegaP_mem : omegaP p ∈ Ith p := Ideal.mul_mem_right _ _ (xi'_mem p)

/-- `a_n → 0` `p`-adically in `A_inf = W(𝓞_ℂ_p♭)`. -/
def PAdicNull (a : ℕ → Ainf p) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, (p : Ainf p) ^ k ∣ a n

/-- Power series over `A_inf` whose coefficients tend to `0` `p`-adically. -/
def restricted : Subring (Ainf p)⟦X⟧ where
  carrier := {f | PAdicNull p fun n => PowerSeries.coeff n f}
  one_mem' k := ⟨1, fun n hn => by
    beta_reduce
    rw [PowerSeries.coeff_one, if_neg (by omega)]
    exact dvd_zero _⟩
  zero_mem' k := ⟨0, fun n _ => by beta_reduce; rw [map_zero]; exact dvd_zero _⟩
  add_mem' {f g} hf hg k := by
    obtain ⟨N, hN⟩ := hf k
    obtain ⟨M, hM⟩ := hg k
    exact ⟨max N M, fun n hn => by
      beta_reduce
      rw [map_add]
      exact dvd_add (hN n (le_of_max_le_left hn)) (hM n (le_of_max_le_right hn))⟩
  neg_mem' {f} hf k := by
    obtain ⟨N, hN⟩ := hf k
    exact ⟨N, fun n hn => by beta_reduce; rw [map_neg]; exact (dvd_neg).mpr (hN n hn)⟩
  mul_mem' {f g} hf hg k := by
    obtain ⟨N, hN⟩ := hf k
    obtain ⟨M, hM⟩ := hg k
    refine ⟨N + M, fun n hn => ?_⟩
    beta_reduce
    rw [PowerSeries.coeff_mul]
    refine Finset.dvd_sum fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    by_cases hi : N ≤ ij.1
    · exact Dvd.dvd.mul_right (hN _ hi) _
    · exact Dvd.dvd.mul_left (hM _ (by omega)) _

/-- **`A_max`** (Berger 2002 §1.2 / Colmez, UNVERIFIED wording): the series `Σ a_n (ω/p)^n`,
`a_n ∈ Ã^+ = A_inf` tending to `0` `p`-adically, `ω` a generator of `ker(θ : A_inf → 𝓞_ℂ_p)`,
as a subring of `B_dR^+`. -/
def Amax : Subring (BDeRhamPlus 𝓞_ℂ_[p] p) :=
  (restricted p).map ((evalB p (omegaP_mem p)).comp
    (PowerSeries.map (algebraMap (Ainf p) (AinfP p))))

/-- The logarithm series `log(1 + X) = Σ_{n ≥ 1} (−1)^{n+1} X^n / n` over `W(𝓞_ℂ_p♭)[1/p]`. -/
def logSeries : (AinfP p)⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (-1) ^ (n + 1) * qpToLoc p ((n : ℚ_[p])⁻¹)

/-- **`log(1 + y) ∈ B_dR^+`** for `y ∈ ker θ`, the `ker θ`-adically convergent series. -/
def logPlus {y : AinfP p} (hy : y ∈ Ith p) : BDeRhamPlus 𝓞_ℂ_[p] p := evalB p hy (logSeries p)

theorem teich_sub_one_mem {ε : PreTilt 𝓞_ℂ_[p] p} (h : PreTilt.untilt ε = 1) :
    algebraMap (Ainf p) (AinfP p) (WittVector.teichmuller p ε - 1) ∈ Ith p := by
  have hk : WittVector.teichmuller p ε - 1 ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) :=
    PanBergerSplit.theta_teich_sub_one p h
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, hc⟩ := hk
  rw [← hc, map_mul, mul_comm]
  exact Ideal.mul_mem_right _ _ (xi'_mem p)

/-- **`log [ε] ∈ B_dR^+`** for `ε ∈ 𝓞_ℂ_p♭` with `ε^♯ = 1`: `log(1 + ([ε] − 1))`. -/
def logTeich {ε : PreTilt 𝓞_ℂ_[p] p} (h : PreTilt.untilt ε = 1) : BDeRhamPlus 𝓞_ℂ_[p] p :=
  logPlus p (teich_sub_one_mem p h)

/-- The inverses in `B_dR` of `log [ε]`, `ε^♯ = 1`, `ε ≠ 1`. Each is `a·t` with `a ∈ ℤ_p ∖ 0`
(`t = log [ε₀]` for a generator `ε₀` of `ℤ_p(1)`), so adjoining them to a `ℚ_p`-algebra
containing `t` is adjoining `1/t`. `Ring.inverse` is the inverse in the field `B_dR`. -/
def tInvSet : Set (BdR p) :=
  {z | ∃ (ε : PreTilt 𝓞_ℂ_[p] p) (h : PreTilt.untilt ε = 1), ε ≠ 1 ∧
    z = Ring.inverse (toBdR p (logTeich p h))}

/-- `[p̃]/p − 1 = −ω/p` (`ω = p − [p̃]`). -/
def pTildeArg : AinfP p := -omegaP p

theorem pTildeArg_mem : pTildeArg p ∈ Ith p := Submodule.neg_mem _ (omegaP_mem p)

/-- **`log [p̃] := log([p̃]/p) ∈ B_dR^+`**, `p̃ = (p, p^{1/p}, …) ∈ 𝓞_ℂ_p♭` (bdr-kertheta's `pFlat`):
`Σ_{n ≥ 1} (−1)^{n+1} ([p̃]/p − 1)^n / n`. -/
def logPTilde : BDeRhamPlus 𝓞_ℂ_[p] p := logPlus p (pTildeArg_mem p)

/-- **`B_max^+ = A_max[1/p]`**, inside `B_dR`. -/
def BmaxPlus : Subalgebra ℚ_[p] (BdR p) := Algebra.adjoin ℚ_[p] (toBdR p '' Amax p)

/-- **`B_max = B_max^+[1/t]`**, inside `B_dR`. -/
def Bmax : Subalgebra ℚ_[p] (BdR p) := Algebra.adjoin ℚ_[p] (toBdR p '' Amax p ∪ tInvSet p)

/-- **`B_st = B_max[log [p̃]]`**, inside `B_dR` (Berger 2002 §1.2, UNVERIFIED wording). -/
def Bst : Subalgebra ℚ_[p] (BdR p) :=
  Algebra.adjoin ℚ_[p] (toBdR p '' Amax p ∪ tInvSet p ∪ {toBdR p (logPTilde p)})

theorem bmaxPlus_le_bmax : BmaxPlus p ≤ Bmax p :=
  Algebra.adjoin_mono Set.subset_union_left

theorem bmax_le_bst : Bmax p ≤ Bst p :=
  Algebra.adjoin_mono Set.subset_union_left

theorem logPTilde_mem_bst : toBdR p (logPTilde p) ∈ Bst p :=
  Algebra.subset_adjoin (Set.mem_union_right _ rfl)

/-- `B_st` is the `B_max`-algebra generated by `log [p̃]`. -/
theorem bst_eq_adjoin :
    Bst p = (Algebra.adjoin (Bmax p) {toBdR p (logPTilde p)}).restrictScalars ℚ_[p] := by
  rw [Bst, Algebra.adjoin_union_eq_adjoin_adjoin]
  rfl

end Rings

/-! ## §3. Fontaine's admissibility for a `G_{ℚ_p}`-stable subring `B ⊆ B_dR` -/

section Admissible

variable (p : ℕ) [Fact p.Prime]
variable {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}

/-- **`B^H`**: the elements of `B` fixed by every `σ ∈ H` (a `ℚ_p`-subalgebra of `B`). -/
def fixedSub (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) : Subalgebra ℚ_[p] B where
  carrier := {b | ∀ σ ∈ H, bdrAct p σ (b : BdR p) = b}
  mul_mem' {a b} ha hb σ hσ := by
    simp only [Set.mem_ofPred_eq, Subalgebra.coe_mul, map_mul] at *
    rw [ha σ hσ, hb σ hσ]
  add_mem' {a b} ha hb σ hσ := by
    simp only [Set.mem_ofPred_eq, Subalgebra.coe_add, map_add] at *
    rw [ha σ hσ, hb σ hσ]
  algebraMap_mem' c σ _ := by
    change bdrAct p σ (algebraMap ℚ_[p] (BdR p) c) = algebraMap ℚ_[p] (BdR p) c
    exact bdrAct_qpToBdR p σ c

/-- `B ⊗_{ℚ_p} V → B_dR ⊗_{ℚ_p} V`. -/
def inclT (B : Subalgebra ℚ_[p] (BdR p)) :
    (B ⊗[ℚ_[p]] (Fin n → E)) →ₗ[ℚ_[p]] (BdR p ⊗[ℚ_[p]] (Fin n → E)) :=
  TensorProduct.map B.val.toLinearMap LinearMap.id

theorem inclT_smul (B : Subalgebra ℚ_[p] (BdR p)) (b : B) (x : B ⊗[ℚ_[p]] (Fin n → E)) :
    inclT p B (b • x) = (b : BdR p) • inclT p B x := by
  induction x using TensorProduct.inductionOn with
  | tmul c v =>
    rw [TensorProduct.smul_tmul', inclT, TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul']
    rfl
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem tensorAct_smul (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) (b : BdR p)
    (y : BdR p ⊗[ℚ_[p]] (Fin n → E)) :
    TensorProduct.map (PanBergerSplit.bdrLin p σ) (PanBergerSplit.vAct p ρ σ) (b • y) =
      bdrAct p σ b • TensorProduct.map (PanBergerSplit.bdrLin p σ) (PanBergerSplit.vAct p ρ σ) y := by
  induction y using TensorProduct.inductionOn with
  | tmul c v =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul']
    change bdrAct p σ (b * c) ⊗ₜ _ = (bdrAct p σ b * bdrAct p σ c) ⊗ₜ _
    rw [map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- **`D_B,H(V) = (B ⊗_{ℚ_p} V)^H`**, Fontaine's functor (Fontaine, Astérisque 223, Exp. III
§1; UNVERIFIED numbering), for `V = E^n` with the action `ρ`: the elements of `B ⊗ V` fixed by
`H`, the action computed in `B_dR ⊗ V`. A module over `B^H` (multiplication on `B`). -/
def dB (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    Submodule (fixedSub p B H) (B ⊗[ℚ_[p]] (Fin n → E)) where
  carrier := {x | inclT p B x ∈ PanBergerSplit.tensorInv p (PanBergerSplit.bdrLin p) H ρ}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact Submodule.zero_mem _
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact Submodule.add_mem _ hx hy
  smul_mem' e x hx := by
    simp only [Set.mem_ofPred_eq] at *
    intro σ hσ
    have h1 : inclT p B (e • x) = ((e : B) : BdR p) • inclT p B x := inclT_smul p B (e : B) x
    rw [h1, tensorAct_smul, hx σ hσ, e.2 σ hσ]

/-- **`V` is `B`-admissible as a representation of `H`** (Fontaine's definition):
`dim_{B^H} (B ⊗_{ℚ_p} V)^H = dim_{ℚ_p} V`. -/
def IsAdmissible (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p))
    (ρ : GQp p →* GL (Fin n) E) : Prop :=
  @finrank (fixedSub p B H) (dB p B H ρ) _ (Submodule.addCommMonoid _)
    (Submodule.module (dB p B H ρ)) = finrank ℚ_[p] (Fin n → E)

end Admissible

end BergerBst
end PkgI4
end HDec
