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

instance (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    Module (fixedSub p B H) (dB p B H ρ) := Submodule.module _

/-- **`V` is `B`-admissible as a representation of `H`** (Fontaine's definition):
`dim_{B^H} (B ⊗_{ℚ_p} V)^H = dim_{ℚ_p} V`. -/
def IsAdmissible (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p))
    (ρ : GQp p →* GL (Fin n) E) : Prop :=
  finrank (fixedSub p B H) (dB p B H ρ) = finrank ℚ_[p] (Fin n → E)

end Admissible

/-! ## §4. Semistable and potentially semistable over Berger's `B_st`; the two leaves -/

section Predicates

variable (p : ℕ) [Fact p.Prime]
variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {n : ℕ}

/-- **`V|_{G_K}` is semistable** (Fontaine; Berger 2002 §1.2): `B_st`-admissible as a
representation of `G_K`, i.e. `dim_{B_st^{G_K}} (B_st ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V`, with
`B_st = B_max[log [p̃]] ⊆ B_dR` (`Bst`). -/
def IsSemistableB (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (ρ : GQp p →* GL (Fin n) E) :
    Prop :=
  IsAdmissible p (Bst p) K.fixingSubgroup ρ

/-- **`V` is potentially semistable**: semistable over some finite `K/ℚ_p` inside `ℚ̄_p`. -/
def IsPstB (ρ : GQp p →* GL (Fin n) E) : Prop :=
  ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ IsSemistableB p K ρ

/-- A `ℚ̄_p`-valued representation of `G_{ℚ_p}` is potentially semistable: it has a model over a
finite `E ⊆ ℚ̄_p` whose underlying `ℚ_p`-representation `E^n` is potentially semistable. -/
def LocalIsPstB (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    IsPstB p ρE

end Predicates

open PanBergerSplit in
/-- **Berger, Théorème 0.7** (L. Berger, *Représentations p-adiques et équations
différentielles*, Invent. Math. 148 (2002), 219-284; Théorème 0.7 = Corollaire 5.22 of the
published version (locator audit row R11) = Théorème 0.6 = Théorème 5.19 of
arXiv:math/0102179v3), at `K = ℚ_p`: every de Rham representation of `G_{ℚ_p}` is potentially
semistable. Applied to the `ℚ_p`-representation `V = E^n` underlying a continuous `ρ` with
values in `GL_n(E)`, `E/ℚ_p` finite inside `ℚ̄_p`, both conditions computed on `V`:

* de Rham: `dim_{ℚ_p} (B_dR ⊗_{ℚ_p} V)^{G_{ℚ_p}} = dim_{ℚ_p} V` (`LocalIsDeRhamU`; `K = ℚ_p`);
* potentially semistable: for some finite `K/ℚ_p` in `ℚ̄_p`,
  `dim_{B_st^{G_K}} (B_st ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V` (`LocalIsPstB`), with Berger's
  `B_st = B_max[log [p̃]] ⊆ B_dR`, `B_max = B_max^+[1/t]`, `B_max^+ = A_max[1/p]`,
  `A_max = {Σ a_n (ω/p)^n : a_n ∈ A_inf, a_n → 0}` (`Bst`, `Bmax`, `BmaxPlus`, `Amax`). -/
def BergerPrintedB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)),
    Continuous ρ → LocalIsDeRhamU p n ρ → LocalIsPstB p n ρ

open PanBergerSplit in
/-- **Pan, Theorem 1.0.4**, as pb-fix2's `PanPrintedU` with potential semistability computed
over Berger's `B_st ⊆ B_dR` (`LocalIsPstB`) instead of pb-bypass's abstract `B_cris[X]`.
Everything else is `PanPrintedU` verbatim (eigenform reading flagged there). -/
def PanPrintedB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (ιp : PadicAlgCl p ≃+* ℂ) (ρ : GaloisRep p 2),
    ρ.IsIrreducible → ρ.FinitelyRamified → LocalIsPstB p 2 (ρ.restrictLocal p) → ρ.IsOdd →
    LocalDistinctHTU p (ρ.restrictLocal p) →
    ∃ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k), 0 < N ∧ 1 ≤ k ∧
      IsNormalizedEigenform g χ ∧
      ∃ (ψ : GaloisChar p) (S : Finset ℕ), ∀ q : ℕ, q.Prime → q ∉ S →
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v q → IsArithFrob σ v q →
          (ρ.mat σ⁻¹).trace = (ψ.toHom σ⁻¹ : PadicAlgCl p) * ιp.symm (coeff g q)

open PanBergerSplit in
/-- **`PanBerger` (the research field `r11r12`) from Pan's and Berger's theorems, potential
semistability over Berger's `B_st ⊆ B_dR`**: pb-fix2's proof verbatim. -/
theorem panBerger_of_printedB (hP : PanPrintedB) (hB : BergerPrintedB)
    (hD : ZInQ.Contrib.HodgeSplit.DSThm965) (hDS : ZInQ.Contrib.HodgeSplit.DSThm966) :
    PanBerger := by
  intro p _ hp ρ hirr hfr hdr hodd hdist
  have hdr' : LocalIsDeRhamU p 2 ((dualRep ρ).restrictLocal p) := by
    rw [dualRep_restrictLocal]
    exact localIsDeRhamU_dualHom p _ hdr
  have hpst' := hB p 2 _ ((dualRep ρ).continuous_toHom.comp
    (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous) hdr'
  have hht' : LocalDistinctHTU p ((dualRep ρ).restrictLocal p) := by
    rw [dualRep_restrictLocal]
    exact localDistinctHTU_dualHom p ρ hdist
  obtain ⟨Φ⟩ := exists_complex_equiv p
  obtain ⟨N, k, χ, g, hN, hk, hg, ψ, S, htr⟩ := hP p hp Φ.symm (dualRep ρ)
    (dualRep_isIrreducible ρ hirr) (dualRep_finitelyRamified ρ hfr) hpst'
    (dualRep_isOdd ρ hodd) hht'
  obtain ⟨Sr, hSr⟩ := hfr
  let ιC : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let ιL : Qbar →ₐ[ℚ] PadicAlgCl p := (Φ : ℂ →+* PadicAlgCl p).toRatAlgHom.comp ιC
  refine ⟨N, k, χ, g, hN, hk, hg, charInv ψ, ιC, ιL, S ∪ Sr ∪ Finset.range (N * p + 1), ?_⟩
  intro q hq hqS
  simp only [Finset.mem_union, Finset.mem_range, not_or, not_lt] at hqS
  obtain ⟨⟨hqS, hqSr⟩, hqNp⟩ := hqS
  have hNp : 0 < N * p := Nat.mul_pos hN (Fact.out : p.Prime).pos
  have hqdvd : ¬ q ∣ N * p := fun h => by
    have := Nat.le_of_dvd hNp h
    omega
  refine ⟨hSr q hq hqSr, ?_⟩
  obtain ⟨α, hα⟩ := coeff_mem_range hD hDS p ιC ιL hN hk hg hq hqdvd
  refine ⟨α, hα, fun v σ hv hσ => ?_⟩
  have h1 := htr q hq hqS v σ hv hσ
  rw [trace_dualRep_inv] at h1
  rw [h1, charInv_apply]
  congr 1
  change Φ.symm.symm (coeff g q) = Φ (ιC α)
  rw [hα]
  rfl

/-! ## §5. Sanity: the trivial representation is admissible for every `B` and `H` -/

section Trivial

variable (p : ℕ) [Fact p.Prime]

/-- `M ⊗_{ℚ_p} ℚ_p^1 ≅ M`, `m ⊗ v ↦ v₀ m`. -/
def ev1 (M : Type*) [AddCommGroup M] [Module ℚ_[p] M] : (M ⊗[ℚ_[p]] (Fin 1 → ℚ_[p])) ≃ₗ[ℚ_[p]] M :=
  (TensorProduct.congr (LinearEquiv.refl ℚ_[p] M)
    (LinearEquiv.funUnique (Fin 1) ℚ_[p] ℚ_[p])).trans (TensorProduct.rid ℚ_[p] M)

theorem ev1_tmul (M : Type*) [AddCommGroup M] [Module ℚ_[p] M] (m : M) (v : Fin 1 → ℚ_[p]) :
    ev1 p M (m ⊗ₜ v) = v 0 • m := rfl

theorem ev1_inclT (B : Subalgebra ℚ_[p] (BdR p)) (x : B ⊗[ℚ_[p]] (Fin 1 → ℚ_[p])) :
    ((ev1 p B x : B) : BdR p) = ev1 p (BdR p) (inclT p B x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b v =>
    rw [ev1_tmul, inclT, TensorProduct.map_tmul, ev1_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, Subalgebra.coe_add, hx, hy]

theorem ev1_act (σ : GQp p) (y : BdR p ⊗[ℚ_[p]] (Fin 1 → ℚ_[p])) :
    ev1 p (BdR p) (TensorProduct.map (PanBergerSplit.bdrLin p σ)
      (PanBergerSplit.vAct p (1 : GQp p →* GL (Fin 1) ℚ_[p]) σ) y) =
      bdrAct p σ (ev1 p (BdR p) y) := by
  induction y using TensorProduct.inductionOn with
  | tmul b v =>
    rw [TensorProduct.map_tmul, ev1_tmul, ev1_tmul, PanBergerSplit.vAct_apply]
    simp only [MonoidHom.one_apply, Units.val_one, Matrix.one_mulVec]
    rw [bdrAct_smul]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

theorem ev1_smul (B : Subalgebra ℚ_[p] (BdR p)) (c : B) (x : B ⊗[ℚ_[p]] (Fin 1 → ℚ_[p])) :
    ev1 p B (c • x) = c * ev1 p B x := by
  induction x using TensorProduct.inductionOn with
  | tmul b v =>
    rw [TensorProduct.smul_tmul', ev1_tmul, ev1_tmul, smul_eq_mul, mul_smul_comm]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, mul_add]

/-- `D_B,H(ℚ_p) → B^H`, `x ↦ ev₁ x`. -/
def dBTrivialMap (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) :
    dB p B H (1 : GQp p →* GL (Fin 1) ℚ_[p]) →ₗ[fixedSub p B H] fixedSub p B H where
  toFun x := ⟨ev1 p B (x : B ⊗[ℚ_[p]] (Fin 1 → ℚ_[p])), fun σ hσ => by
    rw [ev1_inclT, ← ev1_act]
    exact congrArg (ev1 p (BdR p)) (x.2 σ hσ)⟩
  map_add' x y := Subtype.ext (by
    change ev1 p B ((x : B ⊗[ℚ_[p]] (Fin 1 → ℚ_[p])) + y) = ev1 p B x + ev1 p B y
    rw [map_add])
  map_smul' c x := Subtype.ext (by
    change ev1 p B ((c : B) • (x : B ⊗[ℚ_[p]] (Fin 1 → ℚ_[p]))) = (c : B) * ev1 p B x
    rw [ev1_smul])

theorem dBTrivialMap_bijective (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) :
    Function.Bijective (dBTrivialMap p B H) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply (ev1 p B).injective
    exact congrArg (fun z : fixedSub p B H => (z : B)) h
  · intro f
    refine ⟨⟨(ev1 p B).symm f, fun σ hσ => ?_⟩, ?_⟩
    · apply (ev1 p (BdR p)).injective
      rw [ev1_act, ← ev1_inclT, LinearEquiv.apply_symm_apply]
      exact f.2 σ hσ
    · apply Subtype.ext
      change ev1 p B ((ev1 p B).symm f) = f
      rw [LinearEquiv.apply_symm_apply]

/-- **Normalization check (unconditional).** The trivial one-dimensional representation is
`B`-admissible for every `ℚ_p`-subalgebra `B ⊆ B_dR` and every `H`; in particular it is
semistable over every `K` and potentially semistable for Berger's `B_st`. -/
theorem isAdmissible_trivial (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) :
    IsAdmissible p B H (1 : GQp p →* GL (Fin 1) ℚ_[p]) := by
  have : Nontrivial (BdR p) := ZInQ.Contrib.G9.BdrKer.Cp.nontrivial_BDeRham p
  rw [IsAdmissible, LinearEquiv.finrank_eq
    (LinearEquiv.ofBijective _ (dBTrivialMap_bijective p B H)), finrank_self,
    finrank_fin_fun]

theorem isPstB_trivial : IsPstB p (1 : GQp p →* GL (Fin 1) ℚ_[p]) :=
  ⟨⊥, inferInstance, isAdmissible_trivial p _ _⟩

end Trivial

/-! ## §6. The action of `G_{ℚ_p}`: `A_max`, `B_max^+` and `B_max` are stable -/

section Action

theorem adicMap_psEval {A B : Type*} [CommRing A] [CommRing B] (J : Ideal A) (J' : Ideal B)
    (g : A →+* B) (hg : J ≤ J'.comap g) {x : A} (hx : x ∈ J) (f : A⟦X⟧) :
    DR.adicMap J J' g hg (psEval J hx f) =
      psEval J' (show g x ∈ J' from hg hx) (PowerSeries.map g f) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [DR.adicMap_evalₐ, evalₐ_psEval]
  unfold DR.adicMapAux
  rw [RingHom.comp_apply]
  erw [evalₐ_psEval]
  rw [Ideal.quotientMap_mk, PowerSeries.trunc_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]

variable (p : ℕ) [Fact p.Prime]

open PanBergerSplit (Ainf AinfP locAct flatAct)

theorem evalB_congr {x y : AinfP p} (hx : x ∈ Ith p) (hxy : x = y) (f : (AinfP p)⟦X⟧) :
    evalB p hx f = evalB p (hxy ▸ hx) f := by
  subst hxy
  rfl

theorem locAct_mem (σ : GQp p) {x : AinfP p} (hx : x ∈ Ith p) : locAct p σ x ∈ Ith p :=
  DR.ker_le_comap_locMap p (oAct p σ) hx

theorem bdrAct_toBdR (σ : GQp p) (y : BDeRhamPlus 𝓞_ℂ_[p] p) :
    bdrAct p σ (toBdR p y) = toBdR p (DR.bdrPlusMap p (oAct p σ) y) := by
  rw [bdrAct, DR.bdrMap, IsLocalization.map_eq]

/-- **`σ(Σ a_k x^k) = Σ σ(a_k) σ(x)^k`** in `B_dR`. -/
theorem bdrAct_evalB (σ : GQp p) {x : AinfP p} (hx : x ∈ Ith p) (f : (AinfP p)⟦X⟧) :
    bdrAct p σ (toBdR p (evalB p hx f)) =
      toBdR p (evalB p (locAct_mem p σ hx) (PowerSeries.map (locAct p σ) f)) := by
  rw [bdrAct_toBdR]
  exact congrArg (toBdR p) (adicMap_psEval _ _ _ _ hx f)

/-- `σ` as a `ℚ_p`-algebra map of `B_dR`. -/
def bdrAlg (σ : GQp p) : BdR p →ₐ[ℚ_[p]] BdR p :=
  { bdrAct p σ with commutes' := bdrAct_qpToBdR p σ }

theorem bdrAlg_apply (σ : GQp p) (x : BdR p) : bdrAlg p σ x = bdrAct p σ x := rfl

theorem wittMap_xi_mem (σ : GQp p) :
    ∃ c : Ainf p, WittVector.map (flatAct p σ) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) =
      ZInQ.Contrib.G9.BdrKer.Cp.xi p * c := by
  have hk : WittVector.map (flatAct p σ) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ∈
      RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := by
    rw [RingHom.mem_ker, PanBergerSplit.theta_wittMap]
    have : ZInQ.Contrib.G9.BdrKer.Cp.xi p ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := by
      rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
      exact Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker.mp this, map_zero]
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, hc⟩ := hk
  exact ⟨c, by rw [← hc, mul_comm]⟩

theorem restricted_map (g : Ainf p →+* Ainf p) {f : (Ainf p)⟦X⟧} (hf : f ∈ restricted p) :
    PowerSeries.map g f ∈ restricted p := fun k => by
  obtain ⟨N, hN⟩ := hf k
  refine ⟨N, fun n hn => ?_⟩
  change (p : Ainf p) ^ k ∣ PowerSeries.coeff n (PowerSeries.map g f)
  rw [PowerSeries.coeff_map]
  have := map_dvd g (hN n hn)
  rwa [map_pow, map_natCast] at this

theorem restricted_rescale (c : Ainf p) {f : (Ainf p)⟦X⟧} (hf : f ∈ restricted p) :
    PowerSeries.rescale c f ∈ restricted p := fun k => by
  obtain ⟨N, hN⟩ := hf k
  refine ⟨N, fun n hn => ?_⟩
  change (p : Ainf p) ^ k ∣ PowerSeries.coeff n (PowerSeries.rescale c f)
  rw [PowerSeries.coeff_rescale]
  exact Dvd.dvd.mul_left (hN n hn) _

/-- **`A_max` is `G_{ℚ_p}`-stable**: `σ(Σ a_n (ω/p)^n) = Σ σ(a_n) c^n (ω/p)^n` where
`σ(ω) = ω c`, `c ∈ A_inf` (`σ(ω) ∈ ker θ = ω A_inf`). -/
theorem bdrAct_amax (σ : GQp p) {y : BDeRhamPlus 𝓞_ℂ_[p] p} (hy : y ∈ Amax p) :
    ∃ y' ∈ Amax p, bdrAct p σ (toBdR p y) = toBdR p y' := by
  obtain ⟨f, hf, rfl⟩ := hy
  obtain ⟨c, hc⟩ := wittMap_xi_mem p σ
  refine ⟨_, ⟨PowerSeries.rescale c (PowerSeries.map (WittVector.map (flatAct p σ)) f),
    restricted_rescale p c (restricted_map p _ hf), rfl⟩, ?_⟩
  rw [RingHom.comp_apply, bdrAct_evalB]
  congr 1
  rw [RingHom.comp_apply]
  apply psEval_eq_of_terms
  intro k
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_rescale,
    PowerSeries.coeff_map, PanBergerSplit.locAct_algebraMap, omegaP, map_mul,
    PanBergerSplit.locAct_qpToLoc, ZInQ.Contrib.G9.BdrKer.Cp.xi', PanBergerSplit.locAct_algebraMap,
    hc, map_mul, map_mul, map_pow]
  ring

theorem ringInverse_bdrAct (σ : GQp p) (x : BdR p) :
    bdrAct p σ (Ring.inverse x) = Ring.inverse (bdrAct p σ x) := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    rw [Ring.inverse_unit]
    have h : bdrAct p σ (u : BdR p) = ((Units.map (bdrAct p σ : BdR p →* BdR p) u : (BdR p)ˣ) :
        BdR p) := rfl
    rw [h, Ring.inverse_unit, ← map_inv]
    rfl
  · have h0 : x = 0 := by
      by_contra hne
      obtain ⟨y, hy⟩ : ∃ y : BdR p, x * y = 1 :=
        (ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p).mul_inv_cancel hne
      exact hx ⟨⟨x, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
    rw [h0, Ring.inverse_zero, map_zero, Ring.inverse_zero]

theorem map_locAct_logSeries (σ : GQp p) :
    PowerSeries.map (locAct p σ) (logSeries p) = logSeries p := by
  ext n
  rw [PowerSeries.coeff_map, logSeries, PowerSeries.coeff_mk]
  split_ifs
  · exact map_zero _
  · rw [map_mul, map_pow, map_neg, map_one, PanBergerSplit.locAct_qpToLoc]

/-- `σ(log [ε]) = log [σ(ε)]`. -/
theorem bdrAct_logTeich (σ : GQp p) {ε : PreTilt 𝓞_ℂ_[p] p} (h : PreTilt.untilt ε = 1) :
    bdrAct p σ (toBdR p (logTeich p h)) =
      toBdR p (logTeich p (show PreTilt.untilt (flatAct p σ ε) = 1 by
        rw [DR.untilt_preTiltMap, h, map_one])) := by
  rw [logTeich, logPlus, bdrAct_evalB, map_locAct_logSeries]
  congr 1
  apply evalB_congr
  rw [PanBergerSplit.locAct_algebraMap, map_sub, map_one, WittVector.map_teichmuller]

theorem tInvSet_stable (σ : GQp p) {z : BdR p} (hz : z ∈ tInvSet p) :
    bdrAct p σ z ∈ tInvSet p := by
  obtain ⟨ε, h, hne, rfl⟩ := hz
  refine ⟨flatAct p σ ε, by rw [DR.untilt_preTiltMap, h, map_one], fun h1 => hne (PanBergerSplit.flatAct_injective p σ
    (by rw [h1, map_one])), ?_⟩
  rw [ringInverse_bdrAct, bdrAct_logTeich]

/-- **`B_max^+` is `G_{ℚ_p}`-stable.** -/
theorem bmaxPlus_stable (σ : GQp p) : BmaxPlus p ≤ (BmaxPlus p).comap (bdrAlg p σ) := by
  rw [BmaxPlus, Algebra.adjoin_le_iff]
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  rw [SetLike.mem_coe, Subalgebra.mem_comap, bdrAlg_apply]
  obtain ⟨y', hy', he⟩ := bdrAct_amax p σ hy
  rw [he]
  exact Algebra.subset_adjoin ⟨y', hy', rfl⟩

/-- **`B_max` is `G_{ℚ_p}`-stable.** -/
theorem bmax_stable (σ : GQp p) : Bmax p ≤ (Bmax p).comap (bdrAlg p σ) := by
  rw [Bmax, Algebra.adjoin_le_iff]
  intro z hz
  rw [SetLike.mem_coe, Subalgebra.mem_comap, bdrAlg_apply]
  rcases hz with ⟨y, hy, rfl⟩ | hz
  · obtain ⟨y', hy', he⟩ := bdrAct_amax p σ hy
    rw [he]
    exact Algebra.subset_adjoin (Or.inl ⟨y', hy', rfl⟩)
  · exact Algebra.subset_adjoin (Or.inr (tInvSet_stable p σ hz))

end Action

end BergerBst
end PkgI4
end HDec
