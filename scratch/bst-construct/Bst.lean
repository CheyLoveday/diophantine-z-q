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

end BergerBst
end PkgI4
end HDec
