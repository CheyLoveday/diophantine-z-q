import ZInQKernel.Contrib.OneProof.BergerReroute.BergerReroute

/-! The image of the distinguished maximal generator under Witt Frobenius belongs
to the crystalline series ring. This checks the estimate before completion. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4
open BergerBst FontaineSt
open PanBergerSplit (Ainf AinfP)
open PowerSeries

set_option maxHeartbeats 800000

variable (p : ℕ) [hp : Fact p.Prime]

private abbrev xi := ZInQ.Contrib.G9.BdrKer.Cp.xi p
private abbrev wLoc := algebraMap (Ainf p) (AinfP p)
private abbrev locPlus : AinfP p →+* BDeRhamPlus 𝓞_ℂ_[p] p := algebraMap (AinfP p) (AdicCompletion (Ith p) (AinfP p))
private abbrev xiLoc := wLoc p (xi p)

private theorem const_mem_acris (a : Ainf p) :
    locPlus p (wLoc p a) ∈ AcrisOf p (xi p) (theta_xi' p) := by
  refine ⟨PowerSeries.C a, C_mem_restricted p a, ?_⟩
  rw [dpSeries_C]
  exact (psEval_C (Ith p) (algebraMap_mem_ith p (theta_xi' p)) _).symm

private theorem psEval_polynomial {A : Type*} [CommRing A] (I : Ideal A) {x : A} (hx : x ∈ I)
    (Q : Polynomial A) : psEval I hx (Q : A⟦X⟧) = algebraMap A (AdicCompletion I A) (Q.eval x) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_psEval, mk_eval_trunc I hx]
  rfl

private theorem pthDivision_mem_acris :
    locPlus p (xiLoc p ^ p * qpToLoc p ((p : ℚ_[p])⁻¹)) ∈ AcrisOf p (xi p) (theta_xi' p) := by
  let f : (Ainf p)⟦X⟧ := PowerSeries.monomial p ((p - 1).factorial : Ainf p)
  let Q : Polynomial (AinfP p) := Polynomial.monomial p (qpToLoc p ((p : ℚ_[p])⁻¹))
  have hf : f ∈ restricted p := fun k => ⟨p + 1, fun n hn => by
    change (p : Ainf p) ^ k ∣ PowerSeries.coeff n f
    rw [PowerSeries.coeff_monomial, ite_eq_right (by omega)]
    exact dvd_zero _⟩
  refine ⟨f, hf, ?_⟩
  have hX : xiLoc p ∈ Ith p := algebraMap_mem_ith p (theta_xi' p)
  have hcoeff :
      (wLoc p ((p - 1).factorial : Ainf p)) * qpToLoc p ((p.factorial : ℚ_[p])⁻¹) =
        qpToLoc p ((p : ℚ_[p])⁻¹) := by
    have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
    have hfac : ((p - 1).factorial : ℚ_[p]) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h : (p.factorial : ℚ_[p]) = (p : ℚ_[p]) * ((p - 1).factorial : ℚ_[p]) := by
      exact_mod_cast (show p.factorial = p * (p - 1).factorial from by
        conv_lhs => rw [← Nat.sub_add_cancel hp.out.one_le, Nat.factorial_succ]
        rw [Nat.sub_add_cancel hp.out.one_le])
    have heq : wLoc p ((p - 1).factorial : Ainf p) = qpToLoc p ((p - 1).factorial : ℚ_[p]) := by
      simp only [map_natCast]
    rw [heq, ← map_mul, h]
    congr 1
    field_simp
  have hdp : dpSeries p f = (Q : (AinfP p)⟦X⟧) := by
    ext n
    by_cases hn : n = p
    · subst n
      simpa [dpSeries, f, Q, PowerSeries.coeff_coe, Polynomial.coeff_monomial] using hcoeff
    · simp [dpSeries, f, Q, PowerSeries.coeff_monomial, hn]
  change _ = psEval (Ith p) hX (dpSeries p f)
  rw [hdp, psEval_polynomial]
  change _ = algebraMap (AinfP p) (AdicCompletion (Ith p) (AinfP p))
    ((Polynomial.monomial p (qpToLoc p ((p : ℚ_[p])⁻¹))).eval (xiLoc p))
  rw [Polynomial.eval_monomial, mul_comm]
  rfl

/-- In the Witt ring, the difference between the Frobenius of `ξ` and
`-(-ξ)^p` is divisible by `p`. -/
theorem frobenius_xi_add_neg_pow_dvd :
    (p : Ainf p) ∣ WittVector.frobenius (xi p) + (-xi p) ^ p := by
  have hf : WittVector.frobenius (xi p) =
      (p : Ainf p) - (WittVector.teichmuller p (ZInQ.Contrib.G9.BdrKer.Cp.pFlat p)) ^ p := by
    simp only [ZInQ.Contrib.G9.BdrKer.Cp.xi, map_sub, map_natCast]
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  let z := WittVector.teichmuller p (ZInQ.Contrib.G9.BdrKer.Cp.pFlat p)
  have hz : z - (-xi p) = p := by
    simp only [ZInQ.Contrib.G9.BdrKer.Cp.xi, z]
    ring
  have h := sub_dvd_pow_sub_pow z (-xi p) p
  rw [hz] at h
  rw [hf]
  convert dvd_sub (dvd_refl (p : Ainf p)) h using 1
  ring

/-- The image of `φ(ξ)/p` in the de Rham ring lies in the integral crystalline
series image: `φ(ξ)/p = a - (-ξ)^p/p` with `a ∈ A_inf`, and
`ξ^p/p = (p-1)! · ξ^p/p!`. -/
theorem frobenius_xi_div_p_mem_acris :
    locPlus p (wLoc p (WittVector.frobenius (xi p)) * qpToLoc p ((p : ℚ_[p])⁻¹)) ∈
      AcrisOf p (xi p) (theta_xi' p) := by
  obtain ⟨a, ha⟩ := frobenius_xi_add_neg_pow_dvd p
  have he : WittVector.frobenius (xi p) = p * a - (-xi p) ^ p := eq_sub_of_add_eq ha
  have h2 : locPlus p (wLoc p (-((-1 : Ainf p) ^ p))) ∈ AcrisOf p (xi p) (theta_xi' p) :=
    const_mem_acris p _
  have hs := acrisOf_add p (theta_xi' p) (const_mem_acris p a)
    (acrisOf_mul p (theta_xi' p) h2 (pthDivision_mem_acris p))
  convert hs using 1
  rw [← (locPlus p).map_mul, ← (locPlus p).map_add]
  congr 1
  have hpinv : (p : AinfP p) * qpToLoc p ((p : ℚ_[p])⁻¹) = 1 :=
    natCast_mul_qp p p hp.out.ne_zero
  rw [he, map_sub, map_mul, map_natCast, sub_mul, mul_right_comm (p : AinfP p), hpinv, one_mul]
  simp only [map_neg, map_pow, map_one]
  rw [← neg_one_mul (xiLoc p), mul_pow]
  ring

/-- Applying Witt Frobenius to the coefficients of a finite polynomial in
`ξ/p` and substituting `φ(ξ)/p` gives a crystalline period. This is a range
statement on polynomials before descent through their evaluations. -/
theorem eval₂_wittFrobenius_mem_acris (Q : Polynomial (Ainf p)) :
    Q.eval₂ ((locPlus p).comp ((wLoc p).comp WittVector.frobenius))
      (locPlus p (wLoc p (WittVector.frobenius (xi p)) * qpToLoc p ((p : ℚ_[p])⁻¹))) ∈
        AcrisOf p (xi p) (theta_xi' p) := by
  let x := locPlus p (wLoc p (WittVector.frobenius (xi p)) * qpToLoc p ((p : ℚ_[p])⁻¹))
  have hx (n : ℕ) : x ^ n ∈ AcrisOf p (xi p) (theta_xi' p) := by
    induction n with
    | zero =>
      simpa only [pow_zero, map_one] using const_mem_acris p 1
    | succ n ih =>
      rw [pow_succ]
      exact acrisOf_mul p (theta_xi' p) ih (frobenius_xi_div_p_mem_acris p)
  induction Q using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [Polynomial.eval₂_add]
    exact acrisOf_add p (theta_xi' p) hf hg
  | monomial n a =>
    rw [Polynomial.eval₂_monomial]
    exact acrisOf_mul p (theta_xi' p) (const_mem_acris p (WittVector.frobenius a)) (hx n)

end ZInQ.Manuscript.BergerComparison
