import ZInQKernel.Contrib.OneProof.BergerComparison.IntegralEquivariance
import ZInQKernel.Contrib.OneProof.BergerComparison.LogOverlap

/-! Frobenius scales the cyclotomic period and the logarithms appearing
in the Galois action on the semistable coordinate. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst BmaxOne FontaineSt PowerSeries
open PanBergerSplit (Ainf AinfP)
open ZInQ.Contrib.G9.BdrKer.Cp
open scoped BigOperators

variable (p : ℕ) [hp : Fact p.Prime]

set_option maxHeartbeats 500000

private abbrev loc := algebraMap (Ainf p) (AinfP p)
private abbrev wPlus := (ofLoc p).comp (loc p)
private abbrev phiOmega := loc p (WittVector.frobenius (xi p)) * qpToLoc p ((p : ℚ_[p])⁻¹)

private theorem wittFrobenius_zp (z : ℤ_[p]) :
    WittVector.frobenius (zpToW p z) = zpToW p z := by
  apply (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : Ainf p)})).mpr
  intro k
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hz := map_dvd (zpToW p) (Ideal.mem_span_singleton.mp (PadicInt.appr_spec k z))
  rw [map_pow, map_natCast, map_sub, map_natCast] at hz
  have hh := map_dvd (WittVector.frobenius (p := p)) hz
  rw [map_pow, map_natCast, map_sub, map_natCast] at hh
  convert dvd_sub hh hz using 1
  ring

/-- Integral Frobenius fixes the embedded p-adic integers. -/
theorem integralFrobenius_zp (z : ℤ_[p]) :
    (integralFrobenius p ⟨zpB p z, zpB_mem p z⟩ : BDeRhamPlus 𝓞_ℂ_[p] p) = zpB p z := by
  have h : maxToImage p ⟨Polynomial.C (zpToW p z), polynomial_mem_restricted p _⟩ =
      ⟨zpB p z, zpB_mem p z⟩ := by
    apply Subtype.ext
    change maximalEval p (Polynomial.C (zpToW p z)) = _
    rw [maximalEval_polynomial, Polynomial.eval₂_C]
    rfl
  rw [← h, integralFrobenius_polynomial, Polynomial.eval₂_C, RingHom.comp_apply,
    RingHom.comp_apply, wittFrobenius_zp]
  rfl

private theorem wittFrobenius_logCoeff (n : ℕ) :
    WittVector.frobenius (pLogTerm p 1 n) = pLogTerm p 1 n := by
  by_cases hn : n = 0
  · simp [hn, pLogTerm]
  simp only [pLogTerm, ite_eq_right hn, one_pow, mul_one, map_mul, map_pow, map_neg, map_one,
    wittFrobenius_zp]

private theorem dvd_term (b : Ainf p) {k n : ℕ} (hn : 2*k ≤ n) :
    (p : Ainf p)^k ∣ pLogTerm p b n := by
  by_cases h0 : n = 0
  · simp [h0, pLogTerm]
  obtain ⟨d, hd⟩ := (logCoeff_spec p h0).2 k hn
  rw [pLogTerm, ite_eq_right h0, hd, map_mul, map_pow, map_natCast]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_mul_right _ _) _) _

private def logRestricted (b : Ainf p) : restricted p :=
  ⟨PowerSeries.mk (pLogTerm p b), fun k =>
    ⟨2*k, fun n hn => by
      change (p : Ainf p)^k ∣ coeff n (PowerSeries.mk (pLogTerm p b))
      rw [PowerSeries.coeff_mk]
      exact dvd_term p b hn⟩⟩

private theorem logRestricted_eval {ε : PreTilt 𝓞_ℂ_[p] p} (hε : ε.untilt = 1)
    {b : Ainf p} (hb : WittVector.teichmuller p ε - 1 = xi p*b) :
    (maxToImage p (logRestricted p b) : BDeRhamPlus 𝓞_ℂ_[p] p) = logTeich p hε := by
  change maximalEval p (logRestricted p b).val = logTeich p hε
  change psEval (Ith p) (omegaP_mem p) (PowerSeries.map (loc p) (PowerSeries.mk (pLogTerm p b))) =
    psEval (Ith p) (teich_sub_one_mem p hε) (logSeries p)
  symm
  refine psEval_eq_of_terms (Ith p) (teich_sub_one_mem p hε) (omegaP_mem p) _ _ fun n => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  change coeff n (logSeries p) * loc p (WittVector.teichmuller p ε - 1)^n =
    loc p (pLogTerm p b n) * (omegaP p)^n
  rw [hb, pLogTerm_eq_mul_pow, map_mul (loc p) (pLogTerm p 1 n), map_pow, wittLogTerm_one]
  have hω : (p : AinfP p) * omegaP p = loc p (xi p) := by
    rw [omegaP, xi', mul_left_comm, ← map_natCast (qpToLoc p), ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero), map_one, mul_one]
  simp only [map_mul, mul_pow]
  rw [← hω, mul_pow]
  ring

private def logPolynomial (b : Ainf p) (k : ℕ) : Polynomial (Ainf p) :=
  ∑ n ∈ Finset.range (2*k), Polynomial.C (pLogTerm p b n) * Polynomial.X^n

private theorem logPolynomial_approx (b : Ainf p) (k : ℕ) :
    (p : restricted p)^k ∣ logRestricted p b -
      ⟨logPolynomial p b k, polynomial_mem_restricted p _⟩ := by
  apply (pDvd_iff_coeff p _ k).mpr
  intro n
  change (p : Ainf p)^k ∣ coeff n ((logRestricted p b).val - (logPolynomial p b k : (Ainf p)⟦X⟧))
  rw [map_sub, logRestricted, PowerSeries.coeff_mk, Polynomial.coeff_coe, logPolynomial,
    Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : n ∈ Finset.range (2*k)
  · rw [Finset.sum_eq_single_of_mem n h (fun j _ hjn => by simp [Ne.symm hjn]),
      ite_eq_left rfl, mul_one, sub_self]
    exact dvd_zero _
  · rw [Finset.sum_eq_zero (fun j hj => by
      have hjn : n ≠ j := fun e => h (e ▸ hj)
      simp [hjn]), sub_zero]
    exact dvd_term p b (by simpa only [Finset.mem_range, not_lt] using h)

private theorem eval_logPolynomial (b : Ainf p) (k : ℕ) :
    (maxToImage p ⟨logPolynomial p b k, polynomial_mem_restricted p _⟩ :
      BDeRhamPlus 𝓞_ℂ_[p] p) =
      ∑ n ∈ Finset.range (2*k), ofLoc p (loc p (pLogTerm p b n) * (omegaP p)^n) := by
  change maximalEval p (logPolynomial p b k) = _
  rw [maximalEval_polynomial, logPolynomial, Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    RingHom.comp_apply]
  rw [map_mul, map_pow]

private theorem eval_frob_logPolynomial (b : Ainf p) (k : ℕ) :
    (integralFrobenius p (maxToImage p ⟨logPolynomial p b k, polynomial_mem_restricted p _⟩) :
      BDeRhamPlus 𝓞_ℂ_[p] p) =
      ∑ n ∈ Finset.range (2*k), ofLoc p (loc p (WittVector.frobenius (pLogTerm p b n)) *
        (phiOmega p)^n) := by
  rw [integralFrobenius_polynomial, logPolynomial, Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    RingHom.comp_apply]
  rw [map_mul, map_pow]

private theorem phi_teich_sub_one {ε : PreTilt 𝓞_ℂ_[p] p} :
    WittVector.frobenius (WittVector.teichmuller p ε - 1) = WittVector.teichmuller p (ε^p) - 1 := by
  rw [map_sub, map_one, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
    frobenius_def]

private theorem finiteLogs (k : ℕ) {b c : Ainf p}
    (he : WittVector.frobenius (xi p*b) = xi p*c) :
    (integralFrobenius p (maxToImage p ⟨logPolynomial p b k, polynomial_mem_restricted p _⟩) :
      BDeRhamPlus 𝓞_ℂ_[p] p) =
      (maxToImage p ⟨logPolynomial p c k, polynomial_mem_restricted p _⟩ :
        BDeRhamPlus 𝓞_ℂ_[p] p) := by
  rw [eval_logPolynomial, eval_frob_logPolynomial]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  rw [pLogTerm_eq_mul_pow p b n, map_mul, wittFrobenius_logCoeff, map_pow,
    pLogTerm_eq_mul_pow p c n]
  simp only [map_mul, map_pow]
  rw [mul_assoc, mul_assoc, ← mul_pow, ← mul_pow]
  congr 2
  dsimp only [phiOmega]
  rw [omegaP, xi']
  have hh := congrArg (loc p) he
  simp only [map_mul] at hh
  change loc p (WittVector.frobenius b) *
    (loc p (WittVector.frobenius (xi p)) * qpToLoc p ((p : ℚ_[p])⁻¹)) =
    loc p c * (loc p (xi p) * qpToLoc p ((p : ℚ_[p])⁻¹))
  linear_combination (qpToLoc p ((p : ℚ_[p])⁻¹)) * hh

private def crisIntoMax : crystallineIntegral p →+* Amax p :=
  (crystallineIntegral p).subtype.codRestrict (Amax p) (fun y =>
    acrisOf_le_amax p (theta_xi' p) (ker_fontaineTheta_Cp p)
      ((mem_crystallineIntegral p y.val).mp y.property))

/-- Frobenius sends the logarithm of a Teichmüller lift with untilt one
to p times that logarithm. This includes both t and the Galois shifts. -/
theorem integralFrobenius_logTeich {ε : PreTilt 𝓞_ℂ_[p] p} (hε : ε.untilt = 1) :
    (integralFrobenius p ⟨logTeich p hε, logTeich_mem_amax p hε⟩ :
      BDeRhamPlus 𝓞_ℂ_[p] p) = p * logTeich p hε := by
  have hpow : (ε^p).untilt = 1 := by rw [map_pow, hε, one_pow]
  rw [← logTeich_pow p hε p hpow]
  have hb : WittVector.teichmuller p ε - 1 ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) :=
    PanBergerSplit.theta_teich_sub_one p hε
  have hc : WittVector.teichmuller p (ε^p) - 1 ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) :=
    PanBergerSplit.theta_teich_sub_one p hpow
  rw [ker_fontaineTheta_Cp, Ideal.mem_span_singleton] at hb hc
  obtain ⟨b, hb⟩ := hb
  obtain ⟨c, hc⟩ := hc
  have he : WittVector.frobenius (xi p*b) = xi p*c := by
    rw [← hb, ← hc, phi_teich_sub_one]
  have hL := logRestricted_eval p hε hb
  have hLp := logRestricted_eval p hpow hc
  have hEq : crisIntoMax p (integralFrobenius p (maxToImage p (logRestricted p b))) =
      maxToImage p (logRestricted p c) := by
    apply sub_eq_zero.mp
    apply amax_eq_zero_of_pDvd
    intro k
    let F := (crisIntoMax p).comp ((integralFrobenius p).comp (maxToImage p))
    have h₁ := map_dvd F (logPolynomial_approx p b k)
    have h₂ := map_dvd (maxToImage p) (logPolynomial_approx p c k)
    rw [map_sub, map_pow, map_natCast] at h₁ h₂
    have h : F ⟨logPolynomial p b k, polynomial_mem_restricted p _⟩ =
        maxToImage p ⟨logPolynomial p c k, polynomial_mem_restricted p _⟩ :=
      Subtype.ext (finiteLogs p k he)
    rw [h] at h₁
    convert dvd_sub h₁ h₂ using 1
    dsimp only [F, RingHom.comp_apply]
    ring
  rw [← hLp]
  rw [← (show maxToImage p (logRestricted p b) = ⟨_, logTeich_mem_amax p hε⟩ from Subtype.ext hL)]
  exact congrArg Subtype.val hEq

end ZInQ.Manuscript.BergerComparison
