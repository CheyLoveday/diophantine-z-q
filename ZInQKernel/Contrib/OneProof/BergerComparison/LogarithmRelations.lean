import ZInQKernel.Contrib.OneProof.BergerComparison.LogDenominators

/-! A hypothetical linear relation for log[p̃] forces an integral
maximal coefficient to be divisible by every power of p. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst FontaineSt PowerSeries Ideal
open PanBergerSplit (Ainf AinfP)
open ZInQ.Contrib.G9.BdrKer.Cp

variable (p : ℕ) [hp : Fact p.Prime]

set_option maxHeartbeats 750000

private abbrev loc := algebraMap (Ainf p) (AinfP p)
private abbrev res := (WittVector.constantCoeff : Ainf p →+* PreTilt 𝓞_ℂ_[p] p)
private abbrev eval := psEval (Ith p) (omegaP_mem p)

private theorem eval_congr_trunc (N : ℕ) {f g : (AinfP p)⟦X⟧}
    (h : ∀ i < N, coeff i f = coeff i g) :
    AdicCompletion.evalₐ (Ith p) N (eval p f) = AdicCompletion.evalₐ (Ith p) N (eval p g) := by
  change AdicCompletion.evalₐ (Ith p) N (psEval (Ith p) (omegaP_mem p) f) =
    AdicCompletion.evalₐ (Ith p) N (psEval (Ith p) (omegaP_mem p) g)
  rw [evalₐ_psEval, evalₐ_psEval]
  suffices trunc N f = trunc N g by rw [this]
  ext i
  rw [coeff_trunc, coeff_trunc]
  split_ifs with hi
  · exact h i hi
  · rfl

private theorem both_scaled {f g : restricted p} (r k N : ℕ) (hr : r ≤ k) (hN : N < 2*p^k)
    (rel : (p : BDeRhamPlus 𝓞_ℂ_[p] p)^r * maximalEval p f.val * logPTilde p =
      maximalEval p g.val) :
    AdicCompletion.evalₐ (Ith p) (N+1)
      (maximalEval p (f.val * scaledNegativeLog p k N hN - C ((p : Ainf p)^(k-r)) * g.val)) = 0 := by
  let a := PowerSeries.map (loc p) f.val
  let b := PowerSeries.map (loc p) g.val
  let ℓ := negativeLogSeries p
  let m := PowerSeries.map (loc p) (scaledNegativeLog p k N hN)
  let d := C ((p : AinfP p)^(k-r))*b
  have he (j : ℕ) (hj : j < N + 1) :
      coeff j (a*m - d) = coeff j (a*(C ((p : AinfP p)^k)*ℓ) - d) := by
    simp only [map_sub]
    congr 1
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun ⟨u, v⟩ huv => ?_
    have huv' : u+v = j := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
    have hv : v ≤ N := by omega
    dsimp only [m, ℓ, Prod.fst, Prod.snd]
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
    rw [scaledNegativeLog_coeff p k N hN hv]
  have hE : eval p (a*(C ((p : AinfP p)^k)*ℓ) - d) = 0 := by
    change eval p _ = (0 : AdicCompletion (Ith p) (AinfP p))
    dsimp only [d, ℓ]
    rw [map_sub, map_mul, map_mul, map_mul, psEval_C, psEval_C, negativeLogSeries_eval]
    change maximalEval p f.val * (ofLoc p ((p : AinfP p)^k)*logPTilde p) -
      ofLoc p ((p : AinfP p)^(k-r)) * maximalEval p g.val =
      (0 : BDeRhamPlus 𝓞_ℂ_[p] p)
    simp only [map_pow, map_natCast]
    rw [← rel, show (p : BDeRhamPlus 𝓞_ℂ_[p] p)^k =
      (p : BDeRhamPlus 𝓞_ℂ_[p] p)^(k-r) * (p : BDeRhamPlus 𝓞_ℂ_[p] p)^r by
        rw [← pow_add, Nat.sub_add_cancel hr]]
    ring
  change AdicCompletion.evalₐ (Ith p) (N+1)
    (eval p (PowerSeries.map (loc p) (f.val * scaledNegativeLog p k N hN -
      C ((p : Ainf p)^(k-r)) * g.val))) = 0
  have hh : PowerSeries.map (loc p) (f.val * scaledNegativeLog p k N hN -
      C ((p : Ainf p)^(k-r)) * g.val) = a*m-d := by
    dsimp only [a, m, d]
    rw [map_sub (PowerSeries.map (loc p)), map_mul (PowerSeries.map (loc p)),
      map_mul (PowerSeries.map (loc p)), PowerSeries.map_C, map_pow, map_natCast]
  rw [hh]
  rw [eval_congr_trunc p (N+1) he, hE, map_zero]

private theorem p_mul_omega : (p : AinfP p) * omegaP p = loc p (xi p) := by
  rw [omegaP, mul_left_comm, natCast_mul_qp p p hp.out.ne_zero, mul_one]
  rfl

private theorem res_xi_ne_zero : res p (xi p) ≠ 0 := by
  have h : res p (xi p) = -(pFlat p) := by
    rw [xi, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub]
    simp
  rw [h, neg_ne_zero]
  intro hz
  have he := untilt_pFlat p
  rw [← WittVector.fontaineTheta_teichmuller, hz, WittVector.teichmuller_zero, map_zero] at he
  exact p_ne_zero p he.symm

private theorem top_multiple {w : (Ainf p)⟦X⟧} (N : ℕ)
    (h : AdicCompletion.evalₐ (Ith p) (N+1) (maximalEval p w) = 0) :
    ∃ d : Ainf p, res p (coeff N w) = res p (xi p * d) := by
  change AdicCompletion.evalₐ (Ith p) (N+1)
    (psEval (Ith p) (omegaP_mem p) (PowerSeries.map (loc p) w)) = 0 at h
  rw [evalₐ_psEval, Ideal.Quotient.eq_zero_iff_mem] at h
  let a : Ainf p := ∑ j ∈ Finset.range (N+1), coeff j w * (xi p)^j * (p : Ainf p)^(N-j)
  have ha : loc p a = (p : AinfP p)^N *
      (trunc (N+1) (PowerSeries.map (loc p) w)).eval (omegaP p) := by
    rw [Polynomial.eval, eval₂_trunc_eq_sum_range, Finset.mul_sum]
    dsimp only [a]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [RingHom.id_apply, PowerSeries.coeff_map]
    simp only [map_mul, map_pow, map_natCast, ← p_mul_omega, mul_pow]
    have hj' : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [show (p : AinfP p)^N = (p : AinfP p)^j * (p : AinfP p)^(N-j) by
      rw [← pow_add, Nat.add_sub_of_le hj']]
    ring
  have ham : loc p a ∈ Ith p ^ (N+1) := ha ▸ (Ith p^(N+1)).mul_mem_left _ h
  rw [Ith, ker_fontaineThetaInvertP_Cp, Ideal.span_singleton_pow] at ham
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (mem_xi_pow_of_algebraMap p (N+1) a ham)
  have htop : res p a = res p (coeff N w) * (res p (xi p))^N := by
    dsimp only [a]
    rw [map_sum]
    rw [Finset.sum_eq_single_of_mem N (Finset.mem_range.mpr (Nat.lt_succ_self N))]
    · simp only [Nat.sub_self, pow_zero, mul_one, map_mul, map_pow]
    · intro j hj hne
      have hjlt : j < N := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hne
      have hpj : N-j ≠ 0 := by omega
      simp only [map_mul, map_pow, map_natCast, CharP.cast_eq_zero (PreTilt 𝓞_ℂ_[p] p) p,
        zero_pow hpj, mul_zero]
  refine ⟨d, ?_⟩
  rw [hd, map_mul, map_pow, pow_succ] at htop
  rw [map_mul]
  apply mul_right_cancel₀ (pow_ne_zero _ (res_xi_ne_zero p))
  linear_combination -htop

private theorem coeff_split {f g : restricted p} (r : ℕ)
    (rel : (p : BDeRhamPlus 𝓞_ℂ_[p] p)^r * maximalEval p f.val * logPTilde p =
      maximalEval p g.val) (i : ℕ) :
    ∃ d : Ainf p, (p : Ainf p) ∣ coeff i f.val - xi p*d := by
  let k := r+i+1
  let N := p^k + i
  have hr : r < k := by omega
  have hip : i < p^k :=
    (show i ≤ k by omega).trans_lt (Nat.lt_pow_self hp.out.one_lt)
  have hN : N < 2*p^k := by omega
  let m := scaledNegativeLog p k N hN
  let w := f.val * m - C ((p : Ainf p)^(k-r))*g.val
  have h := both_scaled p r k N hr.le hN rel
  obtain ⟨d, hd⟩ := top_multiple p N (w := w) h
  have hm : PowerSeries.map (res p) m = -X^(p^k) :=
    scaledNegativeLog_mod_p p k N hN (Nat.le_add_right ..)
  have hw : res p (coeff N w) = -res p (coeff i f.val) := by
    rw [← PowerSeries.coeff_map]
    have hC : PowerSeries.map (res p) (C ((p : Ainf p)^(k-r))) = 0 := by
      rw [PowerSeries.map_C, map_pow, map_natCast, CharP.cast_eq_zero (PreTilt 𝓞_ℂ_[p] p) p,
        zero_pow (by omega), map_zero]
    dsimp only [w]
    rw [map_sub (PowerSeries.map (res p)), map_mul (PowerSeries.map (res p)),
      map_mul (PowerSeries.map (res p)), hC, hm, zero_mul, sub_zero, mul_neg, map_neg,
      mul_comm (PowerSeries.map (res p) f.val), coeff_X_pow_mul',
      ite_eq_left (show p^k ≤ N from Nat.le_add_right ..), show N-p^k = i by omega,
      PowerSeries.coeff_map]
  refine ⟨-d, ?_⟩
  rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub,
    sub_eq_zero, mul_neg, map_neg, ← hd, hw, neg_neg]

private theorem p_dvd_maximal {f g : restricted p} (r : ℕ)
    (rel : (p : BDeRhamPlus 𝓞_ℂ_[p] p)^r * maximalEval p f.val * logPTilde p =
      maximalEval p g.val) : (p : Amax p) ∣ maxToImage p f := by
  obtain ⟨M, hM⟩ := f.property 1
  have hex (i : ℕ) : ∃ d : Ainf p, (p : Ainf p) ∣ coeff i f.val - xi p*d ∧
       (M ≤ i → d = 0) := by
    by_cases hi : M ≤ i
    · exact ⟨0, by simpa using hM i hi, fun _ => rfl⟩
    · obtain ⟨d, h⟩ := coeff_split p r rel i
      exact ⟨d, h, fun contra => (hi contra).elim⟩
  choose d hd hdz using hex
  choose c hc using hd
  let D : (Ainf p)⟦X⟧ := PowerSeries.mk d
  let C' : (Ainf p)⟦X⟧ := PowerSeries.mk c
  have hD : D ∈ restricted p := fun k => ⟨M, fun i hi => by
    change (p : Ainf p)^k ∣ coeff i D
    rw [PowerSeries.coeff_mk, hdz i hi]
    exact dvd_zero _⟩
  have hC : C' ∈ restricted p := by
    intro k
    obtain ⟨N, hN⟩ := f.property (k+1)
    refine ⟨max M N, fun i hi => ?_⟩
    change (p : Ainf p)^k ∣ coeff i C'
    rw [PowerSeries.coeff_mk]
    have hh := hc i
    rw [hdz i (le_of_max_le_left hi), mul_zero, sub_zero] at hh
    have h := hN i (le_of_max_le_right hi)
    beta_reduce at h
    rw [pow_succ', hh] at h
    exact (mul_dvd_mul_iff_left (witt_p_ne_zero p)).mp h
  have hf : f = ⟨C (p : Ainf p), C_mem_restricted p _⟩ * ⟨C', hC⟩ +
    ⟨C (xi p), C_mem_restricted p _⟩ * ⟨D, hD⟩ := by
    apply Subtype.ext
    apply PowerSeries.ext
    intro i
    change coeff i f.val = coeff i (C (p : Ainf p)*C' + C (xi p)*D)
    rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    linear_combination hc i
  have hrel : maxToImage p (maximalRelSub p) = 0 := Subtype.ext (maximalEval_relation p)
  let X' : restricted p := ⟨X, by
    have h := polynomial_mem_restricted p (Polynomial.X : Polynomial (Ainf p))
    simpa only [Polynomial.coe_X] using h⟩
  have hξ : (⟨C (xi p), C_mem_restricted p _⟩ : restricted p) =
      maximalRelSub p + X' * ⟨C (p : Ainf p), C_mem_restricted p _⟩ := by
    apply Subtype.ext
    exact (sub_add_cancel _ _).symm
  have hp' : (⟨C (p : Ainf p), C_mem_restricted p _⟩ : restricted p) = p := by
    apply Subtype.ext
    exact map_natCast C p
  rw [hf, hξ, hp', map_add, map_mul, map_mul, map_add, hrel, zero_add, map_mul, map_natCast]
  exact dvd_add (dvd_mul_right _ _) (Dvd.dvd.mul_right (dvd_mul_left _ _) _)

/-- No nonzero integral maximal period multiplies log[p̃] into a
maximal period, even if a fixed power of p clears the denominator. -/
theorem eq_zero_of_integral_log_relation (a b : Amax p) (r : ℕ)
    (h : (p : BDeRhamPlus 𝓞_ℂ_[p] p)^r * a.val * logPTilde p = b.val) : a = 0 := by
  apply amax_eq_zero_of_pDvd p
  have lem (k : ℕ) :
      ∀ (a b : Amax p) (r : ℕ), (p : BDeRhamPlus 𝓞_ℂ_[p] p)^r * a.val * logPTilde p = b.val →
        (p : Amax p)^k ∣ a := by
    induction k with
    | zero => intro a b r h; simp
    | succ k ih =>
      intro a b r h
      have hd : (p : Amax p) ∣ a := by
        obtain ⟨f, rfl⟩ := maxToImage_surjective p a
        obtain ⟨g, rfl⟩ := maxToImage_surjective p b
        exact p_dvd_maximal p r h
      obtain ⟨c, rfl⟩ := hd
      rw [pow_succ']
      apply mul_dvd_mul_left
      apply ih c b (r+1)
      rw [pow_succ, mul_assoc ((p : BDeRhamPlus 𝓞_ℂ_[p] p)^r)]
      exact h
  exact fun k => lem k a b r h

end ZInQ.Manuscript.BergerComparison
