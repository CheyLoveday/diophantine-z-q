import ZInQKernel.Contrib.OneProof.BergerComparison.MaximalEvaluation
import ZInQKernel.Contrib.OneProof.BergerComparison.ResidueLog

/-! The two logarithm series agree on their overlap in the Witt ring.
The bridge between the completions is the p-adic closedness of (ξ^n). -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst FontaineSt PowerSeries Ideal
open PanBergerSplit (Ainf AinfP)
open ZInQ.Contrib.G9.BdrKer.Cp
open scoped BigOperators

variable (p : ℕ) [hp : Fact p.Prime]

private abbrev P := Ideal.span {(p : Ainf p)}

private abbrev loc := algebraMap (Ainf p) (AinfP p)
private abbrev intoPlus := algebraMap (AinfP p) (AdicCompletion (Ith p) (AinfP p))

private theorem modP_iff (k : ℕ) (a b : Ainf p) :
    (a ≡ b [SMOD (P p ^ k • ⊤ : Submodule (Ainf p) (Ainf p))]) ↔
      (p : Ainf p)^k ∣ a - b := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

private theorem pDvd_cancel_xiPow (m k : ℕ) (a : Ainf p)
    (h : (p : Ainf p)^k ∣ xi p ^ m * a) : (p : Ainf p)^k ∣ a := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    rw [pow_succ', mul_assoc] at h
    exact ih (pow_p_dvd_of_dvd_xi_mul p k _ h)

/-- If a Witt vector is a multiple of ξ^m modulo every power of p,
it is a multiple of ξ^m in the Witt ring itself. -/
theorem xiPow_dvd_of_mod_every_pPow (m : ℕ) (a : Ainf p)
    (h : ∀ k, ∃ b, (p : Ainf p)^k ∣ a - xi p ^ m * b) :
    xi p ^ m ∣ a := by
  choose f hf using h
  have hc {k l : ℕ} (hkl : k ≤ l) : (p : Ainf p)^k ∣ f k - f l := by
    have h' := dvd_sub ((pow_dvd_pow _ hkl).trans (hf l)) (hf k)
    apply pDvd_cancel_xiPow p m
    rw [show xi p ^ m * (f k - f l) = (a - xi p ^ m * f l) - (a - xi p ^ m * f k) by ring]
    exact h'
  obtain ⟨b, hb⟩ := IsPrecomplete.prec (I := P p) inferInstance (f := f)
    (fun hkl => (modP_iff p _ _ _).mpr (hc hkl))
  refine ⟨b, (IsHausdorff.eq_iff_smodEq (I := P p)).mpr fun k => ?_⟩
  apply (modP_iff p _ _ _).mpr
  have hh := (modP_iff p _ _ _).mp (hb k)
  convert dvd_add (hf k) (Dvd.dvd.mul_left hh (xi p ^ m)) using 1
  ring

private theorem pLogTerm_xi (a : Ainf p) (n : ℕ) :
    pLogTerm p (xi p * a) n = xi p ^ n * pLogTerm p a n := by
  by_cases hn : n = 0
  · simp [pLogTerm, hn]
  · simp only [pLogTerm, hn, ite_false, mul_pow]
    ring

private theorem pLog_xi_mod (a : Ainf p) (m : ℕ) :
    xi p ^ m ∣ pLog p (xi p * a) - ∑ n ∈ Finset.range m, pLogTerm p (xi p * a) n := by
  apply xiPow_dvd_of_mod_every_pPow p
  intro k
  let K := max k m
  have hm : m ≤ 2 * K := by dsimp [K]; omega
  have hk : k ≤ K := le_max_left _ _
  let s := fun N => ∑ n ∈ Finset.range N, pLogTerm p (xi p * a) n
  have hs : s (2*K) = s m + ∑ i ∈ Finset.range (2*K - m), pLogTerm p (xi p * a) (m+i) := by
    dsimp only [s]
    conv_lhs => rw [← Nat.add_sub_of_le hm, Finset.sum_range_add]
  have hd : xi p ^ m ∣ s (2*K) - s m := by
    rw [hs, add_sub_cancel_left]
    exact Finset.dvd_sum fun i _ => by
      rw [pLogTerm_xi]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ (Nat.le_add_right m i)) _
  obtain ⟨d, hd⟩ := hd
  refine ⟨d, ?_⟩
  change (p : Ainf p)^k ∣ pLog p (xi p * a) - s m - xi p ^ m * d
  rw [← hd]
  convert (pow_dvd_pow _ hk).trans ((dvd_sub_comm).mp (pLog_spec p (xi p * a) K)) using 1
  ring

/-- After inverting p, a Witt logarithm coefficient is the formal
logarithm coefficient multiplied by the corresponding power of p. -/
theorem wittLogTerm_one (n : ℕ) :
    loc p (pLogTerm p 1 n) = coeff n (logSeries p) * (p : AinfP p)^n := by
  by_cases hn : n = 0
  · simp [hn, logSeries, pLogTerm]
  rw [logSeries, PowerSeries.coeff_mk, pLogTerm, ite_eq_right hn, ite_eq_right hn]
  have hcoeff :
      qpToLoc p ((n : ℚ_[p])⁻¹) * loc p (p : Ainf p) ^ n =
        loc p (zpToW p (logCoeff p n)) := by
    rw [← qpToLoc_algebraMap, map_natCast, ← map_natCast (qpToLoc p), ← map_pow, ← map_mul]
    congr 1
    have hnn : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn
    change (n : ℚ_[p])⁻¹ * (p : ℚ_[p]) ^ n = (logCoeff p n : ℚ_[p])
    rw [← (logCoeff_spec p hn).1, mul_left_comm, inv_mul_cancel₀ hnn, mul_one]
  simp only [map_mul, map_pow, map_neg, map_one, one_pow, mul_one]
  rw [← hcoeff, map_natCast (loc p)]
  ring

/-- Each Witt logarithm term is its universal coefficient times a power. -/
theorem pLogTerm_eq_mul_pow (a : Ainf p) (n : ℕ) :
    pLogTerm p a n = pLogTerm p 1 n * a^n := by
  by_cases hn : n = 0 <;> simp [pLogTerm, hn]

private theorem finite_term (a : Ainf p) (n : ℕ) :
    coeff n (logSeries p) * loc p ((p : Ainf p) * (xi p * a)) ^ n =
      loc p (pLogTerm p (xi p * a) n) := by
  rw [pLogTerm_eq_mul_pow, map_mul (loc p) (pLogTerm p 1 n), map_pow, wittLogTerm_one]
  simp only [map_mul, map_natCast, mul_pow]
  ring

/-- For a Witt unit in both domains, the p-adic Witt logarithm of
1 + pξa and the Fontaine-kernel logarithm give the same de Rham period. -/
theorem pLog_agrees_logPlus_on_overlap (a : Ainf p)
    (h : loc p ((p : Ainf p) * (xi p * a)) ∈ Ith p) :
    intoPlus p (loc p (pLog p (xi p * a))) = logPlus p h := by
  change intoPlus p (loc p (pLog p (xi p * a))) = psEval (Ith p) h (logSeries p)
  apply AdicCompletion.ext_evalₐ
  intro m
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of, evalₐ_psEval,
    Polynomial.eval, eval₂_trunc_eq_sum_range]
  simp only [RingHom.id_apply, finite_term, ← map_sum]
  rw [Ideal.Quotient.eq, Algebra.algebraMap_self_apply, ← map_sub, Ith,
    ker_fontaineThetaInvertP_Cp, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  simpa only [map_pow, xi'] using map_dvd (loc p) (pLog_xi_mod p a m)

end ZInQ.Manuscript.BergerComparison
