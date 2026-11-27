import ZInQKernel.Contrib.OneProof.BergerComparison.LogOverlap

/-! Additivity of the p-adic Witt logarithm. A finite formal logarithm
identity kills low-degree coefficients; the high-degree coefficients
are divisible by the required power of p before evaluating at one. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst PowerSeries Ideal
open PanBergerSplit (Ainf AinfP)
open ZInQ.Contrib.G9.BdrKer.Cp
open scoped BigOperators

variable (p : ℕ) [hp : Fact p.Prime]

set_option maxHeartbeats 400000

private abbrev loc := algebraMap (Ainf p) (AinfP p)

private def scaledLogPoly (N : ℕ) (Y : Polynomial (Ainf p)) : Polynomial (Ainf p) :=
  ∑ n ∈ Finset.range N, Polynomial.C (pLogTerm p 1 n) * Y^n

private theorem scaledLogPoly_map (N : ℕ) (Y : Polynomial (Ainf p)) :
    (scaledLogPoly p N Y).map (loc p) =
      (logPoly p N).comp (Polynomial.C (p : AinfP p) * Y.map (loc p)) := by
  rw [scaledLogPoly, show Polynomial.map (loc p) _ = Polynomial.mapRingHom (loc p) _ from rfl,
    map_sum, Polynomial.comp, eval₂_trunc_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Polynomial.coe_mapRingHom, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    wittLogTerm_one, map_mul, mul_pow, map_pow]
  ring

private theorem scaledLogPoly_eval (N : ℕ) (Y : Polynomial (Ainf p)) :
    (scaledLogPoly p N Y).eval 1 = ∑ n ∈ Finset.range N, pLogTerm p (Y.eval 1) n := by
  rw [scaledLogPoly, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun n _ => by
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      pLogTerm_eq_mul_pow p (Y.eval 1) n]

private abbrev pSpan (k : ℕ) : Ideal (Ainf p) := Ideal.span {((p : Ainf p)^k)}

private theorem pLogTerm_one_dvd (k n : ℕ) (hn : 2*k ≤ n) :
    (p : Ainf p)^k ∣ pLogTerm p 1 n := by
  by_cases h0 : n = 0
  · simp [pLogTerm, h0]
  obtain ⟨d, hd⟩ := (logCoeff_spec p h0).2 k hn
  rw [pLogTerm, ite_eq_right h0, one_pow, mul_one, hd, map_mul, map_pow, map_natCast]
  exact Dvd.dvd.mul_left (dvd_mul_right _ _) _

private theorem scaledLogPoly_high (k j : ℕ) (hj : 4*k ≤ j) (Y : Polynomial (Ainf p))
    (hY : Y.natDegree ≤ 2) :
    (p : Ainf p)^k ∣ (scaledLogPoly p (4*k) Y).coeff j := by
  rw [scaledLogPoly, Polynomial.finsetSum_coeff]
  apply Finset.dvd_sum
  intro n hn
  by_cases h : 2*k ≤ n
  · rw [Polynomial.coeff_C_mul]
    exact Dvd.dvd.mul_right (pLogTerm_one_dvd p k n h) _
  · have hd : (Polynomial.C (pLogTerm p 1 n) * Y^n).natDegree ≤ 2*n := by
      refine (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_pow_le.trans ?_)
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left n hY
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))]
    exact dvd_zero _

/-- The multiplicative law on Witt units congruent to one modulo p,
written in terms of the arguments to the normalized p-adic logarithm. -/
theorem pLog_add (a b : Ainf p) :
    pLog p (a + b + (p : Ainf p)*a*b) = pLog p a + pLog p b := by
  let Y : Polynomial (Ainf p) := Polynomial.C a * Polynomial.X
  let Z : Polynomial (Ainf p) := Polynomial.C b * Polynomial.X
  let W := Y + Z + Polynomial.C (p : Ainf p) * Y * Z
  have hY : Y.natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans_eq Polynomial.natDegree_X
  have hZ : Z.natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans_eq Polynomial.natDegree_X
  have hW : W.natDegree ≤ 2 := by
    refine (Polynomial.natDegree_add_le_of_le (m := 1) (n := 2) ?_ ?_).trans (by decide)
    · exact (Polynomial.natDegree_add_le_of_le hY hZ).trans (by decide)
    · apply Polynomial.natDegree_mul_le.trans
      have hCY : (Polynomial.C (p : Ainf p) * Y).natDegree ≤ 1 :=
        (Polynomial.natDegree_C_mul_le _ _).trans hY
      omega
  apply (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : Ainf p)})).mpr
  intro k
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  let D := scaledLogPoly p (4*k) W - scaledLogPoly p (4*k) Y - scaledLogPoly p (4*k) Z
  have hlow (j : ℕ) (hj : j < 4*k) : D.coeff j = 0 := by
    have h := X_pow_dvd_logPoly p (4*k) (loc p ((p : Ainf p)*a)) (loc p ((p : Ainf p)*b))
    have he : D.map (loc p) =
        (logPoly p (4*k)).comp
          (Polynomial.C (loc p ((p : Ainf p)*a)) * Polynomial.X +
            Polynomial.C (loc p ((p : Ainf p)*b)) * Polynomial.X +
            Polynomial.C (loc p ((p : Ainf p)*a)) * Polynomial.X *
              (Polynomial.C (loc p ((p : Ainf p)*b)) * Polynomial.X)) -
        (logPoly p (4*k)).comp (Polynomial.C (loc p ((p : Ainf p)*a)) * Polynomial.X) -
        (logPoly p (4*k)).comp (Polynomial.C (loc p ((p : Ainf p)*b)) * Polynomial.X) := by
      dsimp only [D]
      rw [Polynomial.map_sub, Polynomial.map_sub, scaledLogPoly_map, scaledLogPoly_map, scaledLogPoly_map]
      have hy : (Polynomial.C (p : AinfP p)) * Y.map (loc p) =
          Polynomial.C (loc p ((p : Ainf p)*a)) * Polynomial.X := by
        simp only [Y, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, map_mul, map_natCast]
        rw [← mul_assoc]
      have hz : (Polynomial.C (p : AinfP p)) * Z.map (loc p) =
          Polynomial.C (loc p ((p : Ainf p)*b)) * Polynomial.X := by
        simp only [Z, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, map_mul, map_natCast]
        rw [← mul_assoc]
      rw [hy, hz]
      congr 1
      congr 1
      congr 1
      simp only [W, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_natCast,
        Polynomial.C_eq_natCast]
      rw [← hy, ← hz]
      simp only [Polynomial.C_eq_natCast]
      ring
    have hh := Polynomial.X_pow_dvd_iff.mp (by rw [he]; exact h : Polynomial.X^(4*k) ∣ D.map (loc p)) j hj
    rw [Polynomial.coeff_map] at hh
    apply IsLocalization.injective (AinfP p)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (witt_p_ne_zero p))
    simpa only [map_zero] using hh
  have hdCoeffs (j : ℕ) : (p : Ainf p)^k ∣ D.coeff j := by
    by_cases hj : j < 4*k
    · rw [hlow j hj]; exact dvd_zero _
    · simp only [D, Polynomial.coeff_sub]
      exact dvd_sub (dvd_sub (scaledLogPoly_high p k j (by omega) W hW)
        (scaledLogPoly_high p k j (by omega) Y (hY.trans (by decide))))
        (scaledLogPoly_high p k j (by omega) Z (hZ.trans (by decide)))
  have hd : (p : Ainf p)^k ∣ D.eval 1 := by
    rw [Polynomial.eval_eq_sum_range]
    exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_right (hdCoeffs j) _
  have hYe : Y.eval 1 = a := by simp [Y]
  have hZe : Z.eval 1 = b := by simp [Z]
  have hWe : W.eval 1 = a+b+(p : Ainf p)*a*b := by
    simp [W, hYe, hZe]
  simp only [D, Polynomial.eval_sub, scaledLogPoly_eval, hYe, hZe, hWe] at hd
  have hs (x : Ainf p) :
      (p : Ainf p)^k ∣ (∑ n ∈ Finset.range (4*k), pLogTerm p x n) - pLog p x := by
    have h := (pow_dvd_pow (p : Ainf p) (show k ≤ 2*k by omega)).trans (pLog_spec p x (2*k))
    simpa only [← Nat.mul_assoc, show (2*2 : ℕ) = 4 by decide] using h
  convert dvd_sub (dvd_add (dvd_add hd (hs a)) (hs b)) (hs (a+b+(p : Ainf p)*a*b)) using 1
  ring

end ZInQ.Manuscript.BergerComparison
