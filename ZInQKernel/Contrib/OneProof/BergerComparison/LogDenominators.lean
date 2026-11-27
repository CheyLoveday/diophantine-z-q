import ZInQKernel.Contrib.OneProof.BergerComparison.MaximalSeparation

/-! At degrees below twice p^k, the p^k-scaled formal logarithm
has a single coefficient that survives modulo p. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst FontaineSt PowerSeries
open PanBergerSplit (Ainf AinfP)
open ZInQ.Contrib.G9.BdrKer.Cp

variable (p : ℕ) [hp : Fact p.Prime]

set_option maxHeartbeats 500000

private abbrev loc := algebraMap (Ainf p) (AinfP p)
private abbrev T := PreTilt 𝓞_ℂ_[p] p

/-- Up to twice p^k, the quotient p^k/n is integral and is divisible
by p unless n = p^k, when the quotient is one. -/
theorem exists_scaledInverse (k n : ℕ) (hn : 0 < n) (hbound : n < 2*p^k) :
    ∃ z : ℤ_[p], (z : ℚ_[p]) = (p : ℚ_[p])^k * (n : ℚ_[p])⁻¹ ∧
      (if n = p^k then z = 1 else (p : ℤ_[p]) ∣ z) := by
  obtain ⟨v, m, hd, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.out.ne_one
  have hm : m ≠ 0 := fun h => hd (h ▸ dvd_zero p)
  have hle : p^v ≤ n := he ▸ Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hm)
  have hv : v ≤ k := by
    by_contra! h
    have hh : p^(k+1) ≤ p^v := Nat.pow_le_pow_right hp.out.pos (by omega)
    rw [pow_succ] at hh
    nlinarith [hp.out.two_le]
  by_cases hn' : n = p^k
  · refine ⟨1, ?_, by rw [ite_eq_left hn']⟩
    rw [hn', Nat.cast_pow, PadicInt.coe_one,
      mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero))]
  · have hv' : v < k := by
      by_contra! h
      have hve : v = k := by omega
      rw [hve] at he
      have hm1 : m = 1 := by
        by_contra hm1
        have h2 : 2 ≤ m := by omega
        have := Nat.mul_le_mul_left (p^k) h2
        rw [Nat.mul_comm _ 2, ← he] at this
        omega
      exact hn' (by simpa only [hm1, mul_one] using he)
    have hu : IsUnit (m : ℤ_[p]) := PadicInt.isUnit_iff.mpr
      (PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hd))
    let u := hu.unit
    refine ⟨(p : ℤ_[p])^(k-v) * (↑u⁻¹ : ℤ_[p]), ?_, ?_⟩
    · have huq : ((u : ℤ_[p]) : ℚ_[p]) = m := by
        rw [IsUnit.unit_spec, PadicInt.coe_natCast]
      have hui : (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * (m : ℚ_[p]) = 1 := by
        rw [← huq, ← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]
      apply (eq_mul_inv_iff_mul_eq₀ (Nat.cast_ne_zero.mpr hn.ne')).mpr
      push_cast
      rw [he, Nat.cast_mul, Nat.cast_pow]
      calc
        (p : ℚ_[p]) ^ (k-v) * (↑(↑u⁻¹ : ℤ_[p]) : ℚ_[p]) * ((p : ℚ_[p]) ^ v * (m : ℚ_[p])) =
            (p : ℚ_[p]) ^ (k-v) * (p : ℚ_[p]) ^ v *
              ((↑(↑u⁻¹ : ℤ_[p]) : ℚ_[p]) * (m : ℚ_[p])) := by ring
        _ = _ := by rw [hui, mul_one, ← pow_add, Nat.sub_add_cancel hv]
    · rw [ite_eq_right hn']
      exact (dvd_pow_self _ (by omega : k-v ≠ 0)).mul_right _

/-- The formal series log(1-X), expressed without alternating signs. -/
def negativeLogSeries : (AinfP p)⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else -qpToLoc p ((n : ℚ_[p])⁻¹)

/-- Substituting ξ/p gives the normalized de Rham logarithm of [p̃]. -/
theorem negativeLogSeries_eval :
    psEval (Ith p) (omegaP_mem p) (negativeLogSeries p) = logPTilde p := by
  change psEval (Ith p) (omegaP_mem p) (negativeLogSeries p) =
    psEval (Ith p) (pTildeArg_mem p) (logSeries p)
  refine psEval_eq_of_terms (Ith p) (omegaP_mem p) (pTildeArg_mem p) _ _ fun n => ?_
  rw [negativeLogSeries, logSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases h : n = 0
  · simp [h]
  rw [ite_eq_right h, ite_eq_right h, pTildeArg]
  have hneg : -omegaP p = (-1 : AinfP p) * omegaP p := (neg_one_mul _).symm
  rw [hneg, mul_pow]
  have hsign : (-1 : AinfP p) ^ (n+1) * (-1 : AinfP p)^n = -1 := by
    rw [← pow_add, show n+1+n = 2*n+1 by omega, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  linear_combination -(qpToLoc p ((n : ℚ_[p])⁻¹)) * (omegaP p)^n * hsign

private def scaledInverse (k n : ℕ) (hn : 0 < n) (hbound : n < 2*p^k) : ℤ_[p] :=
  Classical.choose (exists_scaledInverse p k n hn hbound)

private theorem scaledInverse_spec (k n : ℕ) (hn : 0 < n) (hbound : n < 2*p^k) :
    algebraMap ℤ_[p] ℚ_[p] (scaledInverse p k n hn hbound) =
      (p : ℚ_[p])^k * (n : ℚ_[p])⁻¹ ∧
      (if n = p^k then scaledInverse p k n hn hbound = 1
        else (p : ℤ_[p]) ∣ scaledInverse p k n hn hbound) :=
  Classical.choose_spec (exists_scaledInverse p k n hn hbound)

/-- A scaled truncation with coefficients lifted to the Witt ring.
Terms after the cutoff can be set to zero. -/
def scaledNegativeLog (k N : ℕ) (hN : N < 2*p^k) : (Ainf p)⟦X⟧ :=
  PowerSeries.mk fun n =>
    if hn : 0 < n ∧ n ≤ N then
      -zpToW p (scaledInverse p k n hn.1 (hn.2.trans_lt hN))
    else 0

/-- The Witt coefficients of the truncation are the scaled log coefficients. -/
theorem scaledNegativeLog_coeff (k N : ℕ) (hN : N < 2*p^k) {n : ℕ} (hn : n ≤ N) :
    loc p (coeff n (scaledNegativeLog p k N hN)) =
      (p : AinfP p)^k * coeff n (negativeLogSeries p) := by
  rw [scaledNegativeLog, negativeLogSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  rcases n.eq_zero_or_pos with rfl | hpos
  · simp
  rw [dite_eq_left ⟨hpos, hn⟩, ite_eq_right hpos.ne', map_neg, ← qpToLoc_algebraMap,
    (scaledInverse_spec p k n hpos (hn.trans_lt hN)).1,
    map_mul, map_pow, map_natCast, mul_neg]

/-- The only term surviving reduction modulo p is -X^(p^k). -/
theorem scaledNegativeLog_mod_p (k N : ℕ) (hN : N < 2*p^k) (hle : p^k ≤ N) :
    PowerSeries.map (WittVector.constantCoeff : Ainf p →+* T p) (scaledNegativeLog p k N hN) =
      -X^(p^k) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map, scaledNegativeLog, PowerSeries.coeff_mk, map_neg,
    PowerSeries.coeff_X_pow]
  by_cases hn : n = p^k
  · subst n
    have hpos : 0 < p^k := pow_pos hp.out.pos _
    have e := (scaledInverse_spec p k (p^k) hpos (hle.trans_lt hN)).2
    rw [ite_eq_left rfl] at e
    rw [dite_eq_left ⟨hpos, hle⟩, ite_eq_left rfl, e, map_neg, map_one, map_one]
  · rw [ite_eq_right hn, neg_zero]
    split
    · rename_i h
      have hd := (scaledInverse_spec p k n h.1 (h.2.trans_lt hN)).2
      rw [ite_eq_right hn] at hd
      obtain ⟨z, hz⟩ := hd
      rw [hz, map_neg, map_mul, map_natCast, map_mul, map_natCast,
        CharP.cast_eq_zero (T p) p, zero_mul, neg_zero]
    · rw [map_zero]

end ZInQ.Manuscript.BergerComparison
