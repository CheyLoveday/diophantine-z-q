import ZInQKernel.Contrib.OneProof.DeRhamScholzeT

/-!
# The Fontaine period in the kernel's de Rham ring

The adic sum used for localization and the power series evaluation used for the
cyclotomic action give the same element for each compatible root system.
-/

namespace DeRhamPrint.BdRT

open ZInQ.Contrib.G9 (qpToPlus)
open ZInQ.Contrib.G9.PkgI4
open HDec.PkgI4.BergerBst
open HDec.PkgI4.PanBergerSplit (AinfP)
open DeRhamPrint.TDict
open scoped PowerSeries

noncomputable section

variable (p : ℕ) [Fact p.Prime] (Z : RootSystem p)

/-- The adic sum and the evaluated power series define the same Fontaine period. -/
theorem tt_eq_logTeich : tt p Z = logTeich p (untilt_eps Z) := by
  let f : (AinfP p)⟦X⟧ →+* BDeRhamPlus 𝓞_ℂ_[p] p :=
    psEval (Ith p) (teich_sub_one_mem p (untilt_eps Z))
  have hX : f PowerSeries.X = xe Z := by
    have h : xe Z = psEval (Ith p) (teich_sub_one_mem p (untilt_eps Z)) PowerSeries.X := by
      rw [DeRhamScholze.TT.psEval_X, xe]
      simp only [map_sub, map_one]
      rfl
    exact h.symm
  have hC (a : AinfP p) : f (PowerSeries.C a) = ofLoc p a :=
    psEval_C _ _ _
  have hinv (k : ℕ) (hk : k ≠ 0) :
      ofLoc p (HDec.PkgI4.qpToLoc p ((k : ℚ_[p])⁻¹)) =
        Ring.inverse (k : BDeRhamPlus 𝓞_ℂ_[p] p) := by
    have hu : IsUnit (k : ℚ_[p]) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hk)
    change qpToPlus p ((k : ℚ_[p])⁻¹) = _
    rw [← Ring.inverse_eq_inv, hu.map_ringInverse (qpToPlus p), map_natCast]
  have htrunc (n : ℕ) :
      f ((PowerSeries.trunc (n + 1) (logSeries p) : Polynomial (AinfP p)) : (AinfP p)⟦X⟧) =
        logPartial (xe Z) n := by
    induction n with
    | zero => simp [logSeries, logPartial]
    | succ n ih =>
      rw [PowerSeries.trunc_succ, Polynomial.coe_add, map_add, ih,
        ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C,
        Polynomial.coe_pow, Polynomial.coe_X, map_mul, map_pow, hC, hX]
      change _ = ∑ i ∈ Finset.range (n + 1), logTerm (xe Z) (i + 1)
      rw [Finset.sum_range_succ]
      change _ = logPartial (xe Z) n + logTerm (xe Z) (n + 1)
      simp only [logSeries, PowerSeries.coeff_mk, Nat.succ_ne_zero, ite_false,
        map_mul, map_pow, map_neg, map_one, hinv (n + 1) (Nat.succ_ne_zero n), logTerm]
  symm
  refine logPlus_unique (xe Z) (xe_mem Z) _ fun n => ?_
  rw [SModEq.sub_mem, smul_top_eq]
  change logPartial (xe Z) n - f (logSeries p) ∈ _
  have hsplit := congrArg f (PowerSeries.eq_X_pow_mul_shift_add_trunc (n + 1) (logSeries p))
  rw [map_add, map_mul, map_pow, hX, htrunc] at hsplit
  have hx := xe_mem Z
  rw [ZInQ.Contrib.G9.BdrKer.Cp.maximalIdeal_BDeRhamPlus] at hx
  let g := PowerSeries.mk fun i => PowerSeries.coeff (i + (n + 1)) (logSeries p)
  have htail : xe Z ^ (n + 1) * f g ∈
      (Ideal.span {varpi p} : Ideal (BDeRhamPlus 𝓞_ℂ_[p] p)) ^ (n + 1) :=
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hx (n + 1))
  rw [hsplit, ← neg_sub, add_sub_cancel_right]
  exact neg_mem (Ideal.pow_le_pow_right (Nat.le_succ n) htail)

end

end DeRhamPrint.BdRT

#print axioms DeRhamPrint.BdRT.tt_eq_logTeich
