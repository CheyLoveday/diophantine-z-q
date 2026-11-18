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

open HDec.PkgI4.BmaxOne (IsGenEps)

/-- Every compatible primitive root system gives a generator of the Tate line. -/
theorem isGenEps_eps : IsGenEps p (eps Z) := by
  refine ⟨untilt_eps Z, ?_⟩
  have h : (frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm (eps Z) = eps1 Z := by
    apply (frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).injective
    rw [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, eps1_pow]
  change PreTilt.untilt ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[1] (eps Z)) ≠ 1
  rw [Function.iterate_one, h, untilt_eps1]
  exact Z.one_ne

/-- The Fontaine period used for localization transforms by the cyclotomic character. -/
theorem bdrPlusMap_tt (σ : GQp p) :
    DR.bdrPlusMap p (oAct p σ) (tt p Z) = qpToPlus p (cycPow p σ 1) * tt p Z := by
  have h := DeRhamScholze.TT.plus_logTeich p σ (untilt_eps Z)
  rw [DeRhamScholze.TT.logTeich_flatAct p (isGenEps_eps p Z) σ,
    DeRhamScholze.TT.zpB_eq_qpToPlus] at h
  rw [tt_eq_logTeich, DeRhamScholze.TT.cycPow_one_eq]
  exact h

/-- The same transformation law in the kernel's fraction field. -/
theorem bdrAct_tt (σ : GQp p) :
    bdrAct p σ (algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (tt p Z)) =
      qpToBdR p (cycPow p σ 1) * algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (tt p Z) := by
  rw [BdRInv.bdrAct_algebraMap, bdrPlusMap_tt, map_mul]
  rfl

local notation "BPlus" => BDeRhamPlus 𝓞_ℂ_[p] p
local notation "AwayT" => Localization.Away (tt p Z)

/-- Extend the Galois action on `B_dR^+` to the ring obtained by inverting `t`. -/
def awayTAct (σ : GQp p) : AwayT →+* AwayT :=
  IsLocalization.Away.lift (tt p Z)
    (g := (algebraMap BPlus AwayT).comp (DR.bdrPlusMap p (oAct p σ))) (by
      rw [RingHom.comp_apply, bdrPlusMap_tt, map_mul]
      exact ((IsUnit.mk0 _ (cycPow_one_ne_zero p σ)).map
        ((algebraMap BPlus AwayT).comp (qpToPlus p))).mul
        (IsLocalization.Away.algebraMap_isUnit (tt p Z)))

/-- The localized action extends the action on the positive ring. -/
theorem awayTAct_comp (σ : GQp p) :
    (awayTAct p Z σ).comp (algebraMap BPlus AwayT) =
      (algebraMap BPlus AwayT).comp (DR.bdrPlusMap p (oAct p σ)) :=
  IsLocalization.Away.lift_comp _ _

/-- The canonical equivalence with `B_dR^+[1/t]` identifies the two Galois actions. -/
theorem bdREquivAwayT_intertwines (σ : GQp p) (x : BdR p) :
    bdREquivAwayT Z (bdrAct p σ x) = awayTAct p Z σ (bdREquivAwayT Z x) := by
  -- Give the input to `transport_extends` the exact localization type it expects.
  let B := ZInQ.Contrib.G9.BdrKer.BdR (𝓞_ℂ_[p] : Type) p
  let f : B →+* B := bdrAct p σ
  have hf : f.comp (algebraMap BPlus B) =
      (algebraMap BPlus B).comp (DR.bdrPlusMap p (oAct p σ)) := by
    apply RingHom.ext
    intro z
    change bdrAct p σ (algebraMap BPlus (BdR p) z) =
      algebraMap BPlus (BdR p) (DR.bdrPlusMap p (oAct p σ) z)
    exact BdRInv.bdrAct_algebraMap p σ z
  have h := ext_of_extends Z _ _ (awayTAct_comp p Z σ) (transport_extends Z f hf)
  let y : B := x
  have hx := DFunLike.congr_fun h (bdREquivAwayT Z y)
  change awayTAct p Z σ (bdREquivAwayT Z y) =
    bdREquivAwayT Z (f ((bdREquivAwayT Z).symm (bdREquivAwayT Z y))) at hx
  rw [AlgEquiv.symm_apply_apply] at hx
  exact hx.symm

/-- The localized maps form a Galois action (composition is multiplication). -/
def awayTAction : GQp p →* (AwayT →+* AwayT) := by
  let e : BdR p ≃ₐ[BPlus] AwayT := bdREquivAwayT Z
  have he (σ : GQp p) (x : BdR p) :
      e (bdrAct p σ x) = awayTAct p Z σ (e x) :=
    bdREquivAwayT_intertwines p Z σ x
  refine { toFun := awayTAct p Z, map_one' := ?_, map_mul' := ?_ }
  · apply RingHom.ext
    intro u
    obtain ⟨x, rfl⟩ := e.surjective u
    simp only [← he, bdrAct_one, RingHom.one_def, RingHom.id_apply]
  · intro σ τ
    apply RingHom.ext
    intro u
    obtain ⟨x, rfl⟩ := e.surjective u
    simp only [RingHom.mul_def, RingHom.comp_apply, ← he, bdrAct_mul]

/-- The two localizations, at `t` and at `ξ`, agree over `B_dR^+`. -/
def awayTEquivAwayXi : AwayT ≃ₐ[BPlus] Localization.Away (varpi p) :=
  (bdREquivAwayT Z).symm.trans (ZInQ.Contrib.G9.BdrKer.Cp.bdREquivAway p)

/-- The period ring dictionary and the cyclotomic law, for the same `t = log[ε]`. -/
theorem fontaineT_reading :
    let t := tt p Z
    let m := IsLocalRing.maximalIdeal BPlus
    t ≠ 0 ∧ t ∈ m ∧ t ∉ m ^ 2 ∧ m = Ideal.span {t} ∧
    (∀ σ : GQp p, DR.bdrPlusMap p (oAct p σ) t = qpToPlus p (cycPow p σ 1) * t) ∧
    (∀ σ : GQp p, bdrAct p σ (algebraMap BPlus (BdR p) t) =
      qpToBdR p (cycPow p σ 1) * algebraMap BPlus (BdR p) t) ∧
    (∃ e : BdR p ≃ₐ[BPlus] AwayT,
      ∀ (σ : GQp p) (x : BdR p), e (bdrAct p σ x) = awayTAct p Z σ (e x)) ∧
    Nonempty (AwayT ≃ₐ[BPlus] Localization.Away (varpi p)) := by
  refine ⟨tt_ne_zero Z, tt_mem Z, ?_, ?_, bdrPlusMap_tt p Z, bdrAct_tt p Z,
    ⟨bdREquivAwayT Z, bdREquivAwayT_intertwines p Z⟩, ⟨awayTEquivAwayXi p Z⟩⟩
  · rw [ZInQ.Contrib.G9.BdrKer.Cp.maximalIdeal_BDeRhamPlus, Ideal.span_singleton_pow]
    exact tt_not_mem_sq Z
  · obtain ⟨u, hu, h⟩ := tt_eq_varpi_mul_unit Z
    rw [ZInQ.Contrib.G9.BdrKer.Cp.maximalIdeal_BDeRhamPlus, h,
      Ideal.span_singleton_mul_right_unit hu]

end

end DeRhamPrint.BdRT

#print axioms DeRhamPrint.BdRT.tt_eq_logTeich
#print axioms DeRhamPrint.BdRT.isGenEps_eps
#print axioms DeRhamPrint.BdRT.bdrPlusMap_tt
#print axioms DeRhamPrint.BdRT.bdrAct_tt
#print axioms DeRhamPrint.BdRT.awayTAct
#print axioms DeRhamPrint.BdRT.awayTAct_comp
#print axioms DeRhamPrint.BdRT.bdREquivAwayT_intertwines
#print axioms DeRhamPrint.BdRT.awayTAction
#print axioms DeRhamPrint.BdRT.awayTEquivAwayXi
#print axioms DeRhamPrint.BdRT.fontaineT_reading
