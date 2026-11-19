import ZInQKernel.Contrib.OneProof.RC.ElkikMD.Periods
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.EichlerIntegral.Transformation

/-! Cusp values of the based Eichler primitive (tex 1785–1787, 2937–2941).
The analytic comparison uses the existing geodesic integral library (provenance (c)). -/

noncomputable section

open Complex Filter Topology
open UpperHalfPlane hiding I
open Matrix Matrix.SpecialLinearGroup ConjAct
open scoped MatrixGroups ModularForm Pointwise
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Manuscript.RC.ElkikMD

namespace ZInQ.Manuscript.RC.ParamAtScale

/-- The analytic value at a cusp, in the period quotient of the same lattice
as the interior parametrization. -/
def torusValue (Lat : PeriodPair) (f : ℍ → ℂ) (κ : ℂ) (τ : ℍ) :
    ℂ ⧸ Lat.lattice.toAddSubgroup :=
  QuotientAddGroup.mk' Lat.lattice.toAddSubgroup (κ * eichlerPotential f τ)

/-- The period condition descends the torus value through the level action. -/
theorem torusValue_smul {N : ℕ} {f : ℍ → ℂ} {Lat : PeriodPair} {κ : ℂ}
    (hκ : IsParamScale N f Lat κ) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (τ : ℍ) : torusValue Lat f κ (γ • τ) = torusValue Lat f κ τ := by
  apply sub_eq_zero.mp
  rw [torusValue, torusValue, ← map_sub, ← mul_sub]
  exact (QuotientAddGroup.eq_zero_iff _).mpr (hκ.2 γ hγ τ)

/-- The analytic map is based at infinity for every scale. -/
theorem torusValue_tendsto_infty {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (κ : ℂ) :
    Tendsto (torusValue Lat f κ) atImInfty (𝓝 0) := by
  have hz : IsZeroAtImInfty (eichlerPotential f) :=
    TauCeti.isZeroAtImInfty_eichlerIntegral (by norm_num : (0 : ℝ) < 1)
      (SlashInvariantFormClass.periodic_comp_ofComplex f
        (TauCeti.one_mem_strictPeriods_Gamma0_map N))
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) 0
  have h : Tendsto (torusValue Lat f κ) atImInfty
      (𝓝 (QuotientAddGroup.mk' Lat.lattice.toAddSubgroup (κ * 0))) :=
    QuotientAddGroup.continuous_mk.continuousAt.tendsto.comp (tendsto_const_nhds.mul hz)
  simpa only [mul_zero, map_zero] using h

/-- At any rational cusp, the analytic parametrization in the period quotient
tends to the scaled symbol. The filter `atImInfty` is in the coordinate
obtained by applying a matrix taking infinity to the given cusp. -/
theorem torusValue_tendsto_cusp {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (κ : ℂ) (r : ℚ) (σ : SL(2, ℤ))
    (hσ : mapGL ℚ σ • (OnePoint.infty : OnePoint ℚ) = r) :
    Tendsto (fun τ : ℍ => torusValue Lat f κ (σ • τ)) atImInfty
      (𝓝 (QuotientAddGroup.mk' Lat.lattice.toAddSubgroup (κ * cuspSymbol f r))) := by
  let Γ := (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
  let Γ' := toConjAct (mapGL ℝ σ)⁻¹ • Γ
  have : Γ'.IsArithmetic := by
    simpa [Γ', ← (Rat.castHom ℝ).algebraMap_toAlgebra, map_inv, map_mapGL]
      using Subgroup.IsArithmetic.conj Γ (mapGL ℚ σ)⁻¹
  let f' := CuspForm.translate f (mapGL ℝ σ)
  have hf' : ⇑f' = ⇑f ∣[(2 : ℤ)] σ := by
    rw [CuspForm.coe_translate, ModularForm.SL_slash,
      TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL]
  have hperiod : TauCeti.cuspIntegral f' (mapGL ℚ σ⁻¹ • OnePoint.infty) OnePoint.infty =
      TauCeti.cuspIntegral f OnePoint.infty (r : OnePoint ℚ) := by
    have hdet : 0 < ((mapGL ℚ σ).det : ℚ) := by
      rw [det_mapGL, Units.val_one]
      exact one_pos
    rw [hf', ModularForm.SL_slash, TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
      ← ModularForm.rat_slash_mapGL,
      TauCeti.cuspIntegral_slash _ (by simpa only [Matrix.GeneralLinearGroup.val_det_apply]
        using hdet), ← mul_smul, ← map_mul,
      mul_inv_cancel, map_one, one_smul, hσ]
  have hformula (τ : ℍ) : eichlerPotential f (σ • τ) =
      TauCeti.eichlerIntegral Γ'.strictWidthInfty 1 f' τ + cuspSymbol f r := by
    have he := TauCeti.CuspFormClass.eichlerIntegral_slash_apply
      (n := 0) (by norm_num : (2 : ℤ) = (0 : ℕ) + 2)
      f (by norm_num : (0 : ℝ) < 1) (TauCeti.one_mem_strictPeriods_Gamma0_map N)
      f' Γ'.strictWidthInfty_pos Γ'.strictWidthInfty_mem_strictPeriods σ hf' τ
    simp only [Nat.zero_add, Nat.cast_zero, neg_zero, ModularForm.SL_slash_apply,
      zpow_zero, pow_zero, pow_one, Nat.factorial_zero, Nat.cast_one, div_one,
      mul_one] at he
    rw [hperiod, TauCeti.cuspIntegral_symm] at he
    unfold eichlerPotential cuspSymbol
    rw [he]
    ring
  have hz : IsZeroAtImInfty (TauCeti.eichlerIntegral Γ'.strictWidthInfty 1 f') :=
    TauCeti.isZeroAtImInfty_eichlerIntegral Γ'.strictWidthInfty_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex f' Γ'.strictWidthInfty_mem_strictPeriods)
      (ModularFormClass.holo f') (ModularFormClass.bdd_at_infty f') 0
  have hl : Tendsto (fun τ : ℍ => eichlerPotential f (σ • τ)) atImInfty
      (𝓝 (cuspSymbol f r)) := by
    simp only [hformula]
    simpa only [zero_add] using (show Tendsto _ atImInfty (𝓝 (0 : ℂ)) from hz).add
      (tendsto_const_nhds (x := cuspSymbol f r))
  exact QuotientAddGroup.continuous_mk.continuousAt.tendsto.comp (tendsto_const_nhds.mul hl)

/-- The form of the cusp comparison used by Elkik, at all the requested
cusps with one nonzero rational scalar. This is a comparison of boundary
values of the analytic map; attaching them to Jacobian classes is separate. -/
theorem rational_cusp_comparison {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) {κ : ℚ} (hκ : κ ≠ 0) :
    ∃ κ' : ℚ, κ' ≠ 0 ∧ (κ' : ℂ) = (κ : ℂ) ∧
      ∀ r : ℚ, ∃ σ : SL(2, ℤ), mapGL ℚ σ • (OnePoint.infty : OnePoint ℚ) = r ∧
        Tendsto (fun τ : ℍ => torusValue Lat f (κ : ℂ) (σ • τ)) atImInfty
          (𝓝 (QuotientAddGroup.mk' Lat.lattice.toAddSubgroup ((κ' : ℂ) * cuspSymbol f r))) := by
  refine ⟨κ, hκ, rfl, fun r => ?_⟩
  obtain ⟨σ, hσ⟩ := (r : OnePoint ℚ).exists_mem_SL2 ℤ
  exact ⟨σ, hσ, torusValue_tendsto_cusp f Lat κ r σ hσ⟩

#print axioms torusValue_smul
#print axioms torusValue_tendsto_infty
#print axioms torusValue_tendsto_cusp
#print axioms rational_cusp_comparison

end ZInQ.Manuscript.RC.ParamAtScale
