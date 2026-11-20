import ZInQKernel.Contrib.OneProof.RC.ParamAtScale.Coordinates
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.EichlerIntegral.Transformation

/-! The cusp germs of the analytic coordinates at tex 1785–1787 and 2836–2838.
The local extension is on-the-spot (c). -/

noncomputable section

open Complex Filter Topology
open UpperHalfPlane hiding I
open Matrix Matrix.SpecialLinearGroup ConjAct
open scoped MatrixGroups ModularForm Pointwise
open ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Manuscript.RC.ParamAtScale

namespace ZInQ.Manuscript.RC.ModFnField

/-- The strict period used for the chart at `σ∞`. -/
abbrev translatedLevel (N : ℕ) (σ : SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ) :=
  toConjAct (mapGL ℝ σ)⁻¹ • (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))

/-- The Eichler primitive extends holomorphically in the parameter at every cusp,
with the integration constant appropriate to the cusp. -/
theorem scaledPrimitive_cusp {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (κ : ℂ) (σ : SL(2, ℤ)) :
    0 < (translatedLevel N σ).strictWidthInfty ∧
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ ∀ τ : ℍ,
      F (Function.Periodic.qParam (translatedLevel N σ).strictWidthInfty τ) =
        scaledPrimitive f κ (σ • τ : ℍ) := by
  let Γ' := translatedLevel N σ
  have : Γ'.IsArithmetic := by
    simpa [Γ', translatedLevel, ← (Rat.castHom ℝ).algebraMap_toAlgebra, map_inv, map_mapGL]
      using Subgroup.IsArithmetic.conj
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) (mapGL ℚ σ)⁻¹
  let h := Γ'.strictWidthInfty
  have hh : 0 < h := Γ'.strictWidthInfty_pos
  let f' := CuspForm.translate f (mapGL ℝ σ)
  have hf' : ⇑f' = ⇑f ∣[(2 : ℤ)] σ := by
    rw [CuspForm.coe_translate, ModularForm.SL_slash,
      TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL]
  let g := TauCeti.eichlerIntegral h 1 f'
  have hper : Function.Periodic (g ∘ ofComplex) h :=
    TauCeti.periodic_eichlerIntegral_comp_ofComplex hh.ne' 1
  have hfper := SlashInvariantFormClass.periodic_comp_ofComplex f'
    Γ'.strictWidthInfty_mem_strictPeriods
  have hg : AnalyticAt ℂ (cuspFunction h g) 0 :=
    analyticAt_cuspFunction_zero hh hper
      (TauCeti.mdifferentiable_eichlerIntegral hh hfper (ModularFormClass.holo f')
        (ModularFormClass.bdd_at_infty f') 1)
      (TauCeti.isZeroAtImInfty_eichlerIntegral hh hfper (ModularFormClass.holo f')
        (ModularFormClass.bdd_at_infty f') 0).isBoundedAtImInfty
  let c : ℂ := (-2 * Real.pi * I) *
    TauCeti.cuspIntegral f' (mapGL ℚ σ⁻¹ • OnePoint.infty) OnePoint.infty
  refine ⟨hh, fun q => κ * (cuspFunction h g q - c),
    analyticAt_const.mul (hg.sub analyticAt_const), fun τ => ?_⟩
  change κ * (cuspFunction h g (Function.Periodic.qParam h τ) - c) =
    scaledPrimitive f κ (σ • τ : ℍ)
  rw [eq_cuspFunction τ hh.ne' hper, scaledPrimitive, ofComplex_apply, eichlerPotential]
  congr 1
  have he := TauCeti.CuspFormClass.eichlerIntegral_slash_apply
    (n := 0) (by norm_num : (2 : ℤ) = (0 : ℕ) + 2)
    f (by norm_num : (0 : ℝ) < 1) (TauCeti.one_mem_strictPeriods_Gamma0_map N)
    f' hh Γ'.strictWidthInfty_mem_strictPeriods σ hf' τ
  simpa only [g, c, Nat.zero_add, Nat.cast_zero, neg_zero, ModularForm.SL_slash_apply,
    zpow_zero, pow_zero, pow_one, Nat.factorial_zero, Nat.cast_one, div_one, mul_one] using he.symm

/-- Both affine coordinates have meromorphic germs in the strict local parameter
at every cusp, including when the limiting primitive meets the period lattice. -/
theorem coordinates_cusp_meromorphic (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (κ : ℂ) (σ : SL(2, ℤ)) :
    0 < (translatedLevel N σ).strictWidthInfty ∧
    ∃ (x y : ℂ → ℂ), MeromorphicAt x 0 ∧ MeromorphicAt y 0 ∧ ∀ τ : ℍ,
      x (Function.Periodic.qParam (translatedLevel N σ).strictWidthInfty τ) =
        xCoordinate E f Lat κ (σ • τ : ℍ) ∧
      y (Function.Periodic.qParam (translatedLevel N σ).strictWidthInfty τ) =
        yCoordinate E f Lat κ (σ • τ : ℍ) := by
  obtain ⟨hh, F, hF, hval⟩ := scaledPrimitive_cusp f κ σ
  let x := fun q => Lat.weierstrassP (F q) - (E.b₂ : ℂ) / 12
  let y := fun q => (Lat.derivWeierstrassP (F q) - (E.a₁ : ℂ) * x q - (E.a₃ : ℂ)) / 2
  have hx : MeromorphicAt x 0 := ((Lat.meromorphic_weierstrassP (F 0)).comp_analyticAt hF).sub
    (MeromorphicAt.const _ _)
  have hy : MeromorphicAt y 0 := (((Lat.meromorphic_derivWeierstrassP (F 0)).comp_analyticAt hF).sub
    ((MeromorphicAt.const _ _).mul hx)).sub (MeromorphicAt.const _ _) |>.div (MeromorphicAt.const _ _)
  exact ⟨hh, x, y, hx, hy, fun τ => by simp only [x, y, hval τ, xCoordinate, yCoordinate, and_self]⟩


end ZInQ.Manuscript.RC.ModFnField
