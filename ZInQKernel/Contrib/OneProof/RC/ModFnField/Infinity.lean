import ZInQKernel.Contrib.OneProof.RC.ModFnField.Weierstrass
import ZInQKernel.Contrib.OneProof.RC.ModFnField.RationalTaylor
import ZInQKernel.RouteK.Rank.LFunctionCd

/-! The rational Taylor series after clearing the two coordinate poles at
the width-one cusp (on-the-spot, provenance (c)). -/

noncomputable section

open UpperHalfPlane Filter Topology
open ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Manuscript.RC.ParamAtScale

namespace ZInQ.Manuscript.RC.ModFnField

/-- At the width-one cusp the scaled primitive is analytic, has rational
Taylor coefficients, and has linear coefficient equal to the scale. -/
theorem primitive_rationalTaylor (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (κ : ℚ) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ RationalTaylor F 0 ∧
      F 0 = 0 ∧ deriv F 0 = (κ : ℂ) ∧ ∀ τ : ℍ,
        F (Function.Periodic.qParam 1 τ) = scaledPrimitive f κ τ := by
  let g := eichlerPotential f
  let G : ℍ → ℂ := (κ : ℂ) • g
  have hh : (0 : ℝ) < 1 := zero_lt_one
  have hper : Function.Periodic (g ∘ ofComplex) 1 :=
    TauCeti.periodic_eichlerIntegral_comp_ofComplex one_ne_zero 1
  have hfper := SlashInvariantFormClass.periodic_comp_ofComplex f
    (TauCeti.one_mem_strictPeriods_Gamma0_map N)
  have hg : AnalyticAt ℂ (cuspFunction 1 g) 0 :=
    analyticAt_cuspFunction_zero hh hper
      (TauCeti.mdifferentiable_eichlerIntegral hh hfper (ModularFormClass.holo f)
        (ModularFormClass.bdd_at_infty f) 1)
      (TauCeti.isZeroAtImInfty_eichlerIntegral hh hfper (ModularFormClass.holo f)
        (ModularFormClass.bdd_at_infty f) 0).isBoundedAtImInfty
  have hG : AnalyticAt ℂ (cuspFunction 1 G) 0 := by
    change AnalyticAt ℂ (cuspFunction 1 ((κ : ℂ) • g)) 0
    rw [cuspFunction_smul hg.continuousAt]
    exact hg.const_smul
  have hval (τ : ℍ) : G τ = scaledPrimitive f κ τ := by
    simp [G, g, scaledPrimitive]
  let a := fun n : ℕ => κ * (E.LFunction n : ℚ) / (n : ℚ)
  have hP := hasFPowerSeriesOnBall_cuspFunction hh hG
    (c := fun n => (a n : ℂ)) (fun τ => by
      rw [hval]
      exact rational_primitive_hasSum E f hf κ τ)
  have hcoeff (n : ℕ) : iteratedDeriv n (cuspFunction 1 G) 0 = (a n : ℂ) * n.factorial := by
    have he := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n)
      (hG.hasFPowerSeriesAt.eq_formalMultilinearSeries hP.hasFPowerSeriesAt)
    simp only [FormalMultilinearSeries.coeff_ofScalars] at he
    exact (div_eq_iff (by exact_mod_cast Nat.factorial_ne_zero n)).mp he
  refine ⟨cuspFunction 1 G, hG, fun n => ?_, ?_, ?_, fun τ => ?_⟩
  · rw [hcoeff]
    exact rationalConstants.mul_mem (SubfieldClass.ratCast_mem _ _) (natCast_mem _ _)
  · simpa [a] using hcoeff 0
  · have hL := (ZInQ.Literature.isMultiplicative_LFunction E).map_one
    simpa [a, hL] using hcoeff 1
  · rw [← hval, show G = (κ : ℂ) • g from rfl, cuspFunction_smul hg.continuousAt]
    change (κ : ℂ) * cuspFunction 1 g (Function.Periodic.qParam 1 τ) = (κ : ℂ) * g τ
    rw [eq_cuspFunction τ one_ne_zero hper]

/-- At nonzero rational scale the analytic coordinates at infinity have pole
bounds two and three, respectively, with rational Taylor coefficients after
multiplication by those powers of the parameter. -/
theorem coordinates_rationalTaylor (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {L : PeriodPair} (hL : IsLatticeOf E L) {κ : ℚ} (hκ : κ ≠ 0) :
    ∃ (X Y : ℂ → ℂ), AnalyticAt ℂ X 0 ∧ AnalyticAt ℂ Y 0 ∧
      RationalTaylor X 0 ∧ RationalTaylor Y 0 ∧ X 0 = (κ : ℂ)⁻¹ ^ 2 ∧
      ∃ T : ℝ, ∀ τ : ℍ, T < τ.im →
        X (Function.Periodic.qParam 1 τ) =
          Function.Periodic.qParam 1 τ ^ 2 * xCoordinate E f L κ τ ∧
        Y (Function.Periodic.qParam 1 τ) =
          Function.Periodic.qParam 1 τ ^ 3 * yCoordinate E f L κ τ := by
  obtain ⟨F, hF, hFr, hF0, hF1, hFτ⟩ := primitive_rationalTaylor E f hf κ
  obtain ⟨u, hu, hur, hu0, hFu⟩ := hFr.factor_at_zero hF hF0
  have hu0' : u 0 ≠ 0 := by
    rw [hu0, hF1]
    exact_mod_cast hκ
  let v := fun q => (u q)⁻¹
  have hv : AnalyticAt ℂ v 0 := hu.inv hu0'
  have hvr : RationalTaylor v 0 := hur.inv hu hu0'
  let A := regularPart L ∘ F
  let B := L.derivWeierstrassPExcept 0 ∘ F
  have ha := L.analyticAt_weierstrassPExcept 0
  have hb := L.analyticAt_derivWeierstrassPExcept 0
  have hA : AnalyticAt ℂ A 0 := (show AnalyticAt ℂ (regularPart L) (F 0) by rwa [hF0]).comp hF
  have hB : AnalyticAt ℂ B 0 :=
    (show AnalyticAt ℂ (L.derivWeierstrassPExcept 0) (F 0) by rwa [hF0]).comp hF
  have hBr₀ : RationalTaylor (L.derivWeierstrassPExcept 0) 0 := by
    have he : deriv (regularPart L) =ᶠ[𝓝 0] L.derivWeierstrassPExcept 0 := by
      filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds (0 : ℂ)] with z hz
      exact L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hz
    intro n
    rw [← he.iteratedDeriv_eq, ← iteratedDeriv_succ']
    exact regularPart_derivatives_rational E hL (n + 1)
  have hAr : RationalTaylor A 0 := RationalTaylor.comp (by rwa [hF0] : AnalyticAt ℂ _ _) hF
    (by rw [hF0]; exact regularPart_derivatives_rational E hL) hFr
  have hBr : RationalTaylor B 0 :=
    RationalTaylor.comp (by rwa [hF0]) hF (by rwa [hF0]) hFr
  let b : ℂ := (E.b₂ : ℂ) / 12
  let a : ℂ := E.a₁
  let c : ℂ := E.a₃
  have bR : b ∈ rationalConstants := rationalConstants.div_mem (SubfieldClass.ratCast_mem _ _) (natCast_mem _ _)
  have aR : a ∈ rationalConstants := SubfieldClass.ratCast_mem _ _
  have cR : c ∈ rationalConstants := SubfieldClass.ratCast_mem _ _
  let X := fun q : ℂ => v q ^ 2 + q ^ 2 * (A q - b)
  let Y := fun q : ℂ => ((-2 : ℂ) * v q ^ 3 + q ^ 3 * B q - a * (q * X q) - c * q ^ 3) * (2 : ℂ)⁻¹
  have hX : AnalyticAt ℂ X 0 := (hv.pow 2).add ((analyticAt_id.pow 2).mul (hA.sub analyticAt_const))
  have hY : AnalyticAt ℂ Y 0 := by
    dsimp [Y]
    exact ((((analyticAt_const.mul (hv.pow 3)).add ((analyticAt_id.pow 3).mul hB)).sub
      (analyticAt_const.mul (analyticAt_id.mul hX))).sub
      (analyticAt_const.mul (analyticAt_id.pow 3))).mul analyticAt_const
  have hXr : RationalTaylor X 0 := (hvr.pow hv 2).add (hv.pow 2)
    ((analyticAt_id.pow 2).mul (hA.sub analyticAt_const))
    ((RationalTaylor.id_zero.pow analyticAt_id 2).mul (analyticAt_id.pow 2)
      (hA.sub analyticAt_const) (hAr.sub hA analyticAt_const (RationalTaylor.const bR 0)))
  have hN2 := RationalTaylor.const (rationalConstants.neg_mem (natCast_mem _ 2)) 0
  have hI2 := RationalTaylor.const (rationalConstants.inv_mem (natCast_mem _ 2)) 0
  have h₁r := hN2.mul analyticAt_const (hv.pow 3) (hvr.pow hv 3)
  have h₂r := (RationalTaylor.id_zero.pow analyticAt_id 3).mul (analyticAt_id.pow 3) hB hBr
  have h₃r := (RationalTaylor.const aR 0).mul analyticAt_const (analyticAt_id.mul hX)
    (RationalTaylor.id_zero.mul analyticAt_id hX hXr)
  have h₄r := (RationalTaylor.const cR 0).mul analyticAt_const (analyticAt_id.pow 3)
    (RationalTaylor.id_zero.pow analyticAt_id 3)
  have h₁ : AnalyticAt ℂ (fun q : ℂ => (-2 : ℂ) * v q ^ 3) 0 := analyticAt_const.mul (hv.pow 3)
  have h₂ : AnalyticAt ℂ (fun q : ℂ => q ^ 3 * B q) 0 := (analyticAt_id.pow 3).mul hB
  have h₃ : AnalyticAt ℂ (fun q : ℂ => a * (q * X q)) 0 := analyticAt_const.mul (analyticAt_id.mul hX)
  have h₄ : AnalyticAt ℂ (fun q : ℂ => c * q ^ 3) 0 := analyticAt_const.mul (analyticAt_id.pow 3)
  have hYr : RationalTaylor Y 0 :=
    (((h₁r.add h₁ h₂ h₂r).sub (h₁.add h₂) h₃ h₃r).sub ((h₁.add h₂).sub h₃) h₄ h₄r).mul
      (((h₁.add h₂).sub h₃).sub h₄) analyticAt_const hI2
  refine ⟨X, Y, hX, hY, hXr, hYr, by simp [X, v, hu0, hF1], ?_⟩
  have huN : ∀ᶠ q : ℂ in 𝓝 0, u q ≠ 0 :=
    hu.continuousAt (isOpen_ne.mem_nhds hu0')
  have he := (qParam_tendsto_atImInfty (by norm_num : (0 : ℝ) < 1)).eventually (hFu.and huN)
  obtain ⟨T, hT⟩ := (atImInfty_mem _).mp he
  refine ⟨T, fun τ hτ => ?_⟩
  let q := Function.Periodic.qParam 1 (τ : ℂ)
  have hq : q ≠ 0 := Function.Periodic.qParam_ne_zero _
  have hqu : F q = q * u q ∧ u q ≠ 0 := hT τ hτ.le
  have hx : X q = q ^ 2 * xCoordinate E f L κ τ := by
    simp only [X, v, xCoordinate, ← hFτ τ, weierstrassP_split, A, Function.comp_apply]
    change (u q)⁻¹ ^ 2 + q ^ 2 * (regularPart L (F q) - b) =
      q ^ 2 * (regularPart L (F q) + 1 / (F q) ^ 2 - b)
    rw [hqu.1]
    field_simp [hq, hqu.2]
    <;> ring
  refine ⟨hx, ?_⟩
  change Y q = q ^ 3 * yCoordinate E f L κ τ
  simp only [Y, v, B, Function.comp_apply, hx, yCoordinate, ← hFτ τ, derivWeierstrassP_split]
  change ((-2 : ℂ) * (u q)⁻¹ ^ 3 + q ^ 3 * L.derivWeierstrassPExcept 0 (F q) -
      a * (q * (q ^ 2 * xCoordinate E f L κ τ)) - c * q ^ 3) * (2 : ℂ)⁻¹ =
    q ^ 3 * ((L.derivWeierstrassPExcept 0 (F q) - 2 / (F q) ^ 3 -
      a * xCoordinate E f L κ τ - c) / 2)
  rw [hqu.1]
  field_simp [hq, hqu.2]
  <;> ring


end ZInQ.Manuscript.RC.ModFnField
