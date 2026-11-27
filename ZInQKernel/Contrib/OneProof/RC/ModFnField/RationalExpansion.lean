import ZInQKernel.Contrib.OneProof.RC.ModFnField.Infinity
import ZInQKernel.Contrib.OneProof.RC.ModFnField.Laurent

/-! Rational bilateral Laurent series at the width-one cusp (provenance (c)). -/

noncomputable section

open Filter Topology UpperHalfPlane
open ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Manuscript.RC.ParamAtScale

namespace ZInQ.Manuscript.RC.ModFnField

/-- An analytic function with rational Taylor coefficients gives a rational
Laurent expansion for any function it represents after clearing a pole. -/
theorem rationalLaurent_of_cleared {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hFr : RationalTaylor F 0)
    (d : ℕ) {g : ℍ → ℂ} {T : ℝ}
    (hg : ∀ τ : ℍ, T < τ.im →
      F (Function.Periodic.qParam 1 τ) = Function.Periodic.qParam 1 τ ^ d * g τ) :
    ∃ (s : LaurentSeries ℚ) (S : ℝ), (∀ m : ℤ, m < -(d : ℤ) → s.coeff m = 0) ∧
      (s.coeff (-(d : ℤ)) : ℂ) = F 0 ∧
      ∀ τ : ℍ, S < τ.im →
        HasSum (fun m : ℤ => (s.coeff m : ℂ) * Function.Periodic.qParam 1 τ ^ m) (g τ) := by
  let c : ℕ → ℚ := fun n => (hFr n).choose / (n.factorial : ℚ)
  have hc (n : ℕ) : (c n : ℂ) = iteratedDeriv n F 0 / n.factorial := by
    have he : (((hFr n).choose : ℚ) : ℂ) = iteratedDeriv n F 0 := (hFr n).choose_spec
    simp only [c, Rat.cast_div, Rat.cast_natCast, he]
  have hp : HasFPowerSeriesAt F (FormalMultilinearSeries.ofScalars ℂ fun n => (c n : ℂ)) 0 := by
    simp_rw [hc]
    exact hF.hasFPowerSeriesAt
  obtain ⟨r, hr⟩ := hp
  let p := PowerSeries.mk c
  let s : LaurentSeries ℚ :=
    HahnSeries.single (-(d : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ ℚ p
  let Q : ℍ → ℂ := fun τ => Function.Periodic.qParam 1 τ
  have ht : Tendsto Q atImInfty (𝓝 0) := qParam_tendsto_atImInfty zero_lt_one
  obtain ⟨S, hS⟩ := (atImInfty_mem _).mp (ht (Metric.eball_mem_nhds 0 hr.r_pos))
  refine ⟨s, max S T, fun m hm => ?_, ?_, fun τ hτ => ?_⟩
  · change (HahnSeries.single (-(d : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ ℚ p).coeff m = 0
    rw [HahnSeries.coeff_single_mul, one_mul]
    exact ModularCurve.ofPowerSeries_coeff_of_neg _ (by omega)
  · change (((HahnSeries.single (-(d : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ ℚ p).coeff (-(d : ℤ)) : ℚ) : ℂ) = F 0
    rw [HahnSeries.coeff_single_mul, one_mul, sub_self]
    change ((HahnSeries.ofPowerSeries ℤ ℚ p).coeff ((0 : ℕ) : ℤ) : ℂ) = F 0
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, hc]
    simp
  · have hq : Q τ ≠ 0 := Function.Periodic.qParam_ne_zero _
    have h := hr.hasSum_sub (hS τ ((le_max_left _ _).trans hτ.le))
    apply hasSum_laurent_shift (Rat.castHom ℂ) p d hq
    rw [← hg τ ((le_max_right _ _).trans_lt hτ)]
    change HasSum (fun n : ℕ => (p.coeff n : ℂ) * Q τ ^ n) (F (Q τ))
    simpa only [sub_zero, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
      p, PowerSeries.coeff_mk] using h

/-- The Laurent series at infinity of the two coordinates have rational
coefficients and pole bounds two and three. -/
theorem coordinates_rationalLaurent (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {L : PeriodPair} (hL : IsLatticeOf E L) {κ : ℚ} (hκ : κ ≠ 0) :
    ∃ (x y : LaurentSeries ℚ) (T : ℝ),
      (∀ m : ℤ, m < -2 → x.coeff m = 0) ∧ (∀ m : ℤ, m < -3 → y.coeff m = 0) ∧
      (x.coeff (-2) : ℂ) = (κ : ℂ)⁻¹ ^ 2 ∧
      ∀ τ : ℍ, T < τ.im →
        HasSum (fun m : ℤ => (x.coeff m : ℂ) * Function.Periodic.qParam 1 τ ^ m)
          (xCoordinate E f L κ τ) ∧
        HasSum (fun m : ℤ => (y.coeff m : ℂ) * Function.Periodic.qParam 1 τ ^ m)
          (yCoordinate E f L κ τ) := by
  obtain ⟨X, Y, hX, hY, hXr, hYr, hX0, T, hT⟩ := coordinates_rationalTaylor E f hf hL hκ
  obtain ⟨x, Sx, hx, hx0, hxs⟩ := rationalLaurent_of_cleared hX hXr 2 (fun τ hτ => (hT τ hτ).1)
  obtain ⟨y, Sy, hy, _, hys⟩ := rationalLaurent_of_cleared hY hYr 3 (fun τ hτ => (hT τ hτ).2)
  exact ⟨x, y, max Sx Sy, hx, hy, hx0.trans hX0, fun τ hτ =>
    ⟨hxs τ ((le_max_left _ _).trans_lt hτ), hys τ ((le_max_right _ _).trans_lt hτ)⟩⟩


end ZInQ.Manuscript.RC.ModFnField
