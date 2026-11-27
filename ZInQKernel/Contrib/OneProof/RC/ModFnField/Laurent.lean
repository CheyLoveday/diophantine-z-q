import ZInQKernel.Contrib.OneProof.RC.ModFnField.Cusps

/-! Convergent Laurent expansions in the cusp parameter (provenance (c)). -/

noncomputable section

open Filter Topology
open UpperHalfPlane
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
open ZInQ.Manuscript.RC.ParamAtScale

namespace ZInQ.Manuscript.RC.ModFnField

/-- Shift an ordinary convergent power series by a finite number of terms.
Coefficients can be read through any ring map to the complex numbers. -/
theorem hasSum_laurent_shift {R : Type*} [CommRing R] (ι : R →+* ℂ)
    (p : PowerSeries R) (d : ℕ) {q g : ℂ} (hq : q ≠ 0)
    (h : HasSum (fun n : ℕ => ι (p.coeff n) * q ^ n) (q ^ d * g)) :
    HasSum (fun m : ℤ => ι
      ((HahnSeries.single (-(d : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ R p).coeff m) * q ^ m) g := by
  let a : LaurentSeries R := HahnSeries.single (-(d : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ R p
  change HasSum (fun m : ℤ => ι (a.coeff m) * q ^ m) g
  have hcoeff (m : ℤ) : a.coeff m = (HahnSeries.ofPowerSeries ℤ R p).coeff (m + d) := by
    simp [a, HahnSeries.coeff_single_mul]
  let ix : ℕ → ℤ := fun n => (n : ℤ) - d
  have hinj : Function.Injective ix := fun j k h => by dsimp [ix] at h; omega
  have hzero (m : ℤ) (hm : m ∉ Set.range ix) : ι (a.coeff m) * q ^ m = 0 := by
    have hlt : m < -(d : ℤ) := by
      by_contra! h
      exact hm ⟨(m + d).toNat, by dsimp [ix]; omega⟩
    rw [hcoeff, ModularCurve.ofPowerSeries_coeff_of_neg _ (by omega), map_zero, zero_mul]
  apply (Function.Injective.hasSum_iff hinj hzero).mp
  convert h.mul_right (q ^ (-(d : ℤ))) using 1
  · ext n
    have hix : ix n + d = (n : ℤ) := by dsimp [ix]; omega
    rw [Function.comp_apply, hcoeff, hix, HahnSeries.ofPowerSeries_apply_coeff]
    change ι (p.coeff n) * q ^ ((n : ℤ) - d) = ι (p.coeff n) * q ^ n * q ^ (-(d : ℤ))
    rw [sub_eq_add_neg, zpow_add₀ hq, zpow_natCast]
    ring
  · rw [_root_.zpow_neg, zpow_natCast, mul_comm (q ^ d) g, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero d hq), mul_one]

/-- A meromorphic function of `q` has a convergent bilateral expansion on
a punctured disk, with a finite principal part. -/
theorem meromorphicAt_hasSum_laurent {g : ℂ → ℂ} (hg : MeromorphicAt g 0) :
    ∃ (a : LaurentSeries ℂ) (d : ℕ) (r : ENNReal), 0 < r ∧
      (∀ m : ℤ, m < -(d : ℤ) → a.coeff m = 0) ∧
      ∀ q : ℂ, q ≠ 0 → q ∈ Metric.eball 0 r →
        HasSum (fun m : ℤ => a.coeff m * q ^ m) (g q) := by
  obtain ⟨d, p, r, hp⟩ := hg
  let a : LaurentSeries ℂ :=
    HahnSeries.single (-(d : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.mk p.coeff)
  refine ⟨a, d, r, hp.r_pos, fun m hm => ?_, fun q hq hqr => ?_⟩
  · rw [HahnSeries.coeff_single_mul, one_mul]
    exact ModularCurve.ofPowerSeries_coeff_of_neg _ (by omega)
  · apply hasSum_laurent_shift (RingHom.id ℂ) _ _ hq
    simpa only [PowerSeries.coeff_mk, RingHom.id_apply, sub_zero,
      FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_comm] using hp.hasSum_sub hqr

/-- The two analytic coordinates admit convergent Laurent expansions with finite
principal part in the strict local parameter at every cusp. -/
theorem coordinates_cusp_hasSum (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (κ : ℂ) (σ : SL(2, ℤ)) :
    ∃ (a b : LaurentSeries ℂ) (d e : ℕ) (T : ℝ),
      (∀ m : ℤ, m < -(d : ℤ) → a.coeff m = 0) ∧
      (∀ m : ℤ, m < -(e : ℤ) → b.coeff m = 0) ∧
      ∀ τ : ℍ, T < τ.im →
        HasSum (fun m : ℤ => a.coeff m *
          Function.Periodic.qParam (translatedLevel N σ).strictWidthInfty τ ^ m)
            (xCoordinate E f Lat κ (σ • τ : ℍ)) ∧
        HasSum (fun m : ℤ => b.coeff m *
          Function.Periodic.qParam (translatedLevel N σ).strictWidthInfty τ ^ m)
            (yCoordinate E f Lat κ (σ • τ : ℍ)) := by
  obtain ⟨hh, x, y, hx, hy, hxy⟩ := coordinates_cusp_meromorphic E f Lat κ σ
  obtain ⟨a, d, r, hr, ha, hsx⟩ := meromorphicAt_hasSum_laurent hx
  obtain ⟨b, e, s, hs, hb, hsy⟩ := meromorphicAt_hasSum_laurent hy
  let Q := fun τ : ℍ => Function.Periodic.qParam (translatedLevel N σ).strictWidthInfty τ
  have ht : Tendsto Q atImInfty (𝓝 0) := qParam_tendsto_atImInfty hh
  obtain ⟨T, hT⟩ := (atImInfty_mem _).mp
    (inter_mem (ht (Metric.eball_mem_nhds _ hr)) (ht (Metric.eball_mem_nhds _ hs)))
  refine ⟨a, b, d, e, T, ha, hb, fun τ hτ => ?_⟩
  have hm : Q τ ∈ Metric.eball 0 r ∩ Metric.eball 0 s := hT τ hτ.le
  have hn : Q τ ≠ 0 := Function.Periodic.qParam_ne_zero _
  exact ⟨(hxy τ).1 ▸ hsx _ hn hm.1, (hxy τ).2 ▸ hsy _ hn hm.2⟩


end ZInQ.Manuscript.RC.ModFnField
