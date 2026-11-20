import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! Convergence and inversion of Laurent series on a small punctured disk.
This is the analytic step in the comparison at tex 2837–2838 and 2915–2919
(on the spot, provenance (c)). -/

noncomputable section

open Filter
open scoped Topology

namespace ZInQ.Manuscript.RC.X0Model2

private def scalarSeries (P : PowerSeries ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n P)

private theorem scalarSeries_exists (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    ∃ P : PowerSeries ℂ, scalarSeries P = p := by
  refine ⟨PowerSeries.mk p.coeff, ?_⟩
  ext n : 1
  apply ContinuousMultilinearMap.ext_ring
  change (scalarSeries (PowerSeries.mk p.coeff) n (fun _ => 1)) = p n (fun _ => 1)
  rw [scalarSeries, FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one,
    PowerSeries.coeff_mk]
  rfl

private theorem scalarSeries_injective : Function.Injective scalarSeries := by
  intro P Q h
  ext n
  simpa [scalarSeries, FormalMultilinearSeries.coeff_ofScalars] using
    congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) h

private theorem scalarSeries_hasFPowerSeriesAt {P : PowerSeries ℂ} {f : ℂ → ℂ} :
    HasFPowerSeriesAt f (scalarSeries P) 0 ↔
      ∀ᶠ q in 𝓝 0, HasSum (fun n : ℕ => PowerSeries.coeff n P * q ^ n) (f q) := by
  rw [hasFPowerSeriesAt_iff]
  simp only [zero_add, scalarSeries, FormalMultilinearSeries.coeff_ofScalars,
    smul_eq_mul, mul_comm]

private theorem scalarSeries_scalar (c : ℂ) :
    HasFPowerSeriesAt (fun _ : ℂ => c) (scalarSeries (PowerSeries.C c)) 0 := by
  apply scalarSeries_hasFPowerSeriesAt.mpr
  filter_upwards [] with q
  simpa using (hasSum_single (f := fun n : ℕ => PowerSeries.coeff n (PowerSeries.C c) * q ^ n) 0
    fun n hn => by simp [PowerSeries.coeff_C, hn])

private theorem scalarSeries_mul {P Q : PowerSeries ℂ} {f g : ℂ → ℂ}
    (hf : HasFPowerSeriesAt f (scalarSeries P) 0)
    (hg : HasFPowerSeriesAt g (scalarSeries Q) 0) :
    HasFPowerSeriesAt (fun q => f q * g q) (scalarSeries (P * Q)) 0 := by
  apply scalarSeries_hasFPowerSeriesAt.mpr
  filter_upwards [scalarSeries_hasFPowerSeriesAt.mp hf, scalarSeries_hasFPowerSeriesAt.mp hg,
    Metric.eball_mem_nhds (0 : ℂ) hf.radius_pos,
    Metric.eball_mem_nhds (0 : ℂ) hg.radius_pos] with q hP hQ hqP hqQ
  have hPs := (scalarSeries P).summable_norm_apply hqP
  have hQs := (scalarSeries Q).summable_norm_apply hqQ
  simp only [scalarSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at hPs hQs
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hPs hQs
  have hm := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hPs hQs
  rw [hP.tsum_eq, hQ.tsum_eq] at hm
  rw [hm]
  convert hs.of_norm.hasSum using 1
  · funext n
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ⟨i, j⟩ hij => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hij, pow_add]
    ring

private theorem scalarSeries_inv {P : PowerSeries ℂ} {f : ℂ → ℂ}
    (hf : HasFPowerSeriesAt f (scalarSeries P) 0) (hP : PowerSeries.coeff 0 P ≠ 0) :
    ∃ Q : PowerSeries ℂ, P * Q = 1 ∧
      HasFPowerSeriesAt (fun q => (f q)⁻¹) (scalarSeries Q) 0 ∧
      ∀ᶠ q in 𝓝 0, f q ≠ 0 := by
  have h0 : f 0 ≠ 0 := by
    have h := (scalarSeries_hasFPowerSeriesAt.mp hf).self_of_nhds
    have he := (hasSum_single (f := fun n : ℕ => PowerSeries.coeff n P * (0 : ℂ) ^ n) 0
       (fun n hn => by simp [zero_pow hn])).unique h
    rw [← he]
    simpa using hP
  have hne := hf.continuousAt.eventually_ne h0
  obtain ⟨p, hp⟩ := hf.analyticAt.inv h0
  obtain ⟨Q, rfl⟩ := scalarSeries_exists p
  refine ⟨Q, scalarSeries_injective ?_, hp, hne⟩
  have hm := (scalarSeries_mul hf hp).congr (hne.mono fun _ h => mul_inv_cancel₀ h)
  exact hm.eq_formalMultilinearSeries (by simpa using scalarSeries_scalar 1)

private theorem scalarSeries_radius_pos {P : PowerSeries ℂ} {q : ℂ}
    (hq : q ≠ 0) (h : Summable fun n : ℕ => PowerSeries.coeff n P * q ^ n) :
    0 < (scalarSeries P).radius := by
  refine lt_of_lt_of_le (b := (‖q‖₊ : ENNReal)) (by simpa using norm_pos_iff.mpr hq) ?_
  apply FormalMultilinearSeries.le_radius_of_tendsto (l := 0)
  convert tendsto_norm.comp h.tendsto_atTop_zero using 1
  · funext n
    simp [scalarSeries, norm_pow]
  · simp

/-- Extracting a Laurent monomial just shifts the indices of the sum. -/
private theorem hasSum_shift (k : ℤ) (P : PowerSeries ℂ) {q t : ℂ} (hq : q ≠ 0) :
    HasSum (fun m : ℤ => (HahnSeries.single k (1 : ℂ) * (P : LaurentSeries ℂ)).coeff m *
      q ^ m) (t * q ^ k) ↔ HasSum (fun n : ℕ => PowerSeries.coeff n P * q ^ n) t := by
  have hi : Function.Injective (fun n : ℕ => (n : ℤ) + k) := fun _ _ h => by simpa using h
  rw [← hi.hasSum_iff]
  · simp only [Function.comp_def, HahnSeries.coeff_single_mul_add, one_mul,
      LaurentSeries.coeff_coe_powerSeries, zpow_add₀ hq, zpow_natCast, ← mul_assoc]
    exact hasSum_mul_right_iff (zpow_ne_zero k hq)
  · intro m hm
    have hk : m - k < 0 := by
      contrapose! hm
      exact ⟨(m - k).toNat, by change ((m - k).toNat : ℤ) + k = m; omega⟩
    rw [← sub_add_cancel m k, HahnSeries.coeff_single_mul_add, one_mul,
      PowerSeries.coeff_coe, ite_eq_left hk, zero_mul]

/-- Once a Laurent series sums at one nonzero point, its power series part
is analytic on a disk about the origin. -/
private theorem laurentAnalyticPart {A : LaurentSeries ℂ} {q t : ℂ}
    (hq : q ≠ 0) (h : HasSum (fun m : ℤ => A.coeff m * q ^ m) t) :
    ∃ f : ℂ → ℂ, HasFPowerSeriesAt f (scalarSeries A.powerSeriesPart) 0 := by
  let P := A.powerSeriesPart
  have hs : HasSum (fun n : ℕ => PowerSeries.coeff n P * q ^ n) (t / q ^ A.order) := by
    apply (hasSum_shift A.order P hq).mp
    rwa [A.single_order_mul_powerSeriesPart, div_mul_cancel₀ _ (zpow_ne_zero _ hq)]
  let p := scalarSeries P
  exact ⟨p.sum, (p.hasFPowerSeriesOnBall (scalarSeries_radius_pos hq hs.summable)).hasFPowerSeriesAt⟩

/-- Products of Laurent series summable at nonzero seeds agree with the
Cauchy product of their sums throughout a sufficiently small punctured disk. -/
theorem eventually_hasSum_laurent_mul {A B : LaurentSeries ℂ} {q r t u : ℂ}
    (hq : q ≠ 0) (hr : r ≠ 0)
    (hA : HasSum (fun m : ℤ => A.coeff m * q ^ m) t)
    (hB : HasSum (fun m : ℤ => B.coeff m * r ^ m) u) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a b : ℂ,
      HasSum (fun m : ℤ => A.coeff m * z ^ m) a →
      HasSum (fun m : ℤ => B.coeff m * z ^ m) b →
      HasSum (fun m : ℤ => (A * B).coeff m * z ^ m) (a * b) := by
  obtain ⟨f, hf⟩ := laurentAnalyticPart hq hA
  obtain ⟨g, hg⟩ := laurentAnalyticPart hr hB
  have hle : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  have hm := (scalarSeries_hasFPowerSeriesAt.mp (scalarSeries_mul hf hg)).filter_mono hle
  have hAf := (scalarSeries_hasFPowerSeriesAt.mp hf).filter_mono hle
  have hBg := (scalarSeries_hasFPowerSeriesAt.mp hg).filter_mono hle
  have he : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 := eventually_mem_nhdsWithin
  filter_upwards [hm, hAf, hBg, he] with z hz hzf hzg hz0 a b ha hb
  have hsa := (hasSum_shift A.order A.powerSeriesPart hz0).mpr hzf
  have hsb := (hasSum_shift B.order B.powerSeriesPart hz0).mpr hzg
  rw [A.single_order_mul_powerSeriesPart] at hsa
  rw [B.single_order_mul_powerSeriesPart] at hsb
  rw [← hsa.unique ha, ← hsb.unique hb]
  have hp : (HahnSeries.single (A.order + B.order) (1 : ℂ) : LaurentSeries ℂ) *
      ((A.powerSeriesPart * B.powerSeriesPart : PowerSeries ℂ) : LaurentSeries ℂ) = A * B := by
    conv_rhs => rw [← A.single_order_mul_powerSeriesPart, ← B.single_order_mul_powerSeriesPart]
    rw [PowerSeries.coe_mul, ← one_mul (1 : ℂ), ← HahnSeries.single_mul_single, one_mul]
    ring
  have hs := (hasSum_shift (A.order + B.order) _ hz0).mpr hz
  rw [hp, zpow_add₀ hz0] at hs
  convert hs using 1
  ring

/-- Near zero a nonzero Laurent series has nonzero sum, and the reciprocal
has the coefficients of the formal Laurent inverse. -/
theorem eventually_hasSum_laurent_inv {A : LaurentSeries ℂ} {q t : ℂ} (hA0 : A ≠ 0)
    (hq : q ≠ 0) (hA : HasSum (fun m : ℤ => A.coeff m * q ^ m) t) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a : ℂ,
      HasSum (fun m : ℤ => A.coeff m * z ^ m) a →
      a ≠ 0 ∧ HasSum (fun m : ℤ => (A⁻¹).coeff m * z ^ m) a⁻¹ := by
  obtain ⟨f, hf⟩ := laurentAnalyticPart hq hA
  have hP : PowerSeries.coeff 0 A.powerSeriesPart ≠ 0 := by
    simpa [LaurentSeries.powerSeriesPart_coeff] using
      (HahnSeries.coeff_order_eq_zero.not.mpr hA0)
  obtain ⟨Q, hQ, hi, hne⟩ := scalarSeries_inv hf hP
  have hle : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  have hAf := (scalarSeries_hasFPowerSeriesAt.mp hf).filter_mono hle
  have hQi := (scalarSeries_hasFPowerSeriesAt.mp hi).filter_mono hle
  have he : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 := eventually_mem_nhdsWithin
  have hAi : (HahnSeries.single (-A.order) (1 : ℂ) : LaurentSeries ℂ) * Q = A⁻¹ := by
    symm
    apply inv_eq_of_mul_eq_one_right
    conv_lhs => arg 1; rw [← A.single_order_mul_powerSeriesPart]
    rw [mul_mul_mul_comm, HahnSeries.single_mul_single, add_neg_cancel, mul_one,
      ← HahnSeries.C_apply, HahnSeries.C_one, one_mul, ← PowerSeries.coe_mul, hQ, PowerSeries.coe_one]
  filter_upwards [hAf, hQi, hne.filter_mono hle, he] with z hzf hzi hz0 hz a ha
  have hsa := (hasSum_shift A.order A.powerSeriesPart hz).mpr hzf
  rw [A.single_order_mul_powerSeriesPart] at hsa
  rw [← hsa.unique ha]
  refine ⟨mul_ne_zero hz0 (zpow_ne_zero _ hz), ?_⟩
  have hs := (hasSum_shift (-A.order) Q hz).mpr hzi
  rw [hAi, zpow_neg] at hs
  simpa only [mul_inv] using hs


end ZInQ.Manuscript.RC.X0Model2
