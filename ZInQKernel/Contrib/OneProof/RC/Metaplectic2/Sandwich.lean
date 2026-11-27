import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Gaussian

/-! The local Weyl and upper operator identity of tex 8754–8758.
Compact supports justify the Fubini step; this justification is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic WeilIndex GaussSign Visibility
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal BigOperators

variable (a : Fin 3 → ℕ) (p : Place) [∀ i, NeZero (2 * a i)]

local instance : IsFiniteMeasureOnCompacts (localHaar a p) := by
  unfold localHaar
  exact IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top

omit [∀ i, NeZero (2 * a i)] in
private theorem polar_merge (x y z : LocalVectors p) :
    polar a y z + polar a z x = polar a z (x + y) := by
  simp only [polar, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem fourier_upper_kernel (b : ℚ_[p.val]ˣ) (f : SchwartzBruhat p) (x : LocalVectors p) :
    (dilationFactor p b : ℂ) *
      (fourier a p (upperUnipotent a p b (fourier a p f))).1 x =
      (scaledIndex a p b : ℂ) *
        ∫ y, f.1 y * localPhase p (-(↑(b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val]) * quad a (x + y))
          ∂localHaar a p := by
  classical
  let B : ℚ_[p.val] := (↑(b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val])
  let g := fourier a p f
  let shift : LocalVectors p → LocalVectors p := fun y => B • (x + y)
  have hshift : Continuous shift := continuous_const_smul B |>.comp (continuous_const.add continuous_id)
  obtain ⟨N, hgauss, hg, hshiftN⟩ :=
    ((gaussianCutoff_eventually p a b).and
      ((eventually_vectorCutoff p g.2.2).and
        (eventually_vectorCutoff p (IsCompact.image f.2.2 hshift)))).exists
  let μ := localHaar a p
  let K : Set (LocalVectors p) := vectorCutoff p N
  have hkopen : IsOpen K := rectangle_open p _
  have hkcomp : IsCompact K := rectangle_compact p _
  let cut : LocalVectors p → ℂ := K.indicator (fun _ => 1)
  have hcut : cut ∈ schwartzBruhat p := by
    convert rectangleIndicator_mem p (fun _ => primeUnit p ^ N) 0 using 1
    funext z
    simp [cut, K, vectorCutoff, rectangleIndicator, rectangleCoset]
  let phase (z y : LocalVectors p) :=
    localPhase p ((b : ℚ_[p.val]) * quad a z + polar a z (x + y))
  let h (z y : LocalVectors p) := cut z * (f.1 y * phase z y)
  have hcont : Continuous (Function.uncurry h) := by
    have hphase : Continuous (Function.uncurry phase) := by
      apply (isLocallyConstant_phase p).continuous.comp
      refine (continuous_const.mul ((continuous_quad p a).comp continuous_fst)).add ?_
      exact (continuous_polar p a).comp (continuous_fst.prodMk (continuous_const.add continuous_snd))
    exact (hcut.1.continuous.comp continuous_fst).mul
      ((f.2.1.continuous.comp continuous_snd).mul hphase)
  have hcompact : HasCompactSupport (Function.uncurry h) := by
    apply (hkcomp.prod f.2.2).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (hkcomp.isClosed.prod isClosed_closure)
    rintro ⟨z, y⟩ hy
    change h z y ≠ 0 at hy
    refine ⟨?_, subset_tsupport _ ?_⟩
    · by_contra hz
      exact hy (by simp [h, cut, hz])
    · change f.1 y ≠ 0
      intro hz
      exact hy (by simp [h, hz])
  have hinner (z : LocalVectors p) :
      (∫ y, h z y ∂μ) =
        cut z * (localPhase p ((b : ℚ_[p.val]) * quad a z) * g.1 z *
          localPhase p (polar a z x)) := by
    have hgval : g.1 z = ∫ y, f.1 y * localPhase p (polar a y z) ∂μ := rfl
    rw [hgval]
    calc
      _ = (cut z * localPhase p ((b : ℚ_[p.val]) * quad a z) *
          localPhase p (polar a z x)) *
          ∫ y, f.1 y * localPhase p (polar a y z) ∂μ := by
        rw [← integral_const_mul]
        congr 1
        funext y
        unfold h phase
        rw [← polar_merge a p, localPhase_add, localPhase_add]
        ring
      _ = _ := by ring
  have hcutoff :
      (fourier a p (upperUnipotent a p b g)).1 x = ∫ z, (∫ y, h z y ∂μ) ∂μ := by
    rw [Metaplectic.fourier_apply, localFourier]
    apply integral_congr_ae
    filter_upwards with z
    rw [hinner]
    change localPhase p ((b : ℚ_[p.val]) * quad a z) * g.1 z *
      localPhase p (polar a z x) = _
    by_cases hz : z ∈ K
    · simp [cut, hz]
    · have hzero : g.1 z = 0 := by
        by_contra hne
        exact hz (hg (subset_tsupport _ hne))
      simp [hzero]
  have hgaussian (y : LocalVectors p) :
      (dilationFactor p b : ℂ) * (∫ z, h z y ∂μ) =
        (scaledIndex a p b : ℂ) * (f.1 y * localPhase p (-B * quad a (x + y))) := by
    by_cases hy : y ∈ tsupport f.1
    · have hstation : B • (x + y) ∈ vectorCutoff p N := hshiftN ⟨y, hy, rfl⟩
      have hi : (∫ z, h z y ∂μ) = f.1 y * gaussianCutoff p a b (x + y) N := by
        unfold gaussianCutoff
        rw [← integral_indicator hkopen.measurableSet, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : z ∈ K <;> simp [h, cut, phase, hz]
      rw [hi, mul_left_comm, hgauss (x + y) hstation, mul_left_comm]
    · have hf : f.1 y = 0 := by
        by_contra hne
        exact hy (subset_tsupport _ hne)
      simp [h, hf]
  change (dilationFactor p b : ℂ) * (fourier a p (upperUnipotent a p b g)).1 x = _
  rw [hcutoff, integral_integral_swap_of_hasCompactSupport hcont hcompact, ← integral_const_mul,
    ← integral_const_mul]
  exact integral_congr_ae (.of_forall hgaussian)

omit [∀ i, NeZero (2 * a i)] in
private theorem factored_phase (b : ℚ_[p.val]) (x y : LocalVectors p) :
    b * quad a (x + y) = b * quad a x + b * quad a y + polar a y (b • x) := by
  simp only [quad, polar, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The factored version of the Weyl sandwich before dividing by the
nonzero norm factor. Its last Fourier argument is that of the inverse transform. -/
theorem fourier_upper_sandwich (b : ℚ_[p.val]ˣ) (f : SchwartzBruhat p) (x : LocalVectors p) :
    (dilationFactor p b : ℂ) *
      (fourier a p (upperUnipotent a p b (fourier a p f))).1 x =
      (scaledIndex a p b : ℂ) *
        (localPhase p (-(↑(b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val]) * quad a x) *
          (fourier a p (upperUnipotent a p (-(↑(b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val])) f)).1
            ((-(↑(b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val])) • x)) := by
  let c : ℚ_[p.val] := -(↑(b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val])
  rw [fourier_upper_kernel]
  change (scaledIndex a p b : ℂ) * (∫ y, f.1 y * localPhase p (c * quad a (x + y))
    ∂localHaar a p) = (scaledIndex a p b : ℂ) *
      (localPhase p (c * quad a x) * (fourier a p (upperUnipotent a p c f)).1 (c • x))
  rw [Metaplectic.fourier_apply, localFourier]
  apply congrArg ((scaledIndex a p b : ℂ) * ·)
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  change f.1 y * localPhase p (c * quad a (x + y)) = localPhase p (c * quad a x) *
    ((localPhase p (c * quad a y) * f.1 y) * localPhase p (polar a y (c • x)))
  rw [factored_phase a p, localPhase_add, localPhase_add]
  ring


end ZInQ.Manuscript.RC.Metaplectic2
