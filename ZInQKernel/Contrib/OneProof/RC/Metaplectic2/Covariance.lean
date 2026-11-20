import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Relations
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Fourier covariance under scalar dilation, tex 8735 and 8778.
The Haar change of variables is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal BigOperators

variable (a : Fin 3 → ℕ) (p : Place) [∀ i, NeZero (2 * a i)]

private theorem localHaar_isHaar : (localHaar a p).IsAddHaarMeasure := by
  unfold localHaar
  refine IsAddHaarMeasure.smul _ ?_ ENNReal.ofReal_ne_top
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  apply Real.sqrt_pos.2
  exact norm_pos_iff.mpr (Nat.cast_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (2 * a i)))

private def dilHomeo (t : ℚ_[p.val]ˣ) : LocalVectors p ≃ₜ LocalVectors p :=
  Homeomorph.smulOfNeZero (t : ℚ_[p.val]) t.ne_zero

private theorem haar_map_dilate (t : ℚ_[p.val]ˣ) :
    (localHaar a p).map (dilHomeo p t) =
      ENNReal.ofReal (‖(t : ℚ_[p.val])‖⁻¹ ^ 3) • localHaar a p := by
  let μ := localHaar a p
  let e := dilHomeo p t
  let E : LocalVectors p ≃+ LocalVectors p :=
    { e.toEquiv with map_add' := fun x y => smul_add (t : ℚ_[p.val]) x y }
  let : μ.IsAddHaarMeasure := localHaar_isHaar a p
  have : (μ.map e).IsAddHaarMeasure :=
    E.isAddHaarMeasure_map μ e.continuous e.symm.continuous
  obtain h := isAddLeftInvariant_eq_smul (μ.map e) μ
  change μ.map e = _
  rw [h]
  congr 1
  let K : Set (LocalVectors p) := rectangle p 1
  have hKopen : IsOpen K := rectangle_open p 1
  have hpre : e ⁻¹' K = (rectangle p (fun _ => t) : Set (LocalVectors p)) := by
    ext x
    change (t : ℚ_[p.val]) • x ∈ rectangle p 1 ↔ x ∈ rectangle p (fun _ => t)
    simp only [mem_rectangle, Pi.one_apply, Units.val_one, one_mul, Pi.smul_apply, smul_eq_mul]
  have hK : μ.real K = Real.sqrt (localNorm (determinant a) p) := by
    simpa [μ, K] using rectangle_volume a p (1 : Fin 3 → ℚ_[p.val]ˣ)
  have hmap : (μ.map e).real K =
      Real.sqrt (localNorm (determinant a) p) * ‖(t : ℚ_[p.val])‖⁻¹ ^ 3 := by
    rw [measureReal_def, Measure.map_apply e.continuous.measurable hKopen.measurableSet, hpre,
      ← measureReal_def, rectangle_volume, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  conv_lhs at hmap => rw [h, measureReal_def, Measure.smul_apply, Measure.nnreal_smul_coe_apply,
    ENNReal.toReal_mul, ENNReal.coe_toReal, ← measureReal_def, hK]
  have hpos : 0 < Real.sqrt (localNorm (determinant a) p) := by
    apply Real.sqrt_pos.2
    exact norm_pos_iff.mpr (Nat.cast_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (2 * a i)))
  have hr := mul_right_cancel₀ hpos.ne' (hmap.trans (mul_comm _ _))
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (by positivity), hr]

omit [∀ i, NeZero (2 * a i)] in
private theorem polar_scale_right_left (t : ℚ_[p.val]) (x y : LocalVectors p) :
    polar a (t • x) y = polar a x (t • y) := by
  simp only [polar, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => by ring)

private theorem dilationFactor_jacobian (t : ℚ_[p.val]ˣ) :
    dilationFactor p t * ‖(t : ℚ_[p.val])‖⁻¹ ^ 3 = dilationFactor p t⁻¹ := by
  have h : Real.sqrt ‖(t : ℚ_[p.val])‖ ≠ 0 :=
    (Real.sqrt_pos.2 (norm_pos_iff.mpr t.ne_zero)).ne'
  rw [dilationFactor, dilationFactor, Units.val_inv_eq_inv_val, norm_inv, Real.sqrt_inv,
    ← mul_pow]
  congr 1
  have hn := Real.sq_sqrt (norm_nonneg (t : ℚ_[p.val]))
  calc
    Real.sqrt ‖(t : ℚ_[p.val])‖ * ‖(t : ℚ_[p.val])‖⁻¹ =
        Real.sqrt ‖(t : ℚ_[p.val])‖ * (Real.sqrt ‖(t : ℚ_[p.val])‖ ^ 2)⁻¹ := by rw [hn]
    _ = (Real.sqrt ‖(t : ℚ_[p.val])‖)⁻¹ := by
      rw [pow_two, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ h, one_mul]

theorem fourier_dilation (t : ℚ_[p.val]ˣ) :
    fourier a p * dilation p t = dilation p t⁻¹ * fourier a p := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext y
  let e := dilHomeo p t
  let g : LocalVectors p → ℂ :=
    fun z => f.1 z * localPhase p (polar a z (((t⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val]) • y))
  have hid (x : LocalVectors p) : (↑(t⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val]) • e x = x := by
    change (↑(t⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val]) • ((t : ℚ_[p.val]) • x) = x
    simp [smul_smul]
  have hkernel (x : LocalVectors p) :
      g (e x) = f.1 ((t : ℚ_[p.val]) • x) * localPhase p (polar a x y) := by
    dsimp [g]
    rw [← polar_scale_right_left a p, hid]
    rfl
  change (fourier a p (dilation p t f)).1 y = (dilation p t⁻¹ (fourier a p f)).1 y
  rw [dilation_apply, Metaplectic.fourier_apply, Metaplectic.fourier_apply]
  unfold localFourier
  simp_rw [dilation_apply, mul_assoc, ← hkernel, integral_const_mul]
  have hc : (∫ x, g (e x) ∂localHaar a p) = ∫ x, g x ∂(localHaar a p).map e :=
    (integral_map_equiv (μ := localHaar a p) e.toMeasurableEquiv g).symm
  have hD : (dilationFactor p t : ℂ) * ((‖(t : ℚ_[p.val])‖⁻¹ ^ 3 : ℝ) : ℂ) =
      (dilationFactor p t⁻¹ : ℂ) := by exact_mod_cast dilationFactor_jacobian p t
  change (dilationFactor p t : ℂ) * (∫ x, g (e x) ∂localHaar a p) =
    (dilationFactor p t⁻¹ : ℂ) * (∫ x, g x ∂localHaar a p)
  rw [hc, haar_map_dilate, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    RCLike.real_smul_eq_coe_mul, ← mul_assoc]
  exact congrArg (fun z : ℂ => z * ∫ x, g x ∂localHaar a p) hD

/-- The full index-normalized Weyl and diagonal covariance. -/
theorem weyl_diagonal (t : ℚ_[p.val]ˣ) :
    Metaplectic.weyl a p * diagonal a p t = diagonal a p t⁻¹ * Metaplectic.weyl a p := by
  have hr : diagonalRatio a p t⁻¹ = diagonalRatio a p t := by
    simp only [diagonalRatio, scaledIndex_inv]
  simp only [Metaplectic.weyl, diagonal, hr, smul_mul_assoc, mul_smul_comm, fourier_dilation, smul_smul]
  rw [mul_comm (gaussIndex a p : ℂ)]


end ZInQ.Manuscript.RC.Metaplectic2
