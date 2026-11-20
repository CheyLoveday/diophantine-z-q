import ZInQKernel.Contrib.OneProof.RC.Metaplectic.Functions
import ZInQKernel.Contrib.OneProof.RC.WeilIndex.ResidueHaar

/-! Local Fourier inversion in the Haar convention of tex 8646–8653.
The rectangle computation and span argument for inversion are on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic

open Intertwine Intertwine2 WeilIndex MeasureTheory MeasureTheory.Measure Set
open scoped BigOperators ENNReal

variable (a : Fin 3 → ℕ) (p : Place)

local instance : IsFiniteMeasureOnCompacts (localHaar a p) := by
  unfold localHaar
  exact IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top

private theorem phase_polar (y : LocalVectors p) :
    IsLocallyConstant (fun x : LocalVectors p => localPhase p (polar a x y)) :=
  (isLocallyConstant_phase p).comp_continuous
    ((continuous_polar p a).comp (continuous_id.prodMk continuous_const))

private theorem integrable_kernel {f : LocalVectors p → ℂ} (hf : f ∈ schwartzBruhat p)
    (y : LocalVectors p) :
    Integrable (fun x => f x * localPhase p (polar a x y)) (localHaar a p) :=
  (hf.1.mul (phase_polar a p y)).continuous.integrable_of_hasCompactSupport hf.2.mul_right

private theorem fourier_add {f g : LocalVectors p → ℂ} (hf : f ∈ schwartzBruhat p)
    (hg : g ∈ schwartzBruhat p) :
    localFourier a p (f + g) = localFourier a p f + localFourier a p g := by
  funext y
  simp only [localFourier, Pi.add_apply, add_mul]
  exact integral_add (integrable_kernel a p hf y) (integrable_kernel a p hg y)

private theorem fourier_smul (z : ℂ) (f : LocalVectors p → ℂ) :
    localFourier a p (z • f) = z • localFourier a p f := by
  funext y
  simp only [localFourier, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

private theorem padicHaar_scaled_real (s : ℚ_[p.val]ˣ) :
    (padicHaar p).real (scaledLattice p s : Set ℚ_[p.val]) = ‖(s : ℚ_[p.val])‖⁻¹ := by
  let q : ℚ_[p.val] := p.val
  have hq : q ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  have hval : (q ^ (s : ℚ_[p.val]).valuation).valuation = (s : ℚ_[p.val]).valuation := by
    rw [Padic.valuation_zpow, show q.valuation = 1 from Padic.valuation_p, mul_one]
  have hline : lineHaar p (2 : ℚ_[p.val])⁻¹ = padicHaar p := by
    simp [lineHaar]
  have h := lineHaar_scaledLattice_zpow p (2 : ℚ_[p.val])⁻¹ (s : ℚ_[p.val]).valuation
  rw [hline, mul_inv_cancel₀ (by norm_num : (2 : ℚ_[p.val]) ≠ 0), norm_one,
    Real.sqrt_one, mul_one] at h
  rw [scaledLattice_eq_of_valuation p _ _ s.ne_zero (zpow_ne_zero _ hq) hval.symm]
  rw [h, Padic.norm_eq_zpow_neg_valuation s.ne_zero, zpow_neg, inv_inv]

theorem rectangle_volume (s : Fin 3 → ℚ_[p.val]ˣ) :
    (localHaar a p).real (rectangle p s : Set (LocalVectors p)) =
      Real.sqrt (localNorm (determinant a) p) * ∏ i, ‖(s i : ℚ_[p.val])‖⁻¹ := by
  simp only [measureReal_def, localHaar, Measure.smul_apply, smul_eq_mul]
  rw [show (rectangle p s : Set (LocalVectors p)) =
    univ.pi (fun i => (scaledLattice p (s i) : Set ℚ_[p.val])) from rfl, Measure.pi_pi,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ENNReal.toReal_prod]
  simp only [← measureReal_def, padicHaar_scaled_real]

variable [∀ i, NeZero (2 * a i)]

def gramUnit (i : Fin 3) : ℚ_[p.val]ˣ :=
  Units.mk0 ((2 * a i : ℕ) : ℚ_[p.val]) (Nat.cast_ne_zero.mpr (NeZero.ne _))

def dualScale (s : Fin 3 → ℚ_[p.val]ˣ) (i : Fin 3) : ℚ_[p.val]ˣ :=
  gramUnit a p i / s i

theorem dualScale_dualScale (s : Fin 3 → ℚ_[p.val]ˣ) :
    dualScale a p (dualScale a p s) = s := by
  funext i
  exact div_div_cancel _ _

/-- For the conductor-(mathbb Z_p) character, the polar annihilator is the indicated rectangle. -/
theorem rectangle_annihilator (s : Fin 3 → ℚ_[p.val]ˣ) (y : LocalVectors p) :
    (∀ t ∈ rectangle p s, localPhase p (polar a t y) = 1) ↔
      y ∈ rectangle p (dualScale a p s) := by
  classical
  rw [mem_rectangle]
  constructor
  · intro h i
    let t : LocalVectors p := Pi.single i (s i : ℚ_[p.val])⁻¹
    have ht : t ∈ rectangle p s := (mem_rectangle p s t).2 fun j => by
      by_cases hj : j = i
      · subst j
        simp [t]
      · simp [t, hj]
    have he : polar a t y = (dualScale a p s i : ℚ_[p.val]) * y i := by
      unfold polar
      rw [Finset.sum_eq_single i]
      · simp [t, dualScale, gramUnit, div_eq_mul_inv]
      · intro j _ hj
        simp [t, hj]
      · simp
    rw [← he]
    exact (localPhase_eq_one p _).mp (h t ht)
  · intro h t ht
    apply (localPhase_eq_one p _).mpr
    apply (PadicInt.subring p.val).sum_mem
    intro i _
    have harg : ((2 * a i : ℕ) : ℚ_[p.val]) * t i * y i =
        ((s i : ℚ_[p.val]) * t i) * ((dualScale a p s i : ℚ_[p.val]) * y i) := by
      simp only [dualScale, gramUnit, Units.val_div_eq_div_val, Units.val_mk0]
      field_simp [(s i).ne_zero]
    rw [harg]
    exact (PadicInt.subring p.val).mul_mem ((mem_rectangle p s t).1 ht i) (h i)

theorem rectangle_volume_mul_dual (s : Fin 3 → ℚ_[p.val]ˣ) :
    (localHaar a p).real (rectangle p s : Set _) *
      (localHaar a p).real (rectangle p (dualScale a p s) : Set _) = 1 := by
  have hn : 0 ≤ localNorm (determinant a) p := norm_nonneg _
  rw [rectangle_volume, rectangle_volume, mul_mul_mul_comm, ← sq,
    Real.sq_sqrt hn, ← Finset.prod_mul_distrib]
  have hnorm : localNorm (determinant a) p = ∏ i, ‖(gramUnit a p i : ℚ_[p.val])‖ := by
    simp [localNorm, determinant, Nat.cast_prod, norm_prod, gramUnit]
  rw [hnorm, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  rw [← mul_inv]
  have h : (s i : ℚ_[p.val]) * (dualScale a p s i : ℚ_[p.val]) = gramUnit a p i := by
    simp [dualScale, Units.val_div_eq_div_val, mul_div_cancel₀ _ (s i).ne_zero]
  rw [← norm_mul, h, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (gramUnit a p i).ne_zero)]

omit [∀ i, NeZero (2 * a i)] in
private theorem polar_comm (x y : LocalVectors p) : polar a x y = polar a y x := by
  unfold polar
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Fourier transform of a rectangular coset: its mass times the center character on the dual. -/
theorem fourier_rectangle (s : Fin 3 → ℚ_[p.val]ˣ) (c : LocalVectors p) :
    localFourier a p (rectangleIndicator p s c) =
      fun y => ((localHaar a p).real (rectangle p s : Set _) : ℂ) *
        (localPhase p (polar a c y) * rectangleIndicator p (dualScale a p s) 0 y) := by
  classical
  funext y
  let L := rectangle p s
  let f : LocalVectors p → ℂ := (L : Set _).indicator (fun x => localPhase p (polar a x y))
  have hshift : localFourier a p (rectangleIndicator p s c) y =
      localPhase p (polar a c y) * ∫ x, f x ∂localHaar a p := by
    unfold localFourier
    rw [← integral_add_left_eq_self (μ := localHaar a p)
      (fun x => rectangleIndicator p s c x * localPhase p (polar a x y)) c, ← integral_const_mul]
    congr 1
    funext x
    by_cases hx : x ∈ L <;>
      simp [rectangleIndicator, rectangleCoset, f, L, hx, polar_add, localPhase_add]
  rw [hshift]
  by_cases hy : y ∈ rectangle p (dualScale a p s)
  · have hf : f = (L : Set _).indicator (fun _ => 1) := by
      funext x
      by_cases hx : x ∈ L
      · simp [f, hx, (rectangle_annihilator a p s y).2 hy x hx]
      · simp [f, hx]
    rw [hf, integral_indicator_const _ (rectangle_open p s).measurableSet,
      RCLike.real_smul_eq_coe_mul, mul_one]
    simp [rectangleIndicator, rectangleCoset, hy, mul_comm]
  · have hn := mt (rectangle_annihilator a p s y).1 hy
    push Not at hn
    obtain ⟨t, ht, hn⟩ := hn
    have he (x : LocalVectors p) : f (t + x) = localPhase p (polar a t y) * f x := by
      have hm : t + x ∈ L ↔ x ∈ L := L.add_mem_cancel_left ht
      by_cases hx : x ∈ L <;> simp [f, hm, hx, polar_add, localPhase_add]
    have hh := integral_add_left_eq_self (μ := localHaar a p) f t
    simp_rw [he, integral_const_mul] at hh
    have hz : (∫ x, f x ∂localHaar a p) = 0 := by
      by_contra hc
      exact hn (mul_right_cancel₀ hc (hh.trans (one_mul _).symm))
    simp [hz, rectangleIndicator, rectangleCoset, hy]

omit [∀ i, NeZero (2 * a i)] in
private theorem fourier_modulate (f : LocalVectors p → ℂ) (c y : LocalVectors p) :
    localFourier a p (fun x => localPhase p (polar a c x) * f x) y =
      localFourier a p f (y + c) := by
  unfold localFourier
  congr 1
  funext x
  rw [polar_comm a p x (y + c), polar_add, localPhase_add, polar_comm a p y x]
  ring

private theorem fourier_rectangle_sq (s : Fin 3 → ℚ_[p.val]ˣ) (c y : LocalVectors p) :
    localFourier a p (localFourier a p (rectangleIndicator p s c)) y =
      rectangleIndicator p s c (-y) := by
  rw [fourier_rectangle a p s c]
  change localFourier a p (((localHaar a p).real (rectangle p s : Set _) : ℂ) •
    (fun x => localPhase p (polar a c x) * rectangleIndicator p (dualScale a p s) 0 x)) y = _
  rw [fourier_smul, Pi.smul_apply, smul_eq_mul, fourier_modulate,
    fourier_rectangle, dualScale_dualScale]
  have hzero : polar a (0 : LocalVectors p) (y + c) = 0 := by simp [polar]
  have hone : localPhase p 0 = 1 := (localPhase_eq_one p 0).2 (zero_mem _)
  simp only [hzero, hone, one_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, rectangle_volume_mul_dual,
    Complex.ofReal_one, one_mul]
  have hm : y + c ∈ rectangle p s ↔ -y - c ∈ rectangle p s := by
    rw [sub_eq_add_neg, ← neg_add]
    exact ((rectangle p s).neg_mem_iff).symm
  by_cases hy : y + c ∈ rectangle p s
  · simp [rectangleIndicator, rectangleCoset, hy, hm.mp hy]
  · simp [rectangleIndicator, rectangleCoset, hy, mt hm.mpr hy]

/-- The Haar Fourier transform preserves Schwartz–Bruhat functions and squares to reflection. -/
theorem fourier_mem_and_sq {f : LocalVectors p → ℂ} (hf : f ∈ schwartzBruhat p) :
    localFourier a p f ∈ schwartzBruhat p ∧
      ∀ y, localFourier a p (localFourier a p f) y = f (-y) := by
  have hm := mem_span_rectangles p hf
  suffices h : f ∈ schwartzBruhat p ∧ localFourier a p f ∈ schwartzBruhat p ∧
      ∀ y, localFourier a p (localFourier a p f) y = f (-y) from h.2
  clear hf
  induction hm using Submodule.span_induction with
  | mem b hb =>
      obtain ⟨s, c, rfl⟩ := hb
      refine ⟨rectangleIndicator_mem p s c, ?_, fourier_rectangle_sq a p s c⟩
      rw [fourier_rectangle a p]
      refine (schwartzBruhat p).smul_mem _ ⟨?_, ?_⟩
      · have hc : IsLocallyConstant (fun y => localPhase p (polar a c y)) := by
          simpa only [polar_comm a p c] using phase_polar a p c
        exact hc.mul (rectangleIndicator_mem p (dualScale a p s) 0).1
      · exact (rectangleIndicator_mem p (dualScale a p s) 0).2.mul_left
  | zero =>
      have hz : localFourier a p 0 = 0 := by ext y; simp [localFourier]
      simp [hz]
  | add f g _ _ hf hg =>
      rw [fourier_add a p hf.1 hg.1, fourier_add a p hf.2.1 hg.2.1]
      exact ⟨(schwartzBruhat p).add_mem hf.1 hg.1,
        (schwartzBruhat p).add_mem hf.2.1 hg.2.1,
        fun y => congrArg₂ (· + ·) (hf.2.2 y) (hg.2.2 y)⟩
  | smul z f _ hf =>
      rw [fourier_smul, fourier_smul]
      exact ⟨(schwartzBruhat p).smul_mem _ hf.1, (schwartzBruhat p).smul_mem _ hf.2.1,
        fun y => congrArg (z • ·) (hf.2.2 y)⟩

def fourier : SchwartzBruhat p →ₗ[ℂ] SchwartzBruhat p where
  toFun f := ⟨localFourier a p f, (fourier_mem_and_sq a p f.2).1⟩
  map_add' f g := Subtype.ext (fourier_add a p f.2 g.2)
  map_smul' z f := Subtype.ext (fourier_smul a p z f)

theorem fourier_apply (f : SchwartzBruhat p) (y : LocalVectors p) :
    (fourier a p f : LocalVectors p → ℂ) y = localFourier a p f y := rfl

theorem fourier_sq (f : SchwartzBruhat p) (y : LocalVectors p) :
    (fourier a p (fourier a p f) : LocalVectors p → ℂ) y = f.1 (-y) :=
  (fourier_mem_and_sq a p f.2).2 y

#print axioms phase_polar
#print axioms integrable_kernel
#print axioms fourier_add
#print axioms fourier_smul
#print axioms padicHaar_scaled_real
#print axioms rectangle_volume
#print axioms dualScale_dualScale
#print axioms rectangle_annihilator
#print axioms rectangle_volume_mul_dual
#print axioms polar_comm
#print axioms fourier_rectangle
#print axioms fourier_modulate
#print axioms fourier_rectangle_sq
#print axioms fourier_mem_and_sq
#print axioms fourier_apply
#print axioms fourier_sq

end ZInQ.Manuscript.RC.Metaplectic
