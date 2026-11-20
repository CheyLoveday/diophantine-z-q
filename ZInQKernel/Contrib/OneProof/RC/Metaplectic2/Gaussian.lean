import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Relations
import Mathlib.MeasureTheory.Integral.Pi

/-! The ternary oscillatory integral in tex 8746–8753, using actual
cutoffs and the scalar Gaussian integral. The product and uniform
cutoff arguments are on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic WeilIndex MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal BigOperators

variable (p : Place)

def primeUnit : ℚ_[p.val]ˣ :=
  Units.mk0 (p.val : ℚ_[p.val]) (Nat.cast_ne_zero.mpr p.property.ne_zero)

/-- The product of the three scalar cutoffs. -/
def vectorCutoff (N : ℕ) : AddSubgroup (LocalVectors p) :=
  rectangle p (fun _ => primeUnit p ^ N)

theorem mem_vectorCutoff (N : ℕ) (x : LocalVectors p) :
    x ∈ vectorCutoff p N ↔ ∀ i, x i ∈ cutoffLattice p N := by
  rw [vectorCutoff, mem_rectangle]
  rfl

private theorem cutoff_mono : Monotone (vectorCutoff p) := by
  intro N M h x hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [mem_vectorCutoff] at hx ⊢
  intro i
  change (p.val : ℚ_[p.val]) ^ (N + k) * x i ∈ PadicInt.subring p.val
  have hk : (p.val : ℚ_[p.val]) ^ k ∈ PadicInt.subring p.val :=
    (PadicInt.subring p.val).pow_mem (natCast_mem _ _) _
  rw [add_comm N, pow_add, mul_assoc]
  exact (PadicInt.subring p.val).mul_mem hk (hx i)

theorem eventually_vectorCutoff {K : Set (LocalVectors p)} (hK : IsCompact K) :
    ∀ᶠ N : ℕ in atTop, K ⊆ vectorCutoff p N := by
  classical
  have hcover : K ⊆ ⋃ N, (vectorCutoff p N : Set (LocalVectors p)) := by
    intro x _
    obtain ⟨N, hN⟩ := (Filter.eventually_all.mpr fun i : Fin 3 =>
      eventually_cutoffLattice p (x i)).exists
    exact mem_iUnion.mpr ⟨N, (mem_vectorCutoff p N x).2 hN⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun N => (vectorCutoff p N : Set (LocalVectors p))) (fun N => rectangle_open p _) hcover
  refine eventually_atTop.2 ⟨s.sup id, fun N hN x hx => ?_⟩
  have hx' := hs hx
  simp only [mem_iUnion] at hx'
  obtain ⟨k, hk, h⟩ := hx'
  exact cutoff_mono p ((Finset.le_sup (f := id) hk).trans hN) h

variable (a : Fin 3 → ℕ) [∀ i, NeZero (2 * a i)]

theorem phase_sum {I : Type*} (s : Finset I) (f : I → ℚ_[p.val]) :
    localPhase p (∑ i ∈ s, f i) = ∏ i ∈ s, localPhase p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (localPhase_eq_one p 0).2 (zero_mem (PadicInt.subring p.val))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, localPhase_add, ih]

/-- Ternary cutoff in the Haar measure for Q, retaining b in the phase. -/
def gaussianCutoff (b : ℚ_[p.val]ˣ) (v : LocalVectors p) (N : ℕ) : ℂ :=
  ∫ z in (vectorCutoff p N : Set (LocalVectors p)),
    localPhase p ((b : ℚ_[p.val]) * quad a z + polar a z v) ∂localHaar a p

private theorem cutoff_product (b : ℚ_[p.val]ˣ) (v : LocalVectors p) (N : ℕ) :
    (dilationFactor p b : ℂ) * gaussianCutoff p a b v N =
      ∏ i, cutoffGaussian p (b * localCoefficient a p i)
        ((↑(b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val]) * v i) N := by
  let h (i : Fin 3) (z : ℚ_[p.val]) :=
    localPhase p ((b : ℚ_[p.val]) * (a i : ℚ_[p.val]) * z ^ 2 +
      ((2 * a i : ℕ) : ℚ_[p.val]) * z * v i)
  have harg (z : LocalVectors p) :
      localPhase p ((b : ℚ_[p.val]) * quad a z + polar a z v) = ∏ i, h i (z i) := by
    simp only [h, quad, polar, Finset.mul_sum, mul_assoc, ← Finset.sum_add_distrib, phase_sum]
  have hset : (vectorCutoff p N : Set (LocalVectors p)) =
      univ.pi (fun _ : Fin 3 => (cutoffLattice p N : Set ℚ_[p.val])) := by
    ext x
    simp [mem_vectorCutoff]
  unfold gaussianCutoff
  simp_rw [harg]
  rw [localHaar, hset, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), RCLike.real_smul_eq_coe_mul,
    restrict_pi_pi, integral_fintype_prod_eq_prod]
  have hi (i : Fin 3) :
      cutoffGaussian p (b * localCoefficient a p i)
          ((↑(b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val]) * v i) N =
        (Real.sqrt ‖(b : ℚ_[p.val]) * ((2 * a i : ℕ) : ℚ_[p.val])‖ : ℂ) *
          ∫ z in (cutoffLattice p N : Set ℚ_[p.val]), h i z ∂padicHaar p := by
    have he (z : ℚ_[p.val]) : h i z =
        localPhase p (((b * localCoefficient a p i : ℚ_[p.val]ˣ) : ℚ_[p.val]) * z ^ 2 +
          2 * ((b * localCoefficient a p i : ℚ_[p.val]ˣ) : ℚ_[p.val]) * z *
          ((↑(b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val]) * v i)) := by
      unfold h
      congr 1
      simp only [Units.val_mul, localCoefficient_val, Nat.cast_mul, Nat.cast_ofNat,
        Units.val_inv_eq_inv_val]
      field_simp [b.ne_zero]
      <;> ring
    have hb : 2 * ((b * localCoefficient a p i : ℚ_[p.val]ˣ) : ℚ_[p.val]) =
        (b : ℚ_[p.val]) * ((2 * a i : ℕ) : ℚ_[p.val]) := by
      simp only [Units.val_mul, localCoefficient_val, Nat.cast_mul, Nat.cast_ofNat]
      ring
    simp only [Units.val_mul] at he hb
    unfold cutoffGaussian
    simp_rw [← he]
    simp only [lineHaar, hb, Measure.restrict_smul, integral_smul_measure,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _), RCLike.real_smul_eq_coe_mul]
    rfl
  simp_rw [hi, Finset.prod_mul_distrib, norm_mul, Real.sqrt_mul (norm_nonneg (b : ℚ_[p.val])),
    Complex.ofReal_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Complex.ofReal_pow, ← mul_assoc, ← Complex.ofReal_prod, ← Real.sqrt_prod Finset.univ (fun _ _ => norm_nonneg _)]
  simp [dilationFactor, determinant, localNorm, Nat.cast_prod, norm_prod]

/-- For all sufficiently large cutoffs the oscillatory formula has
exactly the local-index scalar in tex 8751; the bound can be chosen
uniformly once the stationary shift belongs to the cutoff. -/
theorem gaussianCutoff_eventually (b : ℚ_[p.val]ˣ) :
    ∀ᶠ N : ℕ in atTop, ∀ v : LocalVectors p,
      (↑(b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val]) • v ∈ vectorCutoff p N →
      (dilationFactor p b : ℂ) * gaussianCutoff p a b v N =
        (scaledIndex a p b : ℂ) * localPhase p (-(↑(b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val]) * quad a v) := by
  have h0 (i : Fin 3) : ∀ᶠ N : ℕ in atTop,
      cutoffGaussian p (b * localCoefficient a p i) 0 N =
        (gaussGamma p (b * localCoefficient a p i) : ℂ) := by
    simpa [(localPhase_eq_one p 0).2 (zero_mem (PadicInt.subring p.val))] using
      eventually_cutoffGaussian_gaussGamma p (b * localCoefficient a p i) 0
  filter_upwards [Filter.eventually_all.mpr h0] with N hN v hv
  rw [cutoff_product]
  have hi (i : Fin 3) : cutoffGaussian p (b * localCoefficient a p i)
          ((↑(b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val]) * v i) N =
        (gaussGamma p (b * localCoefficient a p i) : ℂ) *
          localPhase p (-(↑(b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val]) * (a i : ℚ_[p.val]) * v i ^ 2) := by
    have hz := integral_completeSquare p (b * localCoefficient a p i)
      ((↑(b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val]) * v i) (cutoffLattice p N)
      (cutoffLattice_measurable p N) ((mem_vectorCutoff p N _).1 hv i)
    have he : -((b : ℚ_[p.val]) * (localCoefficient a p i : ℚ_[p.val]) *
          ((↑(b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val]) * v i) ^ 2) =
        -(↑(b⁻¹ : ℚ_[p.val]ˣ) : ℚ_[p.val]) * (a i : ℚ_[p.val]) * v i ^ 2 := by
      simp only [Units.val_inv_eq_inv_val, localCoefficient_val]
      field_simp [b.ne_zero]
    have hz₀ :
        (∫ z in (cutoffLattice p N : Set ℚ_[p.val]),
          localPhase p ((b : ℚ_[p.val]) * (localCoefficient a p i : ℚ_[p.val]) * z ^ 2)
            ∂lineHaar p (b * localCoefficient a p i)) =
          (gaussGamma p (b * localCoefficient a p i) : ℂ) := by
      simpa only [cutoffGaussian, Units.val_mul, mul_zero, add_zero] using hN i
    rw [cutoffGaussian, hz, he, hz₀, mul_comm]
  simp_rw [hi, Finset.prod_mul_distrib, scaledIndex, Units.coe_prod]
  congr 1
  simp only [quad, Finset.mul_sum, ← mul_assoc, phase_sum]


end ZInQ.Manuscript.RC.Metaplectic2
