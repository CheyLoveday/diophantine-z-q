import ZInQKernel.Contrib.OneProof.RC.X0Model.Expansion
import ZInQKernel.Contrib.OneProof.RC.X0Model2.LatticeRigidity
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_jLattice_ofTau
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_discriminant_ne_zero
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_E4_cube_div_discriminant_smul
import Mathlib.LinearAlgebra.Matrix.Basis

/-! Orbit separation for the analytic j-function, including the elliptic
parameters (tex 2915–2919, on the spot, provenance (c)). -/

noncomputable section

open Module
open scoped MatrixGroups

namespace ZInQ.Manuscript.RC.X0Model2

/-- The analytic j-function is invariant under the full modular group. -/
theorem analyticJ_smul (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    X0Model.analyticJ (γ • τ) = X0Model.analyticJ τ :=
  ModularCurve.E4_cube_div_discriminant_smul γ τ

private theorem exists_invariant_scaling (a b c d : ℂ)
    (hL : a ^ 3 - 27 * b ^ 2 ≠ 0) (hM : c ^ 3 - 27 * d ^ 2 ≠ 0)
    (h : a ^ 3 * d ^ 2 = c ^ 3 * b ^ 2) :
    ∃ u : ℂˣ, (u : ℂ) ^ 4 * c = a ∧ (u : ℂ) ^ 6 * d = b := by
  by_cases hc : c = 0
  · have hd : d ≠ 0 := by intro hd; simp [hc, hd] at hM
    have ha : a = 0 := by simpa [hc, hd] using h
    have hb : b ≠ 0 := by intro hb; simp [ha, hb] at hL
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (b / d) (by decide : 0 < 6)
    have hu0 : u ≠ 0 := by intro e; exact div_ne_zero hb hd (hu.symm.trans (by simp [e]))
    exact ⟨Units.mk0 u hu0, by simp [ha, hc], by simp [hu, hd]⟩
  have ha : a ≠ 0 := by
    intro ha
    have hb : b = 0 := by
      by_contra hb
      exact (mul_ne_zero (pow_ne_zero 3 hc) (pow_ne_zero 2 hb)) (by simpa [ha] using h.symm)
    simp [ha, hb] at hL
  by_cases hd : d = 0
  · have hb : b = 0 := by
      by_contra hb
      exact (mul_ne_zero (pow_ne_zero 3 hc) (pow_ne_zero 2 hb)) (by simpa [hd] using h.symm)
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (a / c) (by decide : 0 < 4)
    have hu0 : u ≠ 0 := by intro e; exact div_ne_zero ha hc (hu.symm.trans (by simp [e]))
    exact ⟨Units.mk0 u hu0, by simp [hu, hc], by simp [hd, hb]⟩
  have hb : b ≠ 0 := by intro hb; simp [hb, ha, hd] at h
  let A := a / c
  let B := b / d
  have hA : A ≠ 0 := div_ne_zero ha hc
  have hB : B ≠ 0 := div_ne_zero hb hd
  have hAB : A ^ 3 = B ^ 2 := by
    dsimp [A, B]
    rw [div_pow, div_pow, div_eq_div_iff (pow_ne_zero _ hc) (pow_ne_zero _ hd)]
    simpa only [mul_comm (c ^ 3)] using h
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (B / A) (by decide : 0 < 2)
  have hu0 : u ≠ 0 := by intro e; exact div_ne_zero hB hA (hu.symm.trans (by simp [e]))
  have hu4 : u ^ 4 = A := calc
    u ^ 4 = (u ^ 2) ^ 2 := by ring
    _ = A := by rw [hu, div_pow, ← hAB]; field_simp
  have hu6 : u ^ 6 = B := by
    rw [show u ^ 6 = u ^ 4 * u ^ 2 by ring, hu4, hu, mul_comm A, div_mul_cancel₀ _ hA]
  exact ⟨Units.mk0 u hu0, by simp [hu4, A, hc], by simp [hu6, B, hd]⟩

private theorem exists_homothetic_of_jLattice_eq (L M : PeriodPair)
    (h : L.jLattice = M.jLattice) :
    ∃ u : ℂˣ, (L.scale u).lattice = M.lattice := by
  have hL := L.discriminant_ne_zero
  have hM := M.discriminant_ne_zero
  have hab : L.g₂ ^ 3 * M.g₃ ^ 2 = M.g₂ ^ 3 * L.g₃ ^ 2 := by
    rw [PeriodPair.jLattice, PeriodPair.jLattice, div_eq_div_iff hL hM] at h
    linear_combination (-1 / 46656 : ℂ) * h
  obtain ⟨u, h₂, h₃⟩ := exists_invariant_scaling L.g₂ L.g₃ M.g₂ M.g₃ hL hM hab
  refine ⟨u, lattice_eq_of_weierstrass_invariants _ _ ?_ ?_⟩
  · rw [P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair.g₂_scale, ← h₂,
      inv_mul_cancel_left₀ (pow_ne_zero _ u.ne_zero)]
  · rw [P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair.g₃_scale, ← h₃,
      inv_mul_cancel_left₀ (pow_ne_zero _ u.ne_zero)]

private theorem exists_smul_of_lattice_eq (τ σ : UpperHalfPlane) (u : ℂˣ)
    (h : ((PeriodPair.ofTau σ).scale u).lattice = (PeriodPair.ofTau τ).lattice) :
    ∃ γ : SL(2, ℤ), γ • τ = σ := by
  let b := (PeriodPair.ofTau τ).latticeBasis
  let c := ((PeriodPair.ofTau σ).scale u).latticeBasis.map (LinearEquiv.ofEq _ _ h)
  let A := Matrix.transpose (b.toMatrix c)
  have hdet : IsUnit A.det := by
    refine isUnit_iff_exists_inv.mpr ⟨(c.toMatrix b).det, ?_⟩
    change (Matrix.transpose (b.toMatrix c)).det * (c.toMatrix b).det = 1
    rw [Matrix.det_transpose, ← Matrix.det_mul, Basis.toMatrix_mul_toMatrix,
      Basis.toMatrix_self, Matrix.det_one]
  have hcoord (j : Fin 2) : (c j : ℂ) =
      (A j 0 : ℂ) * (τ : ℂ) + (A j 1 : ℂ) := by
    have hh := b.sum_toMatrix_smul_self c j
    rw [Fin.sum_univ_two] at hh
    have hh' := congrArg (fun x : (PeriodPair.ofTau τ).lattice => (x : ℂ)) hh.symm
    simpa only [Submodule.coe_add, Submodule.coe_smul, zsmul_eq_mul, b, A,
      Matrix.transpose_apply, PeriodPair.latticeBasis_zero, PeriodPair.latticeBasis_one,
      PeriodPair.ofTau_ω₁, PeriodPair.ofTau_ω₂, mul_one] using hh'
  have hab : (u : ℂ) * (σ : ℂ) = (A 0 0 : ℂ) * (τ : ℂ) + (A 0 1 : ℂ) := by
    simpa only [c, Basis.map_apply, LinearEquiv.coe_ofEq_apply, PeriodPair.latticeBasis_zero,
      PeriodPair.scale_ω₁, PeriodPair.ofTau_ω₁] using hcoord 0
  have hcd : (u : ℂ) = (A 1 0 : ℂ) * (τ : ℂ) + (A 1 1 : ℂ) := by
    simpa only [c, Basis.map_apply, LinearEquiv.coe_ofEq_apply, PeriodPair.latticeBasis_one,
      PeriodPair.scale_ω₂, PeriodPair.ofTau_ω₂, mul_one] using hcoord 1
  have him : (A.det : ℝ) * τ.im = Complex.normSq (u : ℂ) * σ.im := by
    calc
      _ = (((A 0 0 : ℂ) * (τ : ℂ) + (A 0 1 : ℂ)) *
          star ((A 1 0 : ℂ) * (τ : ℂ) + (A 1 1 : ℂ))).im := by
        simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Complex.mul_im,
          Complex.mul_re, Complex.add_im, Complex.add_re, Complex.intCast_re, Complex.intCast_im,
          Complex.star_def, Complex.conj_re, Complex.conj_im]
        have hτ : τ.im = (τ : ℂ).im := rfl
        rw [hτ]
        ring
      _ = _ := by
        rw [← hab, ← hcd, mul_comm (u : ℂ) (σ : ℂ), mul_assoc, Complex.star_def,
          Complex.mul_conj]
        simp [Complex.mul_im, mul_comm]
  have hpos : 0 ≤ A.det := by
    have hh : 0 < (A.det : ℝ) * τ.im := by rw [him]; exact mul_pos (Complex.normSq_pos.mpr u.ne_zero) σ.im_pos
    exact_mod_cast (pos_of_mul_pos_left hh τ.im_pos.le).le
  have hone : A.det = 1 := by simpa [abs_of_nonneg hpos] using Int.isUnit_iff_abs_eq.mp hdet
  let γ : SL(2, ℤ) := ⟨A, hone⟩
  refine ⟨γ, UpperHalfPlane.ext ?_⟩
  rw [UpperHalfPlane.coe_specialLinearGroup_apply γ τ]
  change ((A 0 0 : ℂ) * (τ : ℂ) + (A 0 1 : ℂ)) /
    ((A 1 0 : ℂ) * (τ : ℂ) + (A 1 1 : ℂ)) = (σ : ℂ)
  rw [← hab, ← hcd, mul_comm (u : ℂ), mul_div_cancel_right₀ _ u.ne_zero]

/-- The fibers of the analytic j-function are exactly the modular group orbits. -/
theorem analyticJ_eq_iff (τ σ : UpperHalfPlane) :
    X0Model.analyticJ τ = X0Model.analyticJ σ ↔ ∃ γ : SL(2, ℤ), γ • τ = σ := by
  constructor
  · intro h
    have hj : (PeriodPair.ofTau σ).jLattice = (PeriodPair.ofTau τ).jLattice := by
      simpa only [PeriodPair.jLattice_ofTau, X0Model.analyticJ] using h.symm
    obtain ⟨u, hu⟩ := exists_homothetic_of_jLattice_eq _ _ hj
    exact exists_smul_of_lattice_eq τ σ u hu
  · rintro ⟨γ, rfl⟩
    exact (analyticJ_smul γ τ).symm

#print axioms analyticJ_smul
#print axioms exists_invariant_scaling
#print axioms exists_homothetic_of_jLattice_eq
#print axioms exists_smul_of_lattice_eq
#print axioms analyticJ_eq_iff

end ZInQ.Manuscript.RC.X0Model2
