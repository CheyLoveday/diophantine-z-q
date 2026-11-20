import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Presentation
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.WeylRelations
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Covariance
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! The projective local action for tex 8772–8795. Quotienting by
nonzero scalar operators is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic WeilIndex Visibility
open scoped MatrixGroups

variable (p : Place) (a : Fin 3 → ℕ)

abbrev LocalEnd := Module.End ℂ (SchwartzBruhat p)

def upperUnit (b : ℚ_[p.val]) : (LocalEnd p)ˣ where
  val := upperUnipotent a p b
  inv := upperUnipotent a p (-b)
  val_inv := by rw [upper_mul, add_neg_cancel, upper_zero]
  inv_val := by rw [upper_mul, neg_add_cancel, upper_zero]

def dilationUnit (t : ℚ_[p.val]ˣ) : (LocalEnd p)ˣ where
  val := dilation p t
  inv := dilation p t⁻¹
  val_inv := by rw [dilation_mul, mul_inv_cancel, dilation_one]
  inv_val := by rw [dilation_mul, inv_mul_cancel, dilation_one]

variable [∀ i, NeZero (2 * a i)]

private theorem fourier_fourth : fourier a p ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, pow_two (fourier a p), fourier_square,
    pow_two, dilation_mul]
  simp [dilation_one]

def fourierUnit : (LocalEnd p)ˣ where
  val := fourier a p
  inv := fourier a p ^ 3
  val_inv := by rw [← pow_succ', fourier_fourth]
  inv_val := by rw [← pow_succ, fourier_fourth]

def diagonalUnit (t : ℚ_[p.val]ˣ) : (LocalEnd p)ˣ :=
  scalarOp (A := LocalEnd p) (diagonalRatio a p t) * dilationUnit p t

def weylUnit : (LocalEnd p)ˣ :=
  scalarOp (A := LocalEnd p) (gaussIndex a p) * fourierUnit p a

omit [∀ i, NeZero (2 * a i)] in
@[simp] theorem coe_upperUnit (b : ℚ_[p.val]) :
    (upperUnit p a b : LocalEnd p) = upperUnipotent a p b := rfl

@[simp] theorem coe_diagonalUnit (t : ℚ_[p.val]ˣ) :
    (diagonalUnit p a t : LocalEnd p) = diagonal a p t := by
  rw [diagonalUnit, coe_scalarOp_mul]
  rfl

@[simp] theorem coe_weylUnit :
    (weylUnit p a : LocalEnd p) = Metaplectic.weyl a p := by
  rw [weylUnit, coe_scalarOp_mul]
  rfl

def scalarSubgroup : Subgroup (LocalEnd p)ˣ :=
  (scalarOp (R := ℂ) (A := LocalEnd p)).range

instance scalarSubgroupNormal : (scalarSubgroup p).Normal where
  conj_mem n hn g := by
    change ∃ z : ℂˣ, scalarOp (A := LocalEnd p) z = n at hn
    obtain ⟨z, rfl⟩ := hn
    refine ⟨z, ?_⟩
    change scalarOp (A := LocalEnd p) z = g * scalarOp (A := LocalEnd p) z * g⁻¹
    calc
      _ = (scalarOp (A := LocalEnd p) z * g) * g⁻¹ := by
        rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = _ := congrArg (fun h : (LocalEnd p)ˣ => h * g⁻¹) (scalarOp_comm (A := LocalEnd p) z g)

/-- Linear automorphisms of the local Schwartz–Bruhat module modulo nonzero scalars. -/
abbrev ProjectiveOperators := (LocalEnd p)ˣ ⧸ scalarSubgroup p

def project : (LocalEnd p)ˣ →* ProjectiveOperators p := QuotientGroup.mk' (scalarSubgroup p)

private theorem project_scalar (z : ℂˣ) :
    project p (scalarOp (A := LocalEnd p) z) = 1 :=
  (QuotientGroup.eq_one_iff _).2 ⟨z, rfl⟩

private theorem project_eq {X Y : (LocalEnd p)ˣ} (z : ℂˣ)
    (h : (X : LocalEnd p) = (z : ℂ) • (Y : LocalEnd p)) :
    project p X = project p Y := by
  have h' : X = scalarOp (A := LocalEnd p) z * Y := by
    apply Units.ext
    rw [coe_scalarOp_mul]
    exact h
  rw [h', map_mul, project_scalar, one_mul]

private theorem operator_relations :
    NormalForm.Relations
      (fun b => project p (upperUnit p a b)) (fun t => project p (diagonalUnit p a t))
      (project p (weylUnit p a)) where
  upper_zero := by
    rw [← map_one (project p)]
    apply congrArg (project p)
    exact Units.ext (upper_zero a p)
  diagonal_one := by
    rw [← map_one (project p)]
    apply congrArg (project p)
    exact Units.ext ((coe_diagonalUnit p a 1).trans (diagonal_one a p))
  upper_add b c := by
    rw [← map_mul]
    apply congrArg (project p)
    exact Units.ext (upper_mul a p b c)
  diagonal_mul s t := by
    rw [← map_mul]
    apply project_eq p (diagonalRatio a p s * diagonalRatio a p t / diagonalRatio a p (s * t))
    simpa only [Units.val_mul, coe_diagonalUnit] using diagonal_mul a p s t
  diagonal_upper t b := by
    rw [← map_mul, ← map_mul]
    apply congrArg (project p)
    apply Units.ext
    simpa only [Units.val_mul, coe_diagonalUnit, coe_upperUnit] using diagonal_upper a p t b
  weyl_diagonal t := by
    rw [← map_mul, ← map_mul]
    apply congrArg (project p)
    apply Units.ext
    simpa only [Units.val_mul, coe_diagonalUnit, coe_weylUnit] using weyl_diagonal a p t
  weyl_square := by
    rw [← map_mul]
    apply project_eq p (gaussIndex a p ^ 2 / diagonalRatio a p (-1))
    simpa only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
      coe_weylUnit, coe_diagonalUnit] using weyl_square_scalar a p
  weyl_upper b := by
    simp only [← map_mul]
    apply project_eq p (gaussIndex a p ^ 2 * scaledIndex a p b / scaledIndex a p (-b⁻¹))
    simpa only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, coe_weylUnit,
      coe_diagonalUnit, coe_upperUnit] using weyl_upper_bruhat a p b

/-- At every finite place, the actual local operators give a
projective representation of SL₂, with the three specified lifts. -/
theorem local_projective_representation :
    ∃ ρ : SL(2, ℚ_[p.val]) →* ProjectiveOperators p,
      (∀ b, ρ (upperMatrix b) = project p (upperUnit p a b)) ∧
      (∀ t, ρ (diagonalMatrix t) = project p (diagonalUnit p a t)) ∧
      ρ weylMatrix = project p (weylUnit p a) :=
  NormalForm.representation_of_relations (operator_relations p a)


end ZInQ.Manuscript.RC.Metaplectic2
