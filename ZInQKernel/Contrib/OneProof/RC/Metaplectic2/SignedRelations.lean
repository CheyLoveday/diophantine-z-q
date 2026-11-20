import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.SignArithmetic
import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.WeylRelations

/-! The three signed defects, tex 8772–8787. We discharge the inherited
one-dimensional index laws by direct arithmetic, provenance (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic Visibility WeilIndex GaussSign

/-- The explicit finite indices satisfy all the rank-one laws needed by the
inherited ternary calculation. No quaternion-norm print is assumed. -/
theorem finiteWeilIndexAxioms (p : Place) : WeilIndexAxioms (gaussGamma p) (hilbertSign p) where
  neg x := by rw [gaussGamma_eq_finiteGamma]; exact
    (congrArg exponentRoot (finiteExponent_neg p x)).trans (exponentRoot_neg _)
  sq x y := by rw [gaussGamma_eq_finiteGamma]; exact finiteGamma_mul_sq p x y
  norm_form x y := by
    simp only [gaussGamma_eq_finiteGamma, gammaDiag, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, finiteGamma, ← exponentRoot_add,
      finiteExponent_neg, hilbertSign]
    congr 1
    have h : finiteExponent p 1 + (-finiteExponent p x +
        (-finiteExponent p y + finiteExponent p (x * y))) = -hilbertExponent p x y := by
      rw [← finiteExponent_defect]
      abel
    exact h.trans (eq_neg_of_add_eq_zero_left (hilbertExponent_double p x y)).symm
  hs_symm x y := congrArg exponentRoot (hilbertExponent_comm p x y)
  hs_mul x y z := by
    unfold hilbertSign
    rw [hilbertExponent_comm p x (y * z), hilbertExponent_mul_left,
      hilbertExponent_comm p y x, hilbertExponent_comm p z x, exponentRoot_add]
  hs_sq x y := by
    unfold hilbertSign
    rw [← exponentRoot_add, hilbertExponent_double, exponentRoot_zero]

variable (a : Fin 3 → ℕ) (p : Place) [∀ i, NeZero (2 * a i)]

private def localDiagonal : List ℚ_[p.val]ˣ := List.ofFn (localCoefficient a p)

private theorem localDiagonal_length : (localDiagonal a p).length = 3 := List.length_ofFn

private theorem scaledIndex_eq_gammaDiag (t : ℚ_[p.val]ˣ) :
    scaledIndex a p t = gammaDiag (gaussGamma p) (scaleForm t (localDiagonal a p)) := by
  simp [scaledIndex, gammaDiag, scaleForm, localDiagonal, Fin.prod_univ_three, mul_assoc]

private theorem gaussIndex_eq_gammaDiag :
    gaussIndex a p = gammaDiag (gaussGamma p) (localDiagonal a p) := by
  rw [← scaledIndex_one a p, scaledIndex_eq_gammaDiag, scaleForm_one]

private theorem diagonalRatio_eq_rQ (t : ℚ_[p.val]ˣ) :
    diagonalRatio a p t = rQ (gaussGamma p) (localDiagonal a p) t := by
  rw [diagonalRatio, scaledIndex_eq_gammaDiag, gaussIndex_eq_gammaDiag, rQ, div_eq_mul_inv]

/-- The diagonal multiplication defect is the local Hilbert sign. -/
theorem diagonal_defect_sign (s t : ℚ_[p.val]ˣ) :
    diagonalRatio a p s * diagonalRatio a p t / diagonalRatio a p (s * t) =
      hilbertSign p s t := by
  simp only [diagonalRatio_eq_rQ]
  rw [rQ_mul (finiteWeilIndexAxioms p) (localDiagonal_length a p), mul_div_cancel_right]

/-- The Weyl square defect is the sign of the pair (-1,-1). -/
theorem weyl_square_defect_sign :
    gaussIndex a p ^ 2 / diagonalRatio a p (-1) = hilbertSign p (-1) (-1) := by
  rw [diagonalRatio_eq_rQ, gaussIndex_eq_gammaDiag, rQ_neg_one (finiteWeilIndexAxioms p),
    div_eq_mul_inv, mul_inv_rev, inv_inv, ← pow_two, ← pow_add]
  exact gamma_pow_four (finiteWeilIndexAxioms p) (localDiagonal_length a p)

/-- The Weyl–upper Bruhat defect is the sign of the pair (-b,-1). -/
theorem weyl_upper_defect_sign (b : ℚ_[p.val]ˣ) :
    gaussIndex a p ^ 2 * scaledIndex a p b / scaledIndex a p (-b⁻¹) =
      hilbertSign p (-b) (-1) := by
  rw [show -b⁻¹ = (-b)⁻¹ by simp, scaledIndex_inv]
  simp only [scaledIndex_eq_gammaDiag, gaussIndex_eq_gammaDiag]
  rw [(finiteWeilIndexAxioms p).gammaDiag_scaleForm_neg, div_eq_mul_inv, inv_inv, mul_assoc, ← pow_two]
  exact scalar_WUW (finiteWeilIndexAxioms p) (localDiagonal_length a p) b

#print axioms finiteWeilIndexAxioms
#print axioms localDiagonal_length
#print axioms scaledIndex_eq_gammaDiag
#print axioms gaussIndex_eq_gammaDiag
#print axioms diagonalRatio_eq_rQ
#print axioms diagonal_defect_sign
#print axioms weyl_square_defect_sign
#print axioms weyl_upper_defect_sign

end ZInQ.Manuscript.RC.Metaplectic2
