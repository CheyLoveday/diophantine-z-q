import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.NormalForm

/-! The ordinary SL₂ presentation used at tex 8790–8795. The
homomorphism proof via right multiplication is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2.NormalForm

open Matrix
open scoped MatrixGroups

variable {k : Type*} [Field k]

private theorem matrix_relations :
    Relations (G := SL(2, k)) upperMatrix diagonalMatrix weylMatrix where
  upper_zero := by
    apply Subtype.ext
    change (upperMatrix (0 : k) : Matrix (Fin 2) (Fin 2) k) = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperMatrix, Matrix.one_apply]
  diagonal_one := by
    apply Subtype.ext
    change (diagonalMatrix (1 : kˣ) : Matrix (Fin 2) (Fin 2) k) = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonalMatrix, Matrix.one_apply]
  upper_add x y := by
    apply Subtype.ext
    change ((upperMatrix x * upperMatrix y : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) =
      (upperMatrix (x + y) : Matrix (Fin 2) (Fin 2) k)
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> simp [upperMatrix, add_comm]
  diagonal_mul t u := by
    apply Subtype.ext
    change ((diagonalMatrix t * diagonalMatrix u : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) =
      (diagonalMatrix (t * u) : Matrix (Fin 2) (Fin 2) k)
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> simp [diagonalMatrix, mul_inv_rev, mul_comm]
  diagonal_upper t x := by
    apply Subtype.ext
    change ((diagonalMatrix t * upperMatrix x : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) =
      ((upperMatrix ((t : k)^2 * x) * diagonalMatrix t : SL(2, k)) : Matrix (Fin 2) (Fin 2) k)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
      simp [upperMatrix, diagonalMatrix]
    field_simp [t.ne_zero]
    <;> ring
  weyl_diagonal t := by
    apply Subtype.ext
    change ((weylMatrix * diagonalMatrix t : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) =
      ((diagonalMatrix t⁻¹ * weylMatrix : SL(2, k)) : Matrix (Fin 2) (Fin 2) k)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> simp [weylMatrix, diagonalMatrix]
  weyl_square := by
    apply Subtype.ext
    change ((weylMatrix * weylMatrix : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) =
      (diagonalMatrix (-1 : kˣ) : Matrix (Fin 2) (Fin 2) k)
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> simp [weylMatrix, diagonalMatrix]
  weyl_upper b := by
    let z : kˣ := -b⁻¹
    apply Subtype.ext
    change ((weylMatrix * upperMatrix (b : k) * weylMatrix : SL(2, k)) :
      Matrix (Fin 2) (Fin 2) k) = (matrix (.openCell (z : k) z (z : k)) : Matrix (Fin 2) (Fin 2) k)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, open_entries]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
      simp [z, weylMatrix, upperMatrix, Units.val_inv_eq_inv_val, b.ne_zero]

variable {G : Type*} [Group G] {U : k → G} {M : kˣ → G} {W : G}

/-- Every generator system satisfying the exact relations acts on SL₂.
The equations may be instantiated in an operator group modulo scalars. -/
theorem representation_of_relations (R : Relations U M W) :
    ∃ ρ : SL(2, k) →* G,
      (∀ z, ρ (upperMatrix z) = U z) ∧
      (∀ t, ρ (diagonalMatrix t) = M t) ∧ ρ weylMatrix = W := by
  let nOf (g : SL(2, k)) := (matrix_surjective g).choose
  have hn (g) : matrix (nOf g) = g := (matrix_surjective g).choose_spec
  let F (g : SL(2, k)) := eval U M W (nOf g)
  have hF (n : NormalForm k) : F (matrix n) = eval U M W n :=
    congrArg (eval U M W) (matrix_injective (hn (matrix n)))
  have h1 : F 1 = 1 := by
    have hmat : matrix (.upper 0 (1 : kˣ)) = 1 := by simp [eval, matrix_relations.upper_zero,
      matrix_relations.diagonal_one]
    rw [← hmat, hF, eval, R.upper_zero, R.diagonal_one, one_mul]
  have hU (g : SL(2, k)) (z : k) : F (g * upperMatrix z) = F g * U z := by
    have hm := eval_appendUpper matrix_relations z (nOf g)
    rw [show eval upperMatrix diagonalMatrix weylMatrix = (matrix (k := k)) from rfl, hn] at hm
    rw [← hm, hF, eval_appendUpper R]
  have hM (g : SL(2, k)) (t : kˣ) : F (g * diagonalMatrix t) = F g * M t := by
    have hm := eval_appendDiagonal matrix_relations t (nOf g)
    rw [show eval upperMatrix diagonalMatrix weylMatrix = (matrix (k := k)) from rfl, hn] at hm
    rw [← hm, hF, eval_appendDiagonal R]
  have hW (g : SL(2, k)) : F (g * weylMatrix) = F g * W := by
    have hm := eval_appendWeyl matrix_relations (nOf g)
    rw [show eval upperMatrix diagonalMatrix weylMatrix = (matrix (k := k)) from rfl, hn] at hm
    rw [← hm, hF, eval_appendWeyl R]
  have hmul (g h : SL(2, k)) : F (g * h) = F g * F h := by
    rw [← hn h, hF]
    cases nOf h with
    | upper x t =>
      change F (g * (upperMatrix x * diagonalMatrix t)) = F g * (U x * M t)
      rw [← mul_assoc, hM, hU, mul_assoc]
    | openCell x t y =>
      change F (g * (upperMatrix x * diagonalMatrix t * weylMatrix * upperMatrix y)) =
        F g * (U x * M t * W * U y)
      simp only [← mul_assoc, hU, hM, hW]
  exact ⟨{ toFun := F, map_one' := h1, map_mul' := hmul }, fun z => by simpa [h1] using hU 1 z,
    fun t => by simpa [h1] using hM 1 t, by simpa [h1] using hW 1⟩


end ZInQ.Manuscript.RC.Metaplectic2.NormalForm
