import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.Unit

/-!
# Common coordinate, part 6: non-vacuity of the step models

The relaxation-step hypotheses of (4.7) — `ActualStep` (consumed by
`prod_relax_of_actual_models`, `commonCoordinate_h47_of_models_full` and
`commonCoordinateModel_of_actual_models`) and the triangular-model hypothesis of
`prod_relax_of_models` — are inhabited, over `ℚ₂[[t]]` with `Λ`-unit basis comparisons:

* `actualStep_example`: one primitive dimension, `D_P = (0)`, Frobenius `F = 1` (trace `2`,
  determinant `q = 1`), scalars `z = z⁻¹ = 2`, so `e_q = −2` and the two-place block is the identity;
  the relaxed model is `diag(0, 1, 1, 1, 1)`, the class and functional `(1)` on the primitive side and
  `(−2, 0, 0, 0, 0)` on the relaxed side, the coordinates `u_prim = 1`, `u_rel = 4`, all basis
  comparisons the identity and `ε = 1`. The (4.7) relation `l_q u_rel = e_q² ε u_prim` reads
  `1 · 4 = 4 · 1 · 1`.

**Classification.** PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.CommonCoordinate

open Matrix ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central

/-- The coefficient field of the example. -/
abbrev KPS : Type := PowerSeries ℚ_[2]

/-- The relaxed model of the example: `diag(0, 1, 1, 1, 1)` on `Fin 1 ⊕ (Fin 2 ⊕ Fin 2)`. -/
noncomputable def exDiag : Fin 1 ⊕ (Fin 2 ⊕ Fin 2) → KPS := Sum.elim (fun _ => 0) (fun _ => 1)

theorem twoPlaceBlock_example :
    twoPlaceBlock (1 : Matrix (Fin 2) (Fin 2) KPS) 1 2 2 = 1 := by
  unfold twoPlaceBlock
  rw [show (2 : KPS) • (1 : Matrix (Fin 2) (Fin 2) KPS) - (1 : KPS) • 1 = 1 by
    rw [one_smul, two_smul, add_sub_cancel_right]]
  exact fromBlocks_one

theorem relaxed_example :
    fromBlocks (0 : Matrix (Fin 1) (Fin 1) KPS) 0 0 (twoPlaceBlock (1 : Matrix (Fin 2) (Fin 2) KPS) 1 2 2) =
      Matrix.diagonal exDiag := by
  rw [twoPlaceBlock_example, ← diagonal_zero, ← diagonal_one, fromBlocks_diagonal]
  rfl

/-- **Non-vacuity of `ActualStep`** with `Λ`-unit basis comparisons, over `ℚ₂[[t]]`. -/
theorem actualStep_example :
    ActualStep (1 : Matrix (Fin 2) (Fin 2) KPS) 1 1 2 2 2 1 4 1 LamUnit LamUnit := by
  refine ⟨1, 0, 1, 1, Matrix.diagonal exDiag, 1, 1, 0, fun _ => 1, fun _ => 1,
    Sum.elim (fun _ => -2) (fun _ => 0), Sum.elim (fun _ => -2) (fun _ => 0),
    by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, ← relaxed_example]
  · intro i
    simp [pointFactor]
  · intro i
    simp [pointFactor]
  · -- the relaxed coordinate: `adj diag(0,1,1,1,1) = diag(1,0,0,0,0)`
    unfold IsCoordOn
    rw [adjugate_diagonal]
    ext x y
    rcases x with x | x <;> rcases y with y | y
    · fin_cases x; fin_cases y
      simp only [vecMulVec_apply, Sum.elim_inl, Matrix.smul_apply, diagonal_apply_eq, smul_eq_mul]
      rw [Finset.prod_eq_one]
      · norm_num
      · intro j hj
        rcases j with j | j
        · fin_cases j; exact absurd rfl (Finset.ne_of_mem_erase hj)
        · rfl
    · simp [vecMulVec_apply, diagonal_apply_ne]
    · simp [vecMulVec_apply, diagonal_apply_ne]
    · simp only [vecMulVec_apply, Sum.elim_inr, mul_zero, Matrix.smul_apply, smul_eq_mul]
      by_cases hxy : x = y
      · subst hxy
        rw [diagonal_apply_eq, Finset.prod_eq_zero (i := Sum.inl 0)]
        · simp
        · simp
        · rfl
      · rw [diagonal_apply_ne _ (fun h => hxy (Sum.inr_injective h)), mul_zero]
  · unfold IsClassFunctionalCoord
    ext i j
    fin_cases i; fin_cases j
    simp [vecMulVec_apply, adjugate_fin_one]
  · rw [Matrix.one_mul, Matrix.mul_one, adjugate_fin_one]
    exact one_ne_zero
  · simpa using ZInQ.Manuscript.RC.Wiring.lamUnit_one
  · simpa using ZInQ.Manuscript.RC.Wiring.lamUnit_one
  · simp

end ZInQ.Contrib.CloudB3RC53.CommonCoordinate
