import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.LinearAlgebra.SymplecticGroup

set_option linter.all false
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace GapTheta

/-- Integer `4 × 4` matrices with the block index of `Matrix.symplecticGroup (Fin 2) ℤ`. -/
abbrev Mat4 := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ

/-- `SL₂(ℤ)` on the coordinates `(a₁, c₁)`. -/
def iota1 : SL(2, ℤ) →* Mat4 where
  toFun g := Matrix.fromBlocks !![(g : Matrix (Fin 2) (Fin 2) ℤ) 0 0, 0; 0, 1]
    !![(g : Matrix (Fin 2) (Fin 2) ℤ) 0 1, 0; 0, 0] !![(g : Matrix (Fin 2) (Fin 2) ℤ) 1 0, 0; 0, 0]
    !![(g : Matrix (Fin 2) (Fin 2) ℤ) 1 1, 0; 0, 1]
  map_one' := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp
  map_mul' g h := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_mul]

/-- `SL₂(ℤ)` on the coordinates `(a₂, c₂)`. -/
def iota2 : SL(2, ℤ) →* Mat4 where
  toFun g := Matrix.fromBlocks !![1, 0; 0, (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0]
    !![0, 0; 0, (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1] !![0, 0; 0, (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0]
    !![1, 0; 0, (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1]
  map_one' := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp
  map_mul' g h := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_mul]

/-- The rotation `[[U, 0], [0, U⁻ᵀ]]` (`U⁻ᵀ` written as the transposed adjugate). -/
def rot : SL(2, ℤ) →* Mat4 where
  toFun g := Matrix.fromBlocks (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0
    !![(g : Matrix (Fin 2) (Fin 2) ℤ) 1 1, -(g : Matrix (Fin 2) (Fin 2) ℤ) 1 0;
       -(g : Matrix (Fin 2) (Fin 2) ℤ) 0 1, (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0]
  map_one' := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp
  map_mul' g h := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_mul] <;>
      ring

/-- The translation `[[1, S], [0, 1]]`. -/
def Tm (S : Matrix (Fin 2) (Fin 2) ℤ) : Mat4 := Matrix.fromBlocks 1 S 0 1

theorem Tm_mul (S S' : Matrix (Fin 2) (Fin 2) ℤ) : Tm S * Tm S' = Tm (S + S') := by
  simp [Tm, Matrix.fromBlocks_multiply, add_comm]

theorem det_sl (g : SL(2, ℤ)) :
    (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
  have := g.2; rwa [Matrix.det_fin_two] at this

/-- The sixteen relations `ω(M eₐ, M e_b) = ω(eₐ, e_b)` of a symplectic matrix. -/
theorem sp_rel {M : Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ) (a b : Fin 2 ⊕ Fin 2) :
    -M (Sum.inl 0) a * M (Sum.inr 0) b - M (Sum.inl 1) a * M (Sum.inr 1) b +
      M (Sum.inr 0) a * M (Sum.inl 0) b + M (Sum.inr 1) a * M (Sum.inl 1) b = Matrix.J (Fin 2) ℤ a b := by
  have h := congrFun (congrFun (SymplecticGroup.mem_iff'.1 hM) a) b
  rw [← h]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.J]
  ring

theorem iota1_mem (g : SL(2, ℤ)) : iota1 g ∈ Matrix.symplecticGroup (Fin 2) ℤ := by
  rw [SymplecticGroup.mem_iff']
  have := det_sl g
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [iota1, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.J] <;> linarith

theorem iota2_mem (g : SL(2, ℤ)) : iota2 g ∈ Matrix.symplecticGroup (Fin 2) ℤ := by
  rw [SymplecticGroup.mem_iff']
  have := det_sl g
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [iota2, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.J] <;> linarith

theorem rot_mem (g : SL(2, ℤ)) : rot g ∈ Matrix.symplecticGroup (Fin 2) ℤ := by
  rw [SymplecticGroup.mem_iff']
  have := det_sl g
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.J] <;> linarith

end GapTheta
