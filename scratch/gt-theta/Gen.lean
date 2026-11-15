import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.Tactic

set_option linter.all false
open Matrix Matrix.SpecialLinearGroup ModularGroup
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


/-- Bezout in `SL₂(ℤ)`: some `U` kills the second coordinate of `(x, y)`. -/
theorem bezout_sl (x y : ℤ) : ∃ U : SL(2, ℤ),
    (U : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * x + (U : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * y = 0 := by
  by_cases h0 : Int.gcd x y = 0
  · refine ⟨1, ?_⟩
    have hx : x = 0 := Int.gcd_eq_zero_iff.1 h0 |>.1
    have hy : y = 0 := Int.gcd_eq_zero_iff.1 h0 |>.2
    simp [hx, hy]
  · obtain ⟨x', hx'⟩ := Int.gcd_dvd_left (a := x) (b := y)
    obtain ⟨y', hy'⟩ := Int.gcd_dvd_right (a := x) (b := y)
    have hg := Int.gcd_eq_gcd_ab x y
    have hg0 : (Int.gcd x y : ℤ) ≠ 0 := by exact_mod_cast h0
    generalize (Int.gcd x y : ℤ) = G at hx' hy' hg hg0
    generalize x.gcdA y = A at hg
    generalize x.gcdB y = B at hg
    subst hx' hy'
    have hdet : A * x' + B * y' = 1 := by
      have : G * (A * x' + B * y') = G * 1 := by linear_combination -hg
      exact mul_left_cancel₀ hg0 this
    refine ⟨⟨!![A, B; -y', x'], by rw [Matrix.det_fin_two_of]; linarith⟩, ?_⟩
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring

section Reduction

variable (H : Submonoid Mat4) (h1 : ∀ g, iota1 g ∈ H) (h2 : ∀ g, iota2 g ∈ H) (hr : ∀ g, rot g ∈ H)
  (hT : ∀ x s : ℤ, Tm !![x, s; s, 0] ∈ H)
include h1 h2 hr hT

theorem red_stab {M : Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    (e0 : M (Sum.inl 0) (Sum.inl 0) = 1) (e1 : M (Sum.inl 1) (Sum.inl 0) = 0)
    (e2 : M (Sum.inr 0) (Sum.inl 0) = 0) (e3 : M (Sum.inr 1) (Sum.inl 0) = 0) : M ∈ H := by
  have r := sp_rel hM
  have k1 := r (Sum.inl 0) (Sum.inl 1)
  have k2 := r (Sum.inl 0) (Sum.inr 0)
  have k3 := r (Sum.inl 0) (Sum.inr 1)
  have k4 := r (Sum.inl 1) (Sum.inr 1)
  have k5 := r (Sum.inl 1) (Sum.inr 0)
  have k6 := r (Sum.inr 0) (Sum.inr 1)
  simp only [e0, e1, e2, e3, Matrix.J, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] at k1 k2 k3 k4 k5 k6
  simp at k1 k2 k3
  simp only [k1, k2, k3] at k4 k5 k6
  simp at k4 k5 k6
  have hp : M (Sum.inl 0) (Sum.inl 1) =
      M (Sum.inr 1) (Sum.inl 1) * M (Sum.inl 1) (Sum.inr 0) -
        M (Sum.inl 1) (Sum.inl 1) * M (Sum.inr 1) (Sum.inr 0) := by linear_combination -k5
  have hr' : M (Sum.inl 0) (Sum.inr 1) =
      M (Sum.inl 1) (Sum.inr 0) * M (Sum.inr 1) (Sum.inr 1) -
        M (Sum.inr 1) (Sum.inr 0) * M (Sum.inl 1) (Sum.inr 1) := by linear_combination k6
  have hγ : !![M (Sum.inl 1) (Sum.inl 1), M (Sum.inl 1) (Sum.inr 1);
      M (Sum.inr 1) (Sum.inl 1), M (Sum.inr 1) (Sum.inr 1)].det = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination -k4
  let γ : SL(2, ℤ) := ⟨_, hγ⟩
  have key : M = Tm !![M (Sum.inl 0) (Sum.inr 0) - M (Sum.inl 1) (Sum.inr 0) * M (Sum.inr 1) (Sum.inr 0),
      M (Sum.inl 1) (Sum.inr 0); M (Sum.inl 1) (Sum.inr 0), 0] *
      rot (T ^ (-M (Sum.inr 1) (Sum.inr 0))) * iota2 γ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Tm, rot, iota2, γ, coe_T_zpow, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
        e0, e1, e2, e3, k1, k2, k3, hp, hr'] <;> ring
  rw [key]
  exact H.mul_mem (H.mul_mem (hT _ _) (hr _)) (h2 _)

end Reduction

end GapTheta
