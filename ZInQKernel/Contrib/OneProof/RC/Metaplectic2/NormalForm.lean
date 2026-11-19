import ZInQKernel.Contrib.OneProof.RC.Metaplectic2.Matrices
import Mathlib.Tactic.LinearCombination

/-! The two ordinary Bruhat forms in tex 8790–8795. The explicit matrix
entries and the word reduction are on-the-spot (c). -/

namespace ZInQ.Manuscript.RC.Metaplectic2

open Matrix
open scoped MatrixGroups

/-- Upper cell and open Bruhat cell, in the manuscript's order. -/
inductive NormalForm (k : Type*) [Field k] where
  | upper (x : k) (t : kˣ)
  | openCell (x : k) (t : kˣ) (y : k)

namespace NormalForm

variable {k : Type*} [Field k]

def eval {G : Type*} [Group G] (U : k → G) (M : kˣ → G) (W : G) : NormalForm k → G
  | .upper x t => U x * M t
  | .openCell x t y => U x * M t * W * U y

abbrev matrix : NormalForm k → SL(2, k) :=
  eval upperMatrix diagonalMatrix weylMatrix

private theorem upper_entries (x : k) (t : kˣ) :
    (matrix (.upper x t) : Matrix (Fin 2) (Fin 2) k) =
      !![(t : k), x * ↑(t⁻¹ : kˣ); 0, ↑(t⁻¹ : kˣ)] := by
  change ((upperMatrix x * diagonalMatrix t : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = _
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> simp [upperMatrix, diagonalMatrix]

theorem open_entries (x : k) (t : kˣ) (y : k) :
    (matrix (.openCell x t y) : Matrix (Fin 2) (Fin 2) k) =
      !![-(x * ↑(t⁻¹ : kˣ)), (t : k) - x * ↑(t⁻¹ : kˣ) * y;
        -(↑(t⁻¹ : kˣ) : k), -(↑(t⁻¹ : kˣ) : k) * y] := by
  change ((matrix (.upper x t) * weylMatrix * upperMatrix y : SL(2, k)) :
    Matrix (Fin 2) (Fin 2) k) = _
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, upper_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [upperMatrix, weylMatrix, sub_eq_add_neg] <;> ring

/-- The normal form is determined by its projected matrix. -/
theorem matrix_injective : Function.Injective (matrix (k := k)) := by
  intro f g h
  have hh := congrArg (fun a : SL(2, k) => (a : Matrix (Fin 2) (Fin 2) k)) h
  cases f with
  | upper x t =>
    cases g with
    | upper z u =>
      rw [upper_entries, upper_entries] at hh
      have ht : t = u := Units.ext (congrFun (congrFun hh 0) 0)
      subst u
      have hx : x = z := mul_right_cancel₀ (t⁻¹).ne_zero (congrFun (congrFun hh 0) 1)
      rw [hx]
    | openCell z u w =>
      rw [upper_entries, open_entries] at hh
      have hz : (0 : k) = -(↑(u⁻¹ : kˣ) : k) := congrFun (congrFun hh 1) 0
      exact False.elim ((u⁻¹).ne_zero (neg_eq_zero.mp hz.symm))
  | openCell x t y =>
    cases g with
    | upper z u =>
      rw [open_entries, upper_entries] at hh
      have hz : -(↑(t⁻¹ : kˣ) : k) = 0 := congrFun (congrFun hh 1) 0
      exact False.elim ((t⁻¹).ne_zero (neg_eq_zero.mp hz))
    | openCell z u w =>
      rw [open_entries, open_entries] at hh
      have ht : t = u := inv_injective (Units.ext (neg_injective (congrFun (congrFun hh 1) 0)))
      subst u
      have hx : x = z := mul_right_cancel₀ (t⁻¹).ne_zero
        (neg_injective (congrFun (congrFun hh 0) 0))
      have hy : y = w := mul_left_cancel₀ (neg_ne_zero.mpr (t⁻¹).ne_zero)
        (congrFun (congrFun hh 1) 1)
      rw [hx, hy]

/-- Ordinary Bruhat decomposition, with no square-root choice. -/
theorem matrix_surjective : Function.Surjective (matrix (k := k)) := by
  intro g
  induction g using Matrix.SpecialLinearGroup.fin_two_induction with
  | h a b c d hdet =>
      by_cases hc : c = 0
      · subst c
        have hd : a * d = 1 := by simpa using hdet
        have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hd
        let t : kˣ := Units.mk0 a ha
        refine ⟨.upper (b * a) t, ?_⟩
        apply Subtype.ext
        change (matrix (.upper (b * a) t) : Matrix (Fin 2) (Fin 2) k) = !![a, b; 0, d]
        rw [upper_entries]
        have hd' : a⁻¹ = d := (eq_inv_of_mul_eq_one_right hd).symm
        simp [t, Units.val_inv_eq_inv_val, mul_assoc, hd, hd']
      · let t : kˣ := Units.mk0 (-c⁻¹) (neg_ne_zero.mpr (inv_ne_zero hc))
        refine ⟨.openCell (a / c) t (d / c), ?_⟩
        apply Subtype.ext
        change (matrix (.openCell (a / c) t (d / c)) : Matrix (Fin 2) (Fin 2) k) =
          !![a, b; c, d]
        rw [open_entries]
        have ht : (↑(t⁻¹ : kˣ) : k) = -c := by simp [t, Units.val_inv_eq_inv_val]
        rw [ht]
        have hb : -(c⁻¹) - (a / c) * (-c) * (d / c) = b := by
          field_simp [hc]
          linear_combination hdet
        have ha : -(a / c * -c) = a := by field_simp [hc]
        have hd : -(-c) * (d / c) = d := by field_simp [hc]
        rw [show (t : k) = -c⁻¹ from rfl, ha, hb, hd, neg_neg]

/-- Relations for a normalized generator system, for example after
quotienting the operator group by the central scalar units. -/
structure Relations {G : Type*} [Group G] (U : k → G) (M : kˣ → G) (W : G) : Prop where
  upper_zero : U 0 = 1
  diagonal_one : M 1 = 1
  upper_add : ∀ x y, U x * U y = U (x + y)
  diagonal_mul : ∀ t u, M t * M u = M (t * u)
  diagonal_upper : ∀ t x, M t * U x = U ((t : k) ^ 2 * x) * M t
  weyl_diagonal : ∀ t, W * M t = M t⁻¹ * W
  weyl_square : W * W = M (-1)
  weyl_upper : ∀ b : kˣ, W * U (b : k) * W =
    U ((-b⁻¹ : kˣ) : k) * M (-b⁻¹) * W * U ((-b⁻¹ : kˣ) : k)

def appendUpper (z : k) : NormalForm k → NormalForm k
  | .upper x t => .upper (x + (t : k)^2 * z) t
  | .openCell x t y => .openCell x t (y + z)

def appendDiagonal (u : kˣ) : NormalForm k → NormalForm k
  | .upper x t => .upper x (t * u)
  | .openCell x t y => .openCell x (t * u⁻¹) ((↑(u⁻¹ : kˣ) : k)^2 * y)

open Classical in
noncomputable def appendWeyl : NormalForm k → NormalForm k
  | .upper x t => .openCell x t 0
  | .openCell x t y =>
    if hy : y = 0 then .upper x (-t)
    else
      let b := Units.mk0 y hy
      let z := ((-b⁻¹ : kˣ) : k)
      .openCell (x + (t : k)^2 * z) (t * -b⁻¹) z

section Eval

variable {G : Type*} [Group G] {U : k → G} {M : kˣ → G} {W : G}
variable (R : Relations U M W)
include R

theorem eval_appendUpper (z : k) (n : NormalForm k) :
    eval U M W (appendUpper z n) = eval U M W n * U z := by
  cases n with
  | upper x t =>
    change U (x + (t : k)^2 * z) * M t = (U x * M t) * U z
    rw [mul_assoc, R.diagonal_upper, ← mul_assoc, R.upper_add]
  | openCell x t y =>
    change U x * M t * W * U (y + z) = (U x * M t * W * U y) * U z
    rw [mul_assoc (U x * M t * W), R.upper_add]

theorem eval_appendDiagonal (u : kˣ) (n : NormalForm k) :
    eval U M W (appendDiagonal u n) = eval U M W n * M u := by
  cases n with
  | upper x t =>
    change U x * M (t * u) = U x * M t * M u
    rw [mul_assoc, R.diagonal_mul]
  | openCell x t y =>
    have h : (u : k)^2 * ((↑(u⁻¹ : kˣ) : k)^2 * y) = y := by
      rw [← mul_assoc, ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        one_pow, one_mul]
    have he := R.diagonal_upper u ((↑(u⁻¹ : kˣ) : k)^2 * y)
    rw [h] at he
    change (U x * M (t * u⁻¹) * W) * U _ = (U x * M t * W * U y) * M u
    calc
      _ = U x * M t * (M u⁻¹ * W) * U ((↑(u⁻¹ : kˣ) : k)^2 * y) := by
        rw [← R.diagonal_mul]
        simp only [mul_assoc]
      _ = U x * M t * (W * M u) * U ((↑(u⁻¹ : kˣ) : k)^2 * y) := by rw [← R.weyl_diagonal]
      _ = U x * M t * W * (M u * U ((↑(u⁻¹ : kˣ) : k)^2 * y)) := by simp only [mul_assoc]
      _ = _ := by rw [he, ← mul_assoc]

theorem eval_appendWeyl (n : NormalForm k) :
    eval U M W (appendWeyl n) = eval U M W n * W := by
  classical
  cases n with
  | upper x t =>
    change (U x * M t * W) * U 0 = U x * M t * W
    rw [R.upper_zero, mul_one]
  | openCell x t y =>
    by_cases hy : y = 0
    · subst y
      simp only [appendWeyl, dite_true, eval, R.upper_zero, mul_one]
      rw [mul_assoc (U x * M t), R.weyl_square, mul_assoc, R.diagonal_mul]
      simp
    · rw [appendWeyl, dite_eq_right hy]
      let b := Units.mk0 y hy
      let z := ((-b⁻¹ : kˣ) : k)
      change U (x + (t : k)^2 * z) * M (t * -b⁻¹) * W * U z =
        U x * M t * W * U (b : k) * W
      calc
        _ = U x * (M t * U z) * M (-b⁻¹) * W * U z := by
          rw [R.diagonal_upper, ← R.upper_add, ← R.diagonal_mul]
          simp only [mul_assoc]
        _ = U x * M t * (U z * M (-b⁻¹) * W * U z) := by simp only [mul_assoc]
        _ = _ := by rw [← R.weyl_upper]; simp only [mul_assoc]

end Eval

#print axioms upper_entries
#print axioms open_entries
#print axioms matrix_injective
#print axioms matrix_surjective
#print axioms eval_appendUpper
#print axioms eval_appendDiagonal
#print axioms eval_appendWeyl

end NormalForm

end ZInQ.Manuscript.RC.Metaplectic2
