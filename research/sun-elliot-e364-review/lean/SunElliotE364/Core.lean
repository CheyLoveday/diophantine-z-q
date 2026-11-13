import Mathlib

/-!
Exact algebraic interfaces and adverse controls from the attached review.
These declarations concern abstract algebra, not the arithmetic realization of
any Selmer complex or the global completeness arguments.
-/

namespace SunElliotE364

open scoped BigOperators

/-- The common-strict determinant-coordinate formulas satisfy the displayed
normalization identity without dividing by a cross-evaluation. -/
theorem determinant_divisionFree {K : Type*} [Field K]
    (η δ θ qF qS : K) (hθ : θ ≠ 0) :
    let uF := -η * qF / θ
    let uS := δ * η * qS / θ
    qS * (δ * uF) + qF * uS = 0 := by
  dsimp
  field_simp
  <;> ring

/-- The opposite cross-evaluation premise gives the opposite-sign determinant
comparison. No unit assumption on the retained common cofactor is needed. -/
theorem determinant_oppositeSign {K : Type*} [Field K]
    (η δ θ qF qS : K) (hθ : θ ≠ 0) (hq : qS = -qF) :
    let uF := -η * qF / θ
    let uS := δ * η * qS / θ
    δ * uF = uS := by
  dsimp
  subst qS
  field_simp
  <;> ring

/-- If division is permitted (including a nonzero determinant of `J`), the
normalization defect is exactly the ratio of the actual cross-evaluations. -/
theorem determinant_ratio {K : Type*} [Field K]
    (η δ θ qF qS : K) (hθ : θ ≠ 0) (hδ : δ ≠ 0) (hqS : qS ≠ 0) (hη : η ≠ 0) :
    let uF := -η * qF / θ
    let uS := δ * η * qS / θ
    uS ≠ 0 ∧ δ * uF / uS = -qF / qS := by
  dsimp
  constructor
  · exact div_ne_zero (mul_ne_zero (mul_ne_zero hδ hη) hqS) hθ
  · field_simp
    <;> ring

/-- The primitive/rank-only countercontrol, parametrically over every field
and every nonzero uniformizer representative. -/
theorem determinant_countercontrol {K : Type*} [Field K] (π : K) (hπ : π ≠ 0) :
    let δ : K := -1
    let uF := -1 / π
    let uS := 1 / π ^ 2
    let qF := -π ^ 2
    let qS := π
    qS * (δ * uF) + qF * uS = 0 ∧ δ * uF / uS = π := by
  dsimp
  constructor
  · field_simp
    <;> ring
  · field_simp
    <;> ring

/-- One term of the reciprocal-polynomial transformation, for exactly the
index range `1 ≤ j ≤ d` occurring in the compiler construction. -/
theorem reciprocal_term {K : Type*} [Field K]
    (D G W Nj : K) {d j : ℕ} (hj : 1 ≤ j) (hjd : j ≤ d)
    (hW : D ^ 2 * G * W ≠ 0) :
    (D ^ 2 * G * W) ^ d * ((Nj / D) * (D ^ 2 * G * W)⁻¹ ^ (d - j)) =
      Nj * D ^ (2 * j - 1) * G ^ j * W ^ j := by
  have hD : D ≠ 0 := by
    intro hD
    subst D
    simp at hW
  let A := D ^ 2 * G * W
  have hA : A ≠ 0 := hW
  have hcancel : A ^ d * A⁻¹ ^ (d - j) = A ^ j := by
    rw [inv_pow]
    have hpow := pow_sub₀ A hA (Nat.sub_le d j)
    rw [Nat.sub_sub_self hjd] at hpow
    exact hpow.symm
  calc
    (D ^ 2 * G * W) ^ d * ((Nj / D) * (D ^ 2 * G * W)⁻¹ ^ (d - j)) =
        (Nj / D) * (A ^ d * A⁻¹ ^ (d - j)) := by dsimp [A]; ring
    _ = (Nj / D) * A ^ j := by rw [hcancel]
    _ = Nj * D ^ (2 * j - 1) * G ^ j * W ^ j := by
      dsimp [A]
      simp only [mul_pow, ← pow_mul]
      have hpow : D ^ (2 * j) = D ^ (2 * j - 1) * D := by
        have hexp : 2 * j = (2 * j - 1) + 1 := by omega
        conv_lhs => rw [hexp, pow_succ]
      field_simp [hD]
      rw [hpow]
      ring

/-- Coefficients along a scalar norm-tree edge. -/
def leftChild (c : ℚ) : ℚ := c / 2

def rightChild (c : ℚ) : ℚ := (c + 1) / 2

/-- Apply a norm-tree path from left to right, with `true` denoting a right edge. -/
def treeCoefficient (path : List Bool) : ℚ :=
  path.foldl (fun c b => if b then rightChild c else leftChild c) (1 / 2)

/-- The seven advertised precision coefficients, following the replay's
left-to-right path convention. -/
theorem scalar_tree_coefficients :
    treeCoefficient [false, false, false] = 1 / 16 ∧
    treeCoefficient [false, false, true] = 9 / 16 ∧
    treeCoefficient [false, true, false] = 5 / 16 ∧
    treeCoefficient [false, true, true] = 13 / 16 ∧
    treeCoefficient [true, false] = 3 / 8 ∧
    treeCoefficient [true, true, false] = 7 / 16 ∧
    treeCoefficient [true, true, true] = 15 / 16 := by
  norm_num [treeCoefficient, leftChild, rightChild]

/-- Exact strict thresholds used by the three height feedback arguments. -/
theorem height_thresholds :
    (24 * 4 : ℚ) / 64 < 2 ∧
      (24 : ℚ) / 16 < 2 ∧ ((24 : ℚ) / 16) / (2 - (24 : ℚ) / 16) = 3 ∧
      (24 : ℚ) / 48 < 1 := by
  norm_num

/-- Product-height loss in one local contribution. -/
theorem local_height_loss (P N : ℚ) (hP : 0 ≤ P) (hN : 0 ≤ N) :
    P - max 0 (P - N) = min P N := by
  rcases le_total P N with h | h
  · rw [max_eq_left (sub_nonpos.mpr h), min_eq_left h]
    ring
  · rw [max_eq_right (sub_nonneg.mpr h), min_eq_right h]
    ring

end SunElliotE364
