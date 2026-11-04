module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring.RingNF

/-!
# Duplication bounds for the model curve `y ^ 2 = x ^ 3 - δ ^ 2 * x`

The duplication map on projective `x`-coordinates is `[a : b] ↦ [F(a, b) : G(a, b)]` with
`F = (a ^ 2 + δ ^ 2 * b ^ 2) ^ 2` and `G = 4 * a * b * (a ^ 2 - δ ^ 2 * b ^ 2)`.
With `M = max |a| |b|` and `1 ≤ δ ≤ 5` we prove the elementary real estimates

* `M ^ 4 ≤ max |F| |G|` (using only `F`, including the case `a = b = 0`),
* `max |F| |G| ≤ 676 * M ^ 4`,
* `|G| ≤ 104 * M ^ 4`.

This is purely a statement about real polynomial inequalities; no height or arithmetic
input is used.
-/

public section

namespace ZInQ.ModelDuplication

theorem duplication_bounds (a b δ : ℝ) (hδlo : 1 ≤ δ) (hδhi : δ ≤ 5) :
    let M := max |a| |b|
    let F := (a ^ 2 + δ ^ 2 * b ^ 2) ^ 2
    let G := 4 * a * b * (a ^ 2 - δ ^ 2 * b ^ 2)
    M ^ 4 ≤ max |F| |G| ∧ max |F| |G| ≤ 676 * M ^ 4 ∧
      |G| ≤ 104 * M ^ 4 := by
  intro M F G
  -- Basic facts about `M = max |a| |b|`.
  have ha : |a| ≤ M := le_max_left |a| |b|
  have hb : |b| ≤ M := le_max_right |a| |b|
  have hM0 : 0 ≤ M := (abs_nonneg a).trans ha
  have ha2 : a ^ 2 ≤ M ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg a) ha 2
    rwa [sq_abs] at h
  have hb2 : b ^ 2 ≤ M ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg b) hb 2
    rwa [sq_abs] at h
  have hMab : M ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases le_total |a| |b| with h | h
    · have hM : M = |b| := max_eq_right h
      rw [hM, sq_abs]
      linarith [sq_nonneg a]
    · have hM : M = |a| := max_eq_left h
      rw [hM, sq_abs]
      linarith [sq_nonneg b]
  -- Facts about `δ`.
  have hδ2lo : 1 ≤ δ ^ 2 := by nlinarith
  have hδ2hi : δ ^ 2 ≤ 25 := by nlinarith
  -- The base `S = a ^ 2 + δ ^ 2 * b ^ 2` of `F = S ^ 2`.
  have hb2nn : 0 ≤ b ^ 2 := sq_nonneg b
  have hS_nn : 0 ≤ a ^ 2 + δ ^ 2 * b ^ 2 := by positivity
  have hS_lo : M ^ 2 ≤ a ^ 2 + δ ^ 2 * b ^ 2 := by
    have h1 : 1 * b ^ 2 ≤ δ ^ 2 * b ^ 2 := mul_le_mul_of_nonneg_right hδ2lo hb2nn
    linarith
  have hS_hi : a ^ 2 + δ ^ 2 * b ^ 2 ≤ 26 * M ^ 2 := by
    have h1 : δ ^ 2 * b ^ 2 ≤ 25 * M ^ 2 := mul_le_mul hδ2hi hb2 hb2nn (by positivity)
    linarith
  -- Bounds for `F`.
  have hF_lo : M ^ 4 ≤ (a ^ 2 + δ ^ 2 * b ^ 2) ^ 2 := by
    calc M ^ 4 = (M ^ 2) ^ 2 := by ring
      _ ≤ (a ^ 2 + δ ^ 2 * b ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg M) hS_lo 2
  have hF_hi : (a ^ 2 + δ ^ 2 * b ^ 2) ^ 2 ≤ 676 * M ^ 4 := by
    calc (a ^ 2 + δ ^ 2 * b ^ 2) ^ 2 ≤ (26 * M ^ 2) ^ 2 := pow_le_pow_left₀ hS_nn hS_hi 2
      _ = 676 * M ^ 4 := by ring
  have hFabs : |F| = (a ^ 2 + δ ^ 2 * b ^ 2) ^ 2 := abs_of_nonneg (sq_nonneg _)
  -- Bound for `G`.
  have hD : |a ^ 2 - δ ^ 2 * b ^ 2| ≤ a ^ 2 + δ ^ 2 * b ^ 2 := by
    have hδb : 0 ≤ δ ^ 2 * b ^ 2 := by positivity
    rw [abs_le]
    constructor <;> linarith [sq_nonneg a]
  have hab : |a| * |b| ≤ M ^ 2 := by
    rw [sq]
    exact mul_le_mul ha hb (abs_nonneg b) hM0
  have hG : |G| ≤ 104 * M ^ 4 := by
    have hGabs : |G| = 4 * (|a| * |b|) * |a ^ 2 - δ ^ 2 * b ^ 2| := by
      show |4 * a * b * (a ^ 2 - δ ^ 2 * b ^ 2)| = _
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4)]
      ring
    rw [hGabs]
    calc 4 * (|a| * |b|) * |a ^ 2 - δ ^ 2 * b ^ 2|
        ≤ 4 * M ^ 2 * (a ^ 2 + δ ^ 2 * b ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hab (by positivity)) hD (abs_nonneg _)
            (by positivity)
      _ ≤ 4 * M ^ 2 * (26 * M ^ 2) := mul_le_mul_of_nonneg_left hS_hi (by positivity)
      _ = 104 * M ^ 4 := by ring
  have h104 : 104 * M ^ 4 ≤ 676 * M ^ 4 := by
    have h4 : 0 ≤ M ^ 4 := by positivity
    linarith
  exact ⟨(hF_lo.trans_eq hFabs.symm).trans (le_max_left _ _),
    max_le (hFabs.trans_le hF_hi) (hG.trans h104), hG⟩

end ZInQ.ModelDuplication
