module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Coordinate identities for the model elliptic curve over a field containing `√2`

Elementary identities in a characteristic-zero field `K` containing an element `s`
with `s ^ 2 = 2` (e.g. `s = √2` in `ℚ(√2)`).  With `ε = 1 + s`, `d = 75 - 53 s` and
`δ = 3 - s` we check:

* `ε` is a unit with inverse `s - 1`;
* `d ε⁴ = δ`;
* `(x, y) ↦ (ε⁴ x, ε⁶ y)` maps `y² = x³ - d² x` onto `y² = x³ - δ² x` (both directions);
* `R = (1 + s, 2 s)` lies on `y² = x³ - δ² x`;
* the tangent-line (doubling) coordinates of `R` are `((57 - 28 s)/8, (-660 + 417 s)/32)`;
* scaling back by `ε⁻⁴, ε⁻⁶` gives `((1641 - 1160 s)/8, (-123720 + 87483 s)/32)`.

These are coordinate identities only; nothing here is a group-law, rank or generation result.
Every polynomial certificate below is an explicit multiple of `s ^ 2 - 2`, checked by `ring`.
All nonzero denominators are derived from `hs` and `CharZero K`.

The `[CharZero K]` binder from the prescribed `variable` line is kept in *every* theorem so
that the exported signatures are exactly the prescribed ones.  Three of the identities
(`epsilon_inverse`, `delta_identity`, `point_R`) do not actually use it, so Lean's
`linter.unusedSectionVars` emits a (harmless) warning for them; its suggested `omit` is
deliberately not applied because it would change the prescribed signature.
-/

public section

namespace ZInQ.ModelCoordinates
variable {K : Type*} [Field K] [CharZero K]

theorem epsilon_inverse (s : K) (hs : s ^ 2 = 2) :
    (1 + s) * (s - 1) = 1 ∧ (s - 1) * (1 + s) = 1 :=
  ⟨by linear_combination hs, by linear_combination hs⟩

theorem delta_identity (s : K) (hs : s ^ 2 = 2) :
    (75 - 53 * s) * (1 + s) ^ 4 = 3 - s := by
  -- `(75 - 53 s)(1 + s)^4 - (3 - s) = (-53 s^3 - 137 s^2 - 124 s - 36)(s^2 - 2)`
  linear_combination (-53 * s ^ 3 - 137 * s ^ 2 - 124 * s - 36) * hs

theorem coordinate_change (s x y : K) (hs : s ^ 2 = 2) :
    (y ^ 2 = x ^ 3 - (75 - 53 * s) ^ 2 * x) ↔
      (((1 + s) ^ 6 * y) ^ 2 =
        ((1 + s) ^ 4 * x) ^ 3 -
          (3 - s) ^ 2 * ((1 + s) ^ 4 * x)) := by
  have hd := delta_identity s hs
  have he : (1 + s) ≠ 0 := left_ne_zero_of_mul_eq_one (epsilon_inverse s hs).1
  have he12 : (1 + s) ^ 12 ≠ 0 := pow_ne_zero 12 he
  constructor
  · intro h
    linear_combination (1 + s) ^ 12 * h -
      (1 + s) ^ 4 * x * ((3 - s) + (75 - 53 * s) * (1 + s) ^ 4) * hd
  · intro h
    apply mul_left_cancel₀ he12
    linear_combination h +
      (1 + s) ^ 4 * x * ((3 - s) + (75 - 53 * s) * (1 + s) ^ 4) * hd

theorem point_R (s : K) (hs : s ^ 2 = 2) :
    (2 * s) ^ 2 = (1 + s) ^ 3 - (3 - s) ^ 2 * (1 + s) := by
  linear_combination (-4) * hs

theorem tangent_coordinates (s : K) (hs : s ^ 2 = 2) :
    4 * s ≠ 0 ∧
      (let m := (3 * (1 + s) ^ 2 - (3 - s) ^ 2) / (4 * s)
       let x₂ := m ^ 2 - 2 * (1 + s)
       let y₂ := m * ((1 + s) - x₂) - 2 * s
       x₂ = (57 - 28 * s) / 8 ∧ y₂ = (-660 + 417 * s) / 32) := by
  have hs0 : s ≠ 0 := by
    intro h
    have h2 : (2 : K) = 0 := by rw [← hs, h, sq, mul_zero]
    exact OfNat.ofNat_ne_zero 2 h2
  have h4s : (4 : K) * s ≠ 0 := mul_ne_zero (OfNat.ofNat_ne_zero 4) hs0
  -- the tangent slope simplifies to `(12 - s) / 4`
  have hm : (3 * (1 + s) ^ 2 - (3 - s) ^ 2) / (4 * s) = (12 - s) / 4 := by
    rw [div_eq_iff h4s]
    linear_combination 3 * hs
  refine ⟨h4s, ?_⟩
  dsimp only
  rw [hm]
  constructor
  · linear_combination (1 / 16) * hs
  · linear_combination ((s - 84) / 64) * hs

theorem scale_back (s : K) (hs : s ^ 2 = 2) :
    ((57 - 28 * s) / 8) / (1 + s) ^ 4 = (1641 - 1160 * s) / 8 ∧
    ((-660 + 417 * s) / 32) / (1 + s) ^ 6 =
      (-123720 + 87483 * s) / 32 := by
  have he : (1 + s) ≠ 0 := left_ne_zero_of_mul_eq_one (epsilon_inverse s hs).1
  have e4 : (1 + s) ^ 4 = 17 + 12 * s := by
    linear_combination (s ^ 2 + 4 * s + 8) * hs
  have e6 : (1 + s) ^ 6 = 99 + 70 * s := by
    linear_combination (s ^ 4 + 6 * s ^ 3 + 17 * s ^ 2 + 32 * s + 49) * hs
  constructor
  · rw [div_eq_iff (pow_ne_zero 4 he), e4]
    linear_combination 1740 * hs
  · rw [div_eq_iff (pow_ne_zero 6 he), e6]
    linear_combination (-3061905 / 16) * hs

end ZInQ.ModelCoordinates
