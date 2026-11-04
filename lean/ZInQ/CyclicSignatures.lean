module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.ZMod.Defs

import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic

/-!
# Finite group-algebra helpers: `F₂[ℤ/2ⁿ]`

The group algebra of the cyclic group `ZMod (2 ^ n)` over `ZMod 2` (Mathlib's
`AddMonoidAlgebra`, the convolution algebra of finitely supported functions) satisfies:

* `f ^ (2 ^ n)` is the augmentation of `f` placed at the identity `0`;
* `f` is a unit iff its augmentation (the literal finite sum of its coefficients) is `1`;
* if the augmentation is `1`, then `f ^ (2 ^ n - 1)` is a two-sided inverse of `f`.

The case `n = 0` is included: `ZMod 1` is the trivial group, `2 ^ 0 = 1`, and the inverse
exponent is `0`.

## Note on the statement shapes

In the pinned Mathlib, `AddMonoidAlgebra R M` is a one-field structure
(`ofCoeff :: coeff : M →₀ R`), not a type synonym for `M →₀ R`. Hence there is no
`AddMonoidAlgebra.sum` and no coercion `(M →₀ R) → AddMonoidAlgebra R M`; the literal
proposed shapes `f.sum (fun _ a => a)` and `Finsupp.single 0 (…) : AddMonoidAlgebra _ _` do not
elaborate. The augmentation is therefore written `f.coeff.sum (fun _ a => a)` (the same literal
finite sum over the underlying finsupp) and the element "`a` at `0`" is
`AddMonoidAlgebra.single 0 a`, which is by definition `AddMonoidAlgebra.ofCoeff (Finsupp.single 0 a)`.
-/

public section

namespace ZInQ.CyclicSignatures

/-- The group algebra `F₂[ℤ/2ⁿ]` has characteristic two. -/
private theorem charP_two (n : ℕ) :
    CharP (AddMonoidAlgebra (ZMod 2) (ZMod (2 ^ n))) 2 where
  cast_eq_zero_iff x := by
    rw [AddMonoidAlgebra.natCast_def, AddMonoidAlgebra.single_eq_zero]
    exact CharP.cast_eq_zero_iff (ZMod 2) 2 x

/-- Every element of `ZMod 2` is `0` or `1`. -/
private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

/-- Frobenius computation: in `F₂[ℤ/2ⁿ]`, the `2 ^ n`-th power of `f` is its augmentation
placed at the identity `0`. -/
theorem pow_two_pow_eq_single_augmentation (n : Nat)
    (f : AddMonoidAlgebra (ZMod 2) (ZMod (2 ^ n))) :
    f ^ (2 ^ n) = AddMonoidAlgebra.single 0 (f.coeff.sum (fun _ a => a)) := by
  have := charP_two n
  have hn : (2 : ℕ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  induction f using AddMonoidAlgebra.induction_linear with
  | zero =>
    rw [zero_pow hn, AddMonoidAlgebra.coeff_zero, Finsupp.sum_zero_index,
      AddMonoidAlgebra.single_zero]
  | add x y hx hy =>
    rw [add_pow_char_pow, hx, hy, AddMonoidAlgebra.coeff_add,
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), AddMonoidAlgebra.single_add]
  | single m r =>
    rw [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.coeff_single,
      Finsupp.sum_single_index rfl, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rcases zmod_two_cases r with rfl | rfl
    · rw [zero_pow hn]
    · rw [one_pow]

/-- Coefficient-level form of `pow_two_pow_eq_single_augmentation`, stated with the literal
`Finsupp.single 0` of the proposed statement. -/
theorem coeff_pow_two_pow_eq_single_augmentation (n : Nat)
    (f : AddMonoidAlgebra (ZMod 2) (ZMod (2 ^ n))) :
    (f ^ (2 ^ n)).coeff = Finsupp.single 0 (f.coeff.sum (fun _ a => a)) := by
  rw [pow_two_pow_eq_single_augmentation, AddMonoidAlgebra.coeff_single]

/-- If the augmentation of `f` is `1`, then `f ^ (2 ^ n - 1)` is a two-sided inverse of `f`. -/
private theorem inverse_aux (n : Nat)
    (f : AddMonoidAlgebra (ZMod 2) (ZMod (2 ^ n)))
    (hf : f.coeff.sum (fun _ a => a) = 1) :
    f * f ^ (2 ^ n - 1) = 1 ∧ f ^ (2 ^ n - 1) * f = 1 := by
  have hn : (2 : ℕ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  have h : f ^ (2 ^ n) = 1 := by
    rw [pow_two_pow_eq_single_augmentation, hf, AddMonoidAlgebra.one_def]
  exact ⟨by rw [mul_pow_sub_one hn, h], by rw [pow_sub_one_mul hn, h]⟩

/-- A group-algebra element is a unit iff its augmentation is `1`. -/
theorem isUnit_iff_augmentation_eq_one (n : Nat)
    (f : AddMonoidAlgebra (ZMod 2) (ZMod (2 ^ n))) :
    IsUnit f ↔ f.coeff.sum (fun _ a => a) = 1 := by
  constructor
  · intro hf
    have h := hf.pow (2 ^ n)
    rw [pow_two_pow_eq_single_augmentation] at h
    rcases zmod_two_cases (f.coeff.sum fun _ a => a) with h0 | h1
    · rw [h0, AddMonoidAlgebra.single_zero] at h
      exact absurd h not_isUnit_zero
    · exact h1
  · intro hf
    obtain ⟨h1, h2⟩ := inverse_aux n f hf
    exact ⟨⟨f, f ^ (2 ^ n - 1), h1, h2⟩, rfl⟩

/-- An augmentation-one element has the explicit two-sided inverse `f ^ (2 ^ n - 1)`. -/
theorem explicit_inverse_of_augmentation_eq_one (n : Nat)
    (f : AddMonoidAlgebra (ZMod 2) (ZMod (2 ^ n)))
    (hf : f.coeff.sum (fun _ a => a) = 1) :
    f * f ^ (2 ^ n - 1) = 1 ∧ f ^ (2 ^ n - 1) * f = 1 :=
  inverse_aux n f hf

end ZInQ.CyclicSignatures

end
