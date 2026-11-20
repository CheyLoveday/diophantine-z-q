import ZInQKernel.Contrib.OneProof.DeligneSerreFiniteLift.DS966Lifting
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-! # The roots of the local characteristic polynomial over the chosen number field -/

noncomputable section

namespace DS966Small

open Polynomial Matrix NumberField
open scoped NumberField

/-- When the power polynomial splits in the base field, every root of it in an
extension comes from that base field. Kind: PROVED. -/
theorem root_of_power_lifts {K F : Type*} [Field K] [Field F]
    (i : K →+* F) {m : ℕ} (hm : 0 < m) (hs : (X ^ m - C 1 : K[X]).Splits)
    {z : F} (hz : z ^ m = 1) : ∃ x : K, x ^ m = 1 ∧ i x = z := by
  let P : K[X] := X ^ m - C 1
  have hn : P ≠ 0 := X_pow_sub_C_ne_zero hm _
  have hr : (P.map i).IsRoot z := by simp [P, Polynomial.IsRoot, hz]
  have hmz := (mem_roots (map_ne_zero hn)).mpr hr
  rw [hs.roots_map i] at hmz
  obtain ⟨x, hx, hix⟩ := Multiset.mem_map.mp hmz
  have hxr := (mem_roots hn).mp hx
  exact ⟨x, by simpa [P, Polynomial.IsRoot, sub_eq_zero] using hxr, hix⟩

/-- A two-dimensional finite-order matrix has both its characteristic roots in
the embedded base field, whenever all roots of the power polynomial lie there.
No field embedding of the completed ambient field into the complex numbers is
used. Kind: PROVED. -/
theorem charpoly_factors_from_power_splits {K F : Type*} [Field K] [Field F]
    (i : K →+* F) {m : ℕ} (hm : 0 < m) (hs : (X ^ m - C 1 : K[X]).Splits)
    (M : Matrix (Fin 2) (Fin 2) F) (hM : M ^ m = 1) :
    ∃ x y : K, x ^ m = 1 ∧ y ^ m = 1 ∧
      M.charpoly = (X - C (i x)) * (X - C (i y)) := by
  let j : F →+* AlgebraicClosure F := algebraMap F _
  let N := j.mapMatrix M
  have hN : N ^ m = 1 := by
    change (j.mapMatrix M) ^ m = 1
    rw [← map_pow, hM, map_one]
  obtain ⟨x, y, hfac⟩ := DS966Lifting.charpoly_eq_two_factors N (IsAlgClosed.splits _)
  have hx : x ^ m = 1 := DS966Lifting.root_pow_eq_one hN (by rw [hfac]; simp [IsRoot])
  have hy : y ^ m = 1 := DS966Lifting.root_pow_eq_one hN (by rw [hfac]; simp [IsRoot])
  obtain ⟨a, ha, he⟩ := root_of_power_lifts (j.comp i) hm hs hx
  obtain ⟨b, hb, hf⟩ := root_of_power_lifts (j.comp i) hm hs hy
  refine ⟨a, b, ha, hb, (Polynomial.map_injective j j.injective) ?_⟩
  rw [← Matrix.charpoly_map M j]
  simpa only [N, RingHom.mapMatrix_apply, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, show j (i a) = x from he,
    show j (i b) = y from hf] using hfac

/-- Over a number field both roots are integers, so their sum and product can be
reduced through the prescribed map on the ring of integers. Kind: PROVED. -/
theorem charpoly_integral_factors_from_power_splits {K F : Type*} [Field K] [NumberField K]
    [Field F] (i : K →+* F) {m : ℕ} (hm : 0 < m) (hs : (X ^ m - C 1 : K[X]).Splits)
    (M : Matrix (Fin 2) (Fin 2) F) (hM : M ^ m = 1) :
    ∃ x y : 𝓞 K, x ^ m = 1 ∧ y ^ m = 1 ∧
      M.charpoly = (X - C (i x)) * (X - C (i y)) := by
  obtain ⟨x, y, hx, hy, hfac⟩ := charpoly_factors_from_power_splits i hm hs M hM
  let a : 𝓞 K := ⟨x, IsIntegral.of_pow hm (hx ▸ isIntegral_one)⟩
  let b : 𝓞 K := ⟨y, IsIntegral.of_pow hm (hy ▸ isIntegral_one)⟩
  exact ⟨a, b, Subtype.ext hx, Subtype.ext hy, hfac⟩

end DS966Small
