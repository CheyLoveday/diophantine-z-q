import ZInQKernel.Contrib.OneProof.FHNonvanishing.FE

open HeckeRing.GL2 CongruenceSubgroup ZMod

namespace ZInQ.GZFH

open ZInQ.GZDecomp

/-! ## The character `χ_D` on `ZMod |D|` and its Fourier transform -/

section Character

variable {D : ℤ}

theorem chiDMod_eq (x : ZMod D.natAbs) : chiDMod D x = (jacobiSym (x.val : ℤ) D.natAbs : ℂ) := rfl

theorem chiDMod_intCast [NeZero D.natAbs] (n : ℤ) :
    chiDMod D (n : ZMod D.natAbs) = (jacobiSym n D.natAbs : ℂ) := by
  rw [chiDMod_eq, ZMod.val_intCast, ← jacobiSym.mod_left]

theorem chiDMod_mul [NeZero D.natAbs] (x y : ZMod D.natAbs) :
    chiDMod D (x * y) = chiDMod D x * chiDMod D y := by
  have hx : x = ((x.val : ℤ) : ZMod D.natAbs) := by simp
  have hy : y = ((y.val : ℤ) : ZMod D.natAbs) := by simp
  rw [hx, hy, ← Int.cast_mul, chiDMod_intCast, chiDMod_intCast, chiDMod_intCast,
    jacobiSym.mul_left]
  push_cast; ring

theorem chiDMod_one [NeZero D.natAbs] : chiDMod D 1 = 1 := by
  rw [show (1 : ZMod D.natAbs) = ((1 : ℤ) : ZMod D.natAbs) by simp, chiDMod_intCast,
    jacobiSym.one_left]; simp

theorem chiDMod_unit [NeZero D.natAbs] (u : (ZMod D.natAbs)ˣ) :
    chiDMod D u = 1 ∨ chiDMod D u = -1 := by
  rw [chiDMod_eq]
  have h := ZMod.val_coe_unit_coprime u
  rcases jacobiSym.eq_one_or_neg_one (a := ((u : ZMod D.natAbs).val : ℤ)) (b := D.natAbs)
    (by rw [Int.gcd_natCast_natCast]; exact h) with h1 | h1
  · left; rw [h1]; simp
  · right; rw [h1]; simp

theorem chiDMod_unit_sq [NeZero D.natAbs] (u : (ZMod D.natAbs)ˣ) :
    chiDMod D u * chiDMod D u = 1 := by
  rcases chiDMod_unit u with h | h <;> rw [h] <;> norm_num

theorem chiDMod_inv [NeZero D.natAbs] (u : (ZMod D.natAbs)ˣ) :
    chiDMod D (↑u⁻¹ : ZMod D.natAbs) = chiDMod D u := by
  have h1 : chiDMod D u * chiDMod D (↑u⁻¹ : ZMod D.natAbs) = 1 := by
    rw [← chiDMod_mul, Units.mul_inv, chiDMod_one]
  rcases chiDMod_unit u with h | h <;> rw [h] at h1 ⊢
  · linear_combination h1
  · linear_combination -h1

/-- `𝓕 χ_D (u) = χ_D(u) 𝓕 χ_D (1)` at a unit `u`. -/
theorem dft_chiDMod_unit [NeZero D.natAbs] (u : (ZMod D.natAbs)ˣ) :
    𝓕 (chiDMod D) u = chiDMod D u * 𝓕 (chiDMod D) 1 := by
  rw [dft_apply, dft_apply, Finset.mul_sum]
  refine Fintype.sum_equiv (Units.mulRight u) _ _ (fun j => ?_)
  simp only [Units.mulRight_apply, mul_one, smul_eq_mul]
  rw [chiDMod_mul]
  linear_combination (-(stdAddChar (-(j * (u : ZMod D.natAbs))) * chiDMod D j)) * chiDMod_unit_sq u

end Character

end ZInQ.GZFH
