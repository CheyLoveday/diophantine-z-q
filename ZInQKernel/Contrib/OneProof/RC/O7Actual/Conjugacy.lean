import ZInQKernel.Contrib.OneProof.RC.O7Actual.Embeddings

/-! The rational conjugation used before counting the finite adelic fibers. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O7Actual

open Eichler Visibility

/-- On-the-spot (c), tex 9149–9160: two nonzero trace-zero rational
quaternions of the same norm are conjugate in the definite algebra.
An intertwiner is obtained by taking a nonzero `q*x + y*q`. -/
theorem rational_conjugacy {a b : ℚ} (ha : a < 0) (hb : b < 0)
    {x y : B a b} (hx : x.re = 0) (hy : y.re = 0) (hx₀ : x ≠ 0)
    (hn : nrd x = nrd y) :
    ∃ u : (B a b)ˣ, (u : B a b) * x * (↑u⁻¹ : B a b) = y := by
  have hex : ∃ q : B a b, q * x + y * q ≠ 0 := by
    by_contra! h
    have hneg : y = -x := eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using h 1)
    have hc (q : B a b) : q * x = x * q := by
      have hq := h q
      rwa [hneg, neg_mul, ← sub_eq_add_neg, sub_eq_zero] at hq
    let i : B a b := ⟨0, 1, 0, 0⟩
    let j : B a b := ⟨0, 0, 1, 0⟩
    have himI : x.imI = 0 := by
      have hI := congrArg QuaternionAlgebra.imK (hc j)
      simp [j, QuaternionAlgebra.imK_mul] at hI
      linarith
    have himJ : x.imJ = 0 := by
      have hJ := congrArg QuaternionAlgebra.imK (hc i)
      simp [i, QuaternionAlgebra.imK_mul] at hJ
      linarith
    have himK : x.imK = 0 := by
      have hK := congrArg QuaternionAlgebra.imJ (hc i)
      simp [i, QuaternionAlgebra.imJ_mul] at hK
      exact (mul_eq_zero.mp (show a * x.imK = 0 by linarith)).resolve_left ha.ne
    exact hx₀ (QuaternionAlgebra.ext hx himI himJ himK)
  obtain ⟨q, hq⟩ := hex
  let u := unitOfNeZero ha hb (q * x + y * q) hq
  have hx' : x * x = algebraMap ℚ (B a b) (-nrd x) := by
    rw [map_neg, algebraMap_nrd_of_re_eq_zero hx, neg_neg]
  have hy' : y * y = algebraMap ℚ (B a b) (-nrd x) := by
    rw [hn, map_neg, algebraMap_nrd_of_re_eq_zero hy, neg_neg]
  have hi : (u : B a b) * x = y * (u : B a b) := by
    change (q * x + y * q) * x = y * (q * x + y * q)
    rw [add_mul, mul_add, mul_assoc q x x, ← mul_assoc y y q, mul_assoc y q x, hx', hy',
      Algebra.commutes, add_comm]
  exact ⟨u, by rw [hi, mul_assoc, Units.mul_inv, mul_one]⟩

end ZInQ.Manuscript.RC.O7Actual
