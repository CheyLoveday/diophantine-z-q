import ZInQKernel.Contrib.OneProof.RC.O7Actual.Family
import ZInQKernel.Contrib.OneProof.RC.ExplicitSplit.Ramification
import Mathlib.Algebra.QuadraticAlgebra.BaseChange
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-! Check the two local hypotheses of the manuscript's rational embedding
citation. The cited implication itself remains the existing GLUE. -/

noncomputable section

open scoped TensorProduct

namespace ZInQ.Manuscript.RC.O7Orbits

open Eichler O7Actual

/-- Tex 9206–9208: the two detecting-prime symbols combine to make
the quadratic discriminant a nonsquare in the residue field. -/
theorem detecting_nonsquare {ell : ℕ} [Fact ell.Prime] {D hstar : ℤ}
    (hD : legendreSym ell D = 1) (hh : legendreSym ell hstar = -1) :
    ¬ IsSquare ((D * hstar : ℤ) : ZMod ell) := by
  apply (legendreSym.eq_neg_one_iff ell).mp
  rw [legendreSym.mul, hD, hh, one_mul]

/-- A residue nonsquare cannot be the square of a rational local element:
a putative square root of an integral element is itself integral. -/
theorem padic_nonsquare_of_residue {p : ℕ} [Fact p.Prime] {d : ℤ}
    (hd : ¬ IsSquare (d : ZMod p)) : ¬ IsSquare (d : ℚ_[p]) := by
  rintro ⟨a, ha⟩
  have hn : ‖a‖ ≤ 1 := by
    have h := (d : ℤ_[p]).property
    change ‖(d : ℚ_[p])‖ ≤ 1 at h
    rw [ha, norm_mul] at h
    nlinarith [norm_nonneg a]
  let a' : ℤ_[p] := ⟨a, hn⟩
  have h : (d : ℤ_[p]) = a' * a' := by
    apply Subtype.ext
    exact ha
  exact hd ⟨PadicInt.toZMod a', by
    simpa only [map_intCast, map_mul] using congrArg PadicInt.toZMod h⟩

/-- In the chosen quadratic model, a nonsquare after extending scalars
makes the scalar extension a field. -/
theorem tensor_isField_of_nonsquare (K : Type*) [Field K] [Algebra ℚ K] [CharZero K]
    {F : Type*} [Field F] [NumberField F] {d : ℤ} (Q : QuadraticBasis F d)
    (hd : ¬ IsSquare (d : K)) : IsField (K ⊗[ℚ] F) := by
  let e := (Algebra.TensorProduct.congr (S := K) (AlgEquiv.refl : K ≃ₐ[K] K) Q.model.symm).trans
    (QuadraticAlgebra.baseChangeEquiv K (d : ℚ) 0)
  have hn : ¬ IsSquare (algebraMap ℚ K (d : ℚ)) := by simpa only [map_intCast] using hd
  let _ : Fact (¬ IsSquare (algebraMap ℚ K (d : ℚ))) := ⟨hn⟩
  have h : IsField (QuadraticAlgebra K (algebraMap ℚ K (d : ℚ)) 0) := Field.toIsField _
  have he : IsField (QuadraticAlgebra K (algebraMap ℚ K (d : ℚ)) (algebraMap ℚ K 0)) := by
    rw [map_zero]
    exact h
  exact e.toRingEquiv.toMulEquiv.isField he

/-- Tex 9149–9155: use the existing Voight implication with the actual
ramification of the explicit algebra, negativity at infinity, and the
product of the two detecting-prime Legendre symbols. -/
theorem exists_reference_embedding {ell : ℕ} [Fact ell.Prime] (hell : ell % 4 = 3)
    {F : Type*} [Field F] [NumberField F] {D hstar : ℤ} (Q : QuadraticBasis F (D * hstar))
    (hd : D * hstar < 0) (hD : legendreSym ell D = 1) (hh : legendreSym ell hstar = -1)
    (voight : Voight1467VToIII ell F) :
    Nonempty (F →ₐ[ℚ] B (-1) (-(ell : ℚ))) := by
  have hneg : ((D * hstar : ℤ) : ℝ) < 0 := by exact_mod_cast hd
  have hreal : ¬ IsSquare ((D * hstar : ℤ) : ℝ) := by
    rintro ⟨a, ha⟩
    exact hneg.not_ge (ha ▸ mul_self_nonneg a)
  exact voight (ExplicitSplit.explicit_ramifiedExactlyAtEll0Infty Fact.out hell)
    (tensor_isField_of_nonsquare ℝ Q hreal)
    (tensor_isField_of_nonsquare ℚ_[ell] Q
      (padic_nonsquare_of_residue (detecting_nonsquare hD hh)))

end ZInQ.Manuscript.RC.O7Orbits
