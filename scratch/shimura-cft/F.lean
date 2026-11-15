
/-! # Part D: the hypotheses of the reciprocity clause can be met (for either value of `δ`)

`K = ℚ(√−3)` (the kernel's `QNeg 3`), `q : √−3 ↦ j` (`j² = −3` in `B = (2, −3)`), `κ : √−3 ↦ i√3`, and
`z = i√3`, the fixed point of `ι(j) = [[0, −3], [1, 0]]`. -/

noncomputable section

namespace ShimuraCFT

open ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZGenus.Shimura Complex NumberField

/-- `j ∈ B` as a root of `X² + 3`. -/
def jRoot : {u : LeafQM.B // u * u = (-((3 : ℕ) : ℚ)) • (1 : LeafQM.B) + (0 : ℚ) • u} :=
  ⟨⟨0, 0, 1, 0⟩, by ext <;> simp⟩

/-- `q : ℚ(√−3) → B`, `√−3 ↦ j`. -/
def q3 : QNeg 3 →ₐ[ℚ] LeafQM.B := QuadraticAlgebra.lift jRoot

theorem q3_apply (a : QNeg 3) : q3 a = ⟨a.re, 0, a.im, 0⟩ := by
  ext <;> simp [q3, jRoot, Rat.smul_def]

/-- `z₃ = i√3 ∈ ℍ`. -/
def z3 : UpperHalfPlane := ⟨I * Real.sqrt 3, by simp⟩

theorem sq_I_sqrt3 : (I * (Real.sqrt 3 : ℂ)) * (I * Real.sqrt 3) = -3 := by
  have := sqrt_mul_self_C 3
  push_cast at this
  rw [show I * (Real.sqrt 3 : ℂ) * (I * Real.sqrt 3) = (I * I) * (Real.sqrt 3 * Real.sqrt 3) by ring,
    I_mul_I, this]; ring

/-- **`z₃` is the CM point of `q₃` with reflex embedding `κ = kappaAlg 3`.** -/
theorem isCMPoint_q3 : IsCMPoint q3 ((kappaAlg 3 : QNeg 3 →ₐ[ℚ] ℂ) : QNeg 3 →+* ℂ) z3 := by
  intro a
  have h := sq_I_sqrt3
  rw [q3_apply]
  ext i
  fin_cases i <;>
    simp [BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, z3, kappaAlg_apply, kappa] <;>
    linear_combination (↑a.im : ℂ) * h

instance : IsTotallyComplex (QNeg 3) :=
  ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.1 (T5Glue.not_isReal_QNeg 3 w)⟩

/-- **The reciprocity clause is not vacuous**: for either value of `δ` there is an imaginary
quadratic `K`, `κ`, `q` and a CM point `z` meeting its hypothesis, and every `σ ∈ Aut(ℂ)` fixing
`κ(K)` is `[s, K]` on `K^ab` for some idele `s`. -/
theorem recip_hyp_nonempty (δ : Bool) :
    ∃ (κ : QNeg 3 →+* ℂ) (q : QNeg 3 →ₐ[ℚ] LeafQM.B) (z : UpperHalfPlane),
      Module.finrank ℚ (QNeg 3) = 2 ∧
      IsCMPoint q (if δ then κ else (starRingEnd ℂ).comp κ) z ∧
      ∀ σ : ℂ ≃+* ℂ, (∀ k, σ (κ k) = κ k) → ∃ s : IdeleGroup (𝓞 (QNeg 3)) (QNeg 3),
        ArtinCondC κ σ s := by
  refine ⟨if δ then (kappaAlg 3 : QNeg 3 →+* ℂ) else (starRingEnd ℂ).comp (kappaAlg 3 : QNeg 3 →+* ℂ),
    q3, z3, QuadraticAlgebra.finrank_eq_two _ _, ?_, fun σ hσ => exists_artinCondC _ σ hσ⟩
  cases δ
  · simp only [Bool.false_eq_true, if_false]
    have : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp (kappaAlg 3 : QNeg 3 →+* ℂ)) =
        (kappaAlg 3 : QNeg 3 →+* ℂ) := by ext x; simp
    rw [this]; exact isCMPoint_q3
  · simpa using isCMPoint_q3

end ShimuraCFT

#print axioms ShimuraCFT.recip_hyp_nonempty
