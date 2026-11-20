import Mathlib

/-!
# The spectral valuation on an algebraic closure of a complete nonarchimedean field

For a complete nontrivially normed nonarchimedean field `K`, the spectral norm of Mathlib is a
multiplicative ultrametric norm on an algebraic closure `\bar K` extending the norm of `K`, and it
is invariant under `Gal(\bar K / K)`. Packaged as a valuation with values in `ℝ≥0` it is the
unique extension of the absolute value of `K` (Milne, *Algebraic Number Theory*, v3.08,
Thm. 7.38, p. 123 and Cor. 7.40, p. 124; Lang, *Algebraic Number Theory*, Ch. II, §2). Its
valuation subring is therefore stable under the whole Galois group, so the decomposition group of
this place is everything.

This file also records the elementwise description of the inertia subgroup of a valuation subring
(Mathlib `ValuationSubring.inertiaSubgroup`): an element of the decomposition group lies in the
inertia subgroup exactly when it acts trivially on the residue field.

## Classification

Definitions and PROVED statements only; no hypotheses are assumed.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.DecompositionGlue

open scoped NNReal Pointwise

section Inertia

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- **PROVED**, membership in the non-units of the valuation subring of a valuation. Locator:
Mathlib `ValuationSubring.mem_nonunits_iff_or`. -/
theorem mem_valuationSubring_nonunits_iff {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation E Γ) {x : E} : x ∈ w.valuationSubring.nonunits ↔ w x < 1 := by
  rw [ValuationSubring.mem_nonunits_iff_or, Valuation.mem_valuationSubring_iff, map_inv₀, not_le]
  constructor
  · rintro (rfl | h)
    · rw [map_zero]
      exact zero_lt_one
    · have h0 : w x ≠ 0 := fun h0 => by rw [h0, inv_zero] at h; exact absurd h (not_lt.2 zero_le)
      exact (one_lt_inv₀ (zero_lt_iff.2 h0)).1 h
  · intro h
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr ((one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx))).2 h)

/-- **PROVED**, the elementwise description of the inertia subgroup: an element `s` of the
decomposition group of `A` lies in the inertia subgroup iff `s x - x` is a non-unit of `A` for
every `x ∈ A`. Locator: Mathlib `ValuationSubring.inertiaSubgroup` (the kernel of the action on
the residue field) and `IsLocalRing.ResidueField.residue_smul`. -/
theorem mem_inertiaSubgroup_iff (A : ValuationSubring E) (s : A.decompositionSubgroup F) :
    s ∈ A.inertiaSubgroup F ↔ ∀ x ∈ A, (s : E ≃ₐ[F] E) x - x ∈ A.nonunits := by
  have key : ∀ a : A, IsLocalRing.residue A (s • a) = IsLocalRing.residue A a ↔
      (s : E ≃ₐ[F] E) (a : E) - (a : E) ∈ A.nonunits := by
    intro a
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff, ← ValuationSubring.mem_nonunits_iff]
    rfl
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  constructor
  · intro h x hx
    rw [← key ⟨x, hx⟩, IsLocalRing.ResidueField.residue_smul]
    have := congrArg (fun φ : IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A =>
      φ (IsLocalRing.residue A ⟨x, hx⟩)) h
    exact this
  · intro h
    ext r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    change s • IsLocalRing.residue A a = IsLocalRing.residue A a
    rw [← IsLocalRing.ResidueField.residue_smul, key]
    exact h a a.2

end Inertia

section Spectral

variable (K : Type*) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- **DEFINITION**, the spectral valuation on `\bar K`: the spectral norm, as a valuation with
values in `ℝ≥0`. Locator: Mathlib `spectralNorm`, `spectralAlgNorm_mul`,
`isNonarchimedean_spectralNorm`; Milne, Thm. 7.38, p. 123 and Cor. 7.40, p. 124. -/
def spectralValuation : Valuation (AlgebraicClosure K) ℝ≥0 where
  toFun x := (spectralNorm K (AlgebraicClosure K) x).toNNReal
  map_zero' := by simp [spectralNorm_zero]
  map_one' := by simp [spectralNorm_one]
  map_mul' x y := by
    rw [← Real.toNNReal_mul (spectralNorm_nonneg x)]
    exact congrArg Real.toNNReal (spectralAlgNorm_mul x y)
  map_add_le_max' x y :=
    (Real.toNNReal_le_toNNReal (isNonarchimedean_spectralNorm x y)).trans_eq
      (Monotone.map_max fun _ _ h => Real.toNNReal_mono h)

/-- **PROVED**, the spectral valuation is the spectral norm. Locator: definition. -/
theorem coe_spectralValuation (x : AlgebraicClosure K) :
    (spectralValuation K x : ℝ) = spectralNorm K (AlgebraicClosure K) x :=
  Real.coe_toNNReal _ (spectralNorm_nonneg x)

/-- **PROVED**, the spectral valuation extends the norm of `K`. Locator: Mathlib
`spectralNorm_extends`. -/
theorem spectralValuation_algebraMap (k : K) :
    (spectralValuation K (algebraMap K (AlgebraicClosure K) k) : ℝ) = ‖k‖ :=
  (coe_spectralValuation K _).trans (spectralNorm_extends k)

/-- **PROVED**, the spectral valuation is invariant under `Gal(\bar K / K)`. Locator: Mathlib
`spectralNorm_eq_of_equiv`. -/
theorem spectralValuation_galois (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : AlgebraicClosure K) : spectralValuation K (σ x) = spectralValuation K x :=
  NNReal.eq <| by rw [coe_spectralValuation, coe_spectralValuation, spectralNorm_eq_of_equiv σ x]

/-- **PROVED**, every element of `Gal(\bar K / K)` lies in the decomposition group of the
spectral place. Locator: `spectralValuation_galois`. -/
theorem mem_decompositionSubgroup_spectral (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    σ ∈ (spectralValuation K).valuationSubring.decompositionSubgroup K := by
  refine MulAction.mem_stabilizer_iff.2 (SetLike.ext fun x => ?_)
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff,
    spectralValuation_galois]

end Spectral

end ZInQ.Contrib.RC53Assist.DecompositionGlue
