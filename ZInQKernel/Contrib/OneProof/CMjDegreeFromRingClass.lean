import ZInQKernel.Contrib.OneProof.CMjBridgesArithmetic
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClass.Field

/-! Conditional degree comparisons for the period and order in DZQ's CM theorems. -/

namespace HDec.CMBranch.CMjBridges

open scoped UpperHalfPlane
open NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory

/-- Extending the base field can only lower the degree of an algebraic element. -/
theorem finrank_adjoin_le_rat {k : Type} [Field k] [Algebra ℚ k]
    [Algebra k ℂ] [IsScalarTower ℚ k ℂ] {x : ℂ} (hx : IsIntegral ℚ x) :
    Module.finrank k (IntermediateField.adjoin k {x}) ≤
      Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) := by
  have hxk : IsIntegral k x := hx.tower_top
  rw [IntermediateField.adjoin.finrank hxk, IntermediateField.adjoin.finrank hx]
  have h := Polynomial.natDegree_le_of_dvd (minpoly.dvd_map_of_isScalarTower ℚ k x)
    (((minpoly.monic hx).map (algebraMap ℚ k)).ne_zero)
  simpa only [Polynomial.natDegree_map] using h

/-- A nonzero rational annihilator bounds the degree from above. -/
theorem finrank_adjoin_rat_bounds {k : Type} [Field k] [Algebra ℚ k]
    [Algebra k ℂ] [IsScalarTower ℚ k ℂ] {x : ℂ} {P : Polynomial ℚ}
    (hP : P ≠ 0) (hx : Polynomial.aeval x P = 0) :
    Module.finrank k (IntermediateField.adjoin k {x}) ≤
      Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) ∧
    Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) ≤ P.natDegree := by
  have hi : IsIntegral ℚ x := (show IsAlgebraic ℚ x from ⟨P, hP, hx⟩).isIntegral
  refine ⟨finrank_adjoin_le_rat (k := k) hi, ?_⟩
  rw [IntermediateField.adjoin.finrank hi]
  exact Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ x hx) hP

/-- Only the embedding into the field of the actual value is needed for the lower bound. -/
theorem properClassNumber_le_rat_degree_of_embedding
    {k : Type} [Field k] [NumberField k] [Algebra k ℂ] [IsScalarTower ℚ k ℂ]
    (hk : Module.finrank ℚ k = 2) (O : NumberFieldOrder k) {x : ℂ}
    (hx : IsIntegral ℚ x) (e : ringClassField O →ₐ[k] IntermediateField.adjoin k {x}) :
    FowlerBridges.properClassNumber O ≤ Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) := by
  letI : FiniteDimensional k (IntermediateField.adjoin k {x}) :=
    IntermediateField.adjoin.finiteDimensional (show IsIntegral k x from hx.tower_top)
  calc
    FowlerBridges.properClassNumber O = Nat.card (Pic O) :=
      Nat.card_congr (FowlerBridges.properIdealClassesEquivClassGroup O hk)
    _ = Module.finrank k (ringClassField O) := (finrank_ringClassField O).symm
    _ ≤ Module.finrank k (IntermediateField.adjoin k {x}) :=
      LinearMap.finrank_le_finrank_of_injective (show Function.Injective e.toLinearMap from e.injective)
    _ ≤ _ := finrank_adjoin_le_rat (k := k) hx

/-- DZQ's Picard-cardinality bound, using only the lower half of the CM comparison.
The input identifies the order and period through the very same discriminant.
Its arithmetic content is the embedding into the simple field of that period. -/
theorem card_pic_le_of_ringClass_embedding
    {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ)
    {k : Type} [Field k] [NumberField k] (R : Subring k) (hR : IsImagQuadOrder k R)
    (hCM : ∀ (τ : ℍ), PeriodDiscriminant τ (orderDisc R) →
      ∃ ι : k →+* ℂ,
        letI : Algebra k ℂ := ι.toAlgebra
        Nonempty (ringClassField (FowlerBridges.toOrder R hR) →ₐ[k]
          IntermediateField.adjoin k {modularJ τ}))
    {x : ℂ} (hx : x ∈ Set.range σ) (hDisc : IsSingularModulusOfDisc x (orderDisc R)) :
    Nat.card (CommRing.Pic R) ≤ Module.finrank ℚ L := by
  obtain ⟨τ, rfl, hτ⟩ := hDisc
  obtain ⟨ι, ⟨e⟩⟩ := hCM τ hτ
  letI : Algebra k ℂ := ι.toAlgebra
  letI : IsScalarTower ℚ k ℂ := IsScalarTower.of_algebraMap_eq fun q => by
    simp [RingHom.algebraMap_toAlgebra]
  have hi : IsIntegral ℚ (modularJ τ) := by
    obtain ⟨y, hy⟩ := hx
    let f : L →ₐ[ℚ] ℂ := { σ with commutes' := σ.map_rat_algebraMap }
    rw [← hy]
    exact IsIntegral.map f (IsIntegral.of_finite ℚ y)
  rw [FowlerBridges.card_pic_eq_properClassNumber R hR]
  exact (properClassNumber_le_rat_degree_of_embedding hR.2.1 _ hi e).trans
    (degree_le_of_mem_range σ hx)

/-- A lower embedding and a nonzero rational annihilator for the same modular j
give the exact printed degree. Both CM inputs remain explicit. -/
theorem cmjDegreePrint_of_ringClass_and_polynomial
    (h : ∀ (τ : ℍ) (Δ : ℤ), PeriodDiscriminant τ Δ →
      ∀ (k : Type) [Field k] [NumberField k] [IsTotallyComplex k],
        Module.finrank ℚ k = 2 → ∀ (O : NumberFieldOrder k), O.discr = Δ →
          ∃ (σ : k →+* ℂ) (P : Polynomial ℚ), P ≠ 0 ∧
            Polynomial.aeval (modularJ τ) P = 0 ∧
            P.natDegree ≤ FowlerBridges.properClassNumber O ∧
            (letI : Algebra k ℂ := σ.toAlgebra
             Nonempty (ringClassField O →ₐ[k] IntermediateField.adjoin k {modularJ τ}))) :
    CMjDegreePrint := by
  rintro x Δ ⟨τ, rfl, hτ⟩ k _ _ _ hk O hO
  obtain ⟨σ, P, hP, hroot, hdegree, ⟨e⟩⟩ := h τ Δ hτ k hk O hO
  letI : Algebra k ℂ := σ.toAlgebra
  letI : IsScalarTower ℚ k ℂ := IsScalarTower.of_algebraMap_eq fun q => by
    simp [RingHom.algebraMap_toAlgebra]
  have hi : IsIntegral ℚ (modularJ τ) :=
    (show IsAlgebraic ℚ (modularJ τ) from ⟨P, hP, hroot⟩).isIntegral
  have upper := (finrank_adjoin_rat_bounds (k := k) hP hroot).2
  exact le_antisymm (upper.trans hdegree)
    (properClassNumber_le_rat_degree_of_embedding hk O hi e)

end HDec.CMBranch.CMjBridges
