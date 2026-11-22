import ZInQKernel.Contrib.OneProof.CMjDegreeFromRingClass

open scoped UpperHalfPlane
open NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory
namespace HDec.CMBranch.CMjBridges

-- The downstream inequality must accept the order-specific embedding alone.
example {L k : Type} [Field L] [NumberField L] [Field k] [NumberField k]
    (σ : L →+* ℂ) (R : Subring k) (hR : IsImagQuadOrder k R)
    (h : ∀ τ : ℍ, PeriodDiscriminant τ (orderDisc R) →
      ∃ ι : k →+* ℂ,
        letI : Algebra k ℂ := ι.toAlgebra
        Nonempty (ringClassField (FowlerBridges.toOrder R hR) →ₐ[k]
          IntermediateField.adjoin k {modularJ τ}))
    (x : ℂ) (hx : x ∈ Set.range σ) (hd : IsSingularModulusOfDisc x (orderDisc R)) :
    Nat.card (CommRing.Pic R) ≤ Module.finrank ℚ L :=
  card_pic_le_of_ringClass_embedding σ R hR h hx hd

-- Present the two CM inputs independently, then specialize the board type to
-- arbitrary x and O. This checks that the recovered equality uses the input x.
example
    (lower : ∀ (τ : ℍ) (Δ : ℤ), PeriodDiscriminant τ Δ →
      ∀ (k : Type) [Field k] [NumberField k] [IsTotallyComplex k],
        Module.finrank ℚ k = 2 → ∀ O : NumberFieldOrder k, O.discr = Δ →
          ∃ ι : k →+* ℂ,
            letI : Algebra k ℂ := ι.toAlgebra
            Nonempty (ringClassField O →ₐ[k] IntermediateField.adjoin k {modularJ τ}))
    (upper : ∀ (τ : ℍ) (Δ : ℤ), PeriodDiscriminant τ Δ →
      ∀ (k : Type) [Field k] [NumberField k] [IsTotallyComplex k],
        Module.finrank ℚ k = 2 → ∀ O : NumberFieldOrder k, O.discr = Δ →
          ∃ P : Polynomial ℚ, P ≠ 0 ∧ Polynomial.aeval (modularJ τ) P = 0 ∧
            P.natDegree ≤ FowlerBridges.properClassNumber O)
    (x : ℂ) (Δ : ℤ) (hx : IsSingularModulusOfDisc x Δ)
    (k : Type) [Field k] [NumberField k] [IsTotallyComplex k]
    (hk : Module.finrank ℚ k = 2) (O : NumberFieldOrder k) (hd : O.discr = Δ) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = FowlerBridges.properClassNumber O := by
  refine cmjDegreePrint_of_ringClass_and_polynomial ?_ x Δ hx k hk O hd
  intro τ d hτ F _ _ _ hF A hA
  obtain ⟨ι, he⟩ := lower τ d hτ F hF A hA
  obtain ⟨P, hn, hr, hp⟩ := upper τ d hτ F hF A hA
  exact ⟨ι, P, hn, hr, hp, he⟩

end HDec.CMBranch.CMjBridges

#print axioms HDec.CMBranch.CMjBridges.finrank_adjoin_le_rat
#print axioms HDec.CMBranch.CMjBridges.finrank_adjoin_rat_bounds
#print axioms HDec.CMBranch.CMjBridges.properClassNumber_le_rat_degree_of_embedding
#print axioms HDec.CMBranch.CMjBridges.card_pic_le_of_ringClass_embedding
#print axioms HDec.CMBranch.CMjBridges.cmjDegreePrint_of_ringClass_and_polynomial
