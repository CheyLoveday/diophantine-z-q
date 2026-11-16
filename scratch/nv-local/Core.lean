import ZInQKernel.Contrib.OneProof.SGRDirectNV

open NumberField

set_option linter.style.haveILetI false

namespace NVLocal

/-- **An inertia automorphism at an unramified prime is trivial.** -/
theorem eq_one_of_inertia_of_unram {K : Type*} [Field K] [NumberField K] (P : Ideal (𝓞 K))
    [P.IsPrime] (hun : P.ramificationIdx ℤ = 1) (σ : K ≃ₐ[ℚ] K)
    (hσ : ∀ x : 𝓞 K, σ • x - x ∈ P) : σ = 1 := by
  set G := Subgroup.zpowers σ
  haveI : Finite G := inferInstance
  set K₀ := FixedPoints.subfield G K
  haveI : CharZero K₀ := inferInstance
  haveI : FiniteDimensional ℚ K₀ := by
    exact Module.Finite.of_injective ((algebraMap K₀ K).toRatAlgHom.toLinearMap)
      (algebraMap K₀ K).injective
  haveI : NumberField K₀ := ⟨⟩
  haveI : FaithfulSMul G K := ⟨fun {g₁ g₂} h => Subtype.ext (AlgEquiv.ext h)⟩
  haveI : IsGaloisGroup G K₀ K := IsGaloisGroup.fixedPoints G K
  haveI : IsGaloisGroup G (𝓞 K₀) (𝓞 K) := IsGaloisGroup.of_isFractionRing G (𝓞 K₀) (𝓞 K) K₀ K
  set P₀ := P.under (𝓞 K₀)
  haveI : P₀.IsPrime := Ideal.IsPrime.under _ P
  haveI : P.LiesOver P₀ := ⟨rfl⟩
  have hg : (⟨σ, Subgroup.mem_zpowers σ⟩ : G) ∈ P.inertia G := by
    intro x
    exact hσ x
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := G) P₀ P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx P₀ P G] at hcard
  have htow := Ideal.ramificationIdx_tower (R := ℤ) P₀ P
  rw [hun] at htow
  have h1 : P.ramificationIdx (𝓞 K₀) = 1 := (Nat.eq_one_of_mul_eq_one_left htow.symm)
  rw [h1] at hcard
  have : (⟨σ, Subgroup.mem_zpowers σ⟩ : G) = 1 := by
    have hb : P.inertia G = ⊥ := Subgroup.card_eq_one.mp hcard
    rw [hb] at hg
    exact hg
  exact congrArg Subtype.val this

end NVLocal
