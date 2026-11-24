import ZInQKernel.Contrib.OneProof.RC.HCMV21.AdelicCorrespondence

/-! Assemble the comparison in the covariant Hom convention. The
geometric input is still needed to read the right-ideal generator of
each prime-to-level quotient at the reference point. -/

namespace ZInQ.Manuscript.RC.HCMV21

open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open scoped NumberField nonZeroDivisors

section FiniteOrbit

variable {F G : Type*} [Field F] [NumberField F] [Group G]
  (j : 𝔸ᶠ[𝓞 F, F]ˣ →* G) (U : Subgroup G) (z : G)
  (hunit : ∀ s : 𝔸ᶠ[𝓞 F, F]ˣ,
    z⁻¹ * j s * z ∈ U ↔ s ∈ integralUnits (𝓞 F) F)

local notation "X" => Set.range (torusOrbitMap j U z)
local notation "ClG" => ClassGroup (𝓞 F)

/-- In covariant Hom coordinates the class of `a` acts by the inverse
of the finite idele representing `a`. -/
@[instance_reducible]
noncomputable def inverseAdelicOrbitAction : MulAction ClG X := by
  letI := adelicOrbitAction j U z hunit
  exact {
    smul := fun c x => c⁻¹ • x
    one_smul := fun x => by
      change (1 : ClG)⁻¹ • x = x
      rw [inv_one, one_smul]
    mul_smul := fun c d x => by
      change (c * d)⁻¹ • x = c⁻¹ • (d⁻¹ • x)
      rw [mul_inv, mul_smul] }

/-- The inverse convention does not change the regularity of the action. -/
theorem inverseAdelicOrbitAction_bijective (x : X) :
    letI := inverseAdelicOrbitAction j U z hunit
    Function.Bijective (fun c : ClG => c • x) :=
  (adelicOrbitAction_bijective j U z hunit x).comp (Equiv.inv ClG).bijective

/-- Conditional comparison from actual quotient reads at the reference.
The premises are a coordinate for the reference and the individual
right-ideal calculations on integral coprime representatives; neither
premise asserts any surjectivity. -/
theorem orientedCorrespondence_of_inverseReferenceReads
    (red : IdealLatticeClass (𝓞 F) F → X) (x₀ : IdealLatticeClass (𝓞 F) F)
    (h₀ : (red x₀).val = torusOrbitMap j U z 1)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (hread : ∀ a : (Ideal (𝓞 F))⁰, IsCoprime (a : Ideal (𝓞 F)) m →
      ∃ s : 𝔸ᶠ[𝓞 F, F]ˣ, toFractionalIdeal s = FractionalIdeal.mk0 F a ∧
        (red (ClassGroup.mk0 a • x₀)).val = torusOrbitMap j U z s⁻¹) :
    letI := inverseAdelicOrbitAction j U z hunit
    OrientedCorrespondence (C := ClG) red := by
  let := inverseAdelicOrbitAction j U z hunit
  apply orientedCorrespondence_of_primeTo_representatives red x₀ (analytic_orbit_bijective x₀)
    (inverseAdelicOrbitAction_bijective j U z hunit (red x₀)) m hm
  intro a ha
  obtain ⟨s, hs, hread⟩ := hread a ha
  have hc : toClassGroup (𝓞 F) F s = ClassGroup.mk0 a := by
    change ClassGroup.mk F (toFractionalIdeal s) = _
    rw [hs, ClassGroup.mk_mk0]
  have hr : red x₀ = (⟨torusOrbitMap j U z 1, ⟨1, rfl⟩⟩ : X) := Subtype.ext h₀
  change red (ClassGroup.mk0 a • x₀) =
    @SMul.smul ClG X (adelicOrbitAction j U z hunit).toSMul (ClassGroup.mk0 a)⁻¹ (red x₀)
  have h := adelicOrbitAction_smul_idele j U z hunit s⁻¹ 1
  rw [map_inv, hc, mul_one, ← hr] at h
  exact (Subtype.ext hread).trans h.symm

end FiniteOrbit

/-- Inversion in a pointwise class comparison cancels in the weighted
sum when the weight is a quadratic character. -/
theorem sum_mul_inv_eq_of_invariant {C S : Type*} [Group C] [Fintype C] [Semiring S]
    (χ f : C → S) (hχ : ∀ c, χ c⁻¹ = χ c) :
    ∑ c, χ c * f c⁻¹ = ∑ c, χ c * f c := by
  apply Fintype.sum_equiv (Equiv.inv C)
  intro c
  change χ c * f c⁻¹ = χ c⁻¹ * f c⁻¹
  rw [hχ]

end ZInQ.Manuscript.RC.HCMV21
