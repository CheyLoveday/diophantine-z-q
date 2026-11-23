import ZInQKernel.Contrib.OneProof.RC.HCMV21.AdelicTorsor
import ZInQKernel.Contrib.OneProof.RC.HCMV21.AnalyticTorsor
import ZInQKernel.Contrib.OneProof.RC.HCMV21.QuotientComparison

/-! The correspondence for the concrete analytic class set and the finite
adelic orbit, conditional on the prime-to-level geometric comparison. -/

namespace ZInQ.Manuscript.RC.HCMV21

open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open scoped NumberField nonZeroDivisors

section Orbit

variable {R F G : Type*} [CommRing R] [IsDedekindDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F] [Group G]
  (j : 𝔸ᶠ[R, F]ˣ →* G) (U : Subgroup G) (z : G)
  (hunit : ∀ s : 𝔸ᶠ[R, F]ˣ, z⁻¹ * j s * z ∈ U ↔ s ∈ integralUnits R F)

/-- The class group acts on the finite adelic orbit by left multiplication
of its torus representatives. -/
@[instance_reducible]
noncomputable def adelicOrbitAction : MulAction (ClassGroup R) (Set.range (torusOrbitMap j U z)) where
  smul c w := (adelicOrbitEquivClassGroup j U z hunit).symm (c * adelicOrbitEquivClassGroup j U z hunit w)
  one_smul w := by
    let e := adelicOrbitEquivClassGroup j U z hunit
    change e.symm (1 * e w) = w
    rw [one_mul, Equiv.symm_apply_apply]
  mul_smul c d w := by
    let e := adelicOrbitEquivClassGroup j U z hunit
    change e.symm ((c * d) * e w) = e.symm (c * e (e.symm (d * e w)))
    rw [Equiv.apply_symm_apply, mul_assoc]

/-- The action really is left multiplication by the image of a finite
idele when that idele is chosen as a class representative. -/
theorem adelicOrbitAction_smul_idele (s t : 𝔸ᶠ[R, F]ˣ) :
    letI := adelicOrbitAction j U z hunit
    toClassGroup R F s •
      (⟨torusOrbitMap j U z t, ⟨t, rfl⟩⟩ : Set.range (torusOrbitMap j U z)) =
      ⟨torusOrbitMap j U z (s * t), ⟨s * t, rfl⟩⟩ := by
  let e := adelicOrbitEquivClassGroup j U z hunit
  apply e.injective
  change e (e.symm (toClassGroup R F s * e ⟨torusOrbitMap j U z t, ⟨t, rfl⟩⟩)) = _
  rw [Equiv.apply_symm_apply]
  simp only [e, adelicOrbitEquivClassGroup_apply, map_mul]

/-- Free and transitive independently of any CM reduction map. -/
theorem adelicOrbitAction_bijective (w : Set.range (torusOrbitMap j U z)) :
    letI := adelicOrbitAction j U z hunit
    Function.Bijective (fun c : ClassGroup R => c • w) := by
  let e := adelicOrbitEquivClassGroup j U z hunit
  exact e.symm.bijective.comp (Equiv.mulRight (e w)).bijective

end Orbit

/-- Once the geometric reduction is identified in the selected adelic
orbit, a comparison at coprime ideal representatives discharges the
equivariant bijection. Neither orbit is assumed bijective as an input. -/
theorem orientedCorrespondence_to_adelicOrbit {F G : Type*} [Field F] [NumberField F] [Group G]
    (j : 𝔸ᶠ[𝓞 F, F]ˣ →* G) (U : Subgroup G) (z : G)
    (hunit : ∀ s : 𝔸ᶠ[𝓞 F, F]ˣ, z⁻¹ * j s * z ∈ U ↔ s ∈ integralUnits (𝓞 F) F)
    (red : IdealLatticeClass (𝓞 F) F → Set.range (torusOrbitMap j U z))
    (x₀ : IdealLatticeClass (𝓞 F) F) (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (he : letI := adelicOrbitAction j U z hunit
      ∀ (a : (Ideal (𝓞 F))⁰), IsCoprime (a : Ideal (𝓞 F)) m →
        red (ClassGroup.mk0 a • x₀) = ClassGroup.mk0 a • red x₀) :
    letI := adelicOrbitAction j U z hunit
    OrientedCorrespondence (C := ClassGroup (𝓞 F)) red := by
  letI := adelicOrbitAction j U z hunit
  exact orientedCorrespondence_of_primeTo_representatives red x₀ (analytic_orbit_bijective x₀)
    (adelicOrbitAction_bijective j U z hunit (red x₀)) m hm he

end ZInQ.Manuscript.RC.HCMV21
