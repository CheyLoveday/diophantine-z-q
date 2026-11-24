import ZInQKernel.Contrib.OneProof.RC.HCMV21.Correspondence
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ClassRepresentatives
import ZInQKernel.Contrib.OneProof.RC.HCMV21.IdealLattice
import Mathlib.LinearAlgebra.Isomorphisms

/-! An ideal quotient commutes with specialization once its specialized
kernel is identified, and checking prime-to-modulus representatives suffices
for the equivariance test. -/

namespace ZInQ.Manuscript.RC.HCMV21

open NumberField
open scoped nonZeroDivisors

variable {R M P Q : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

/-- Two surjective labelled maps with the same kernel give the same
quotient module under a unique isomorphism over the source. This is the
point-module calculation; a geometric identification still needs the
finite étale scheme quotient. -/
theorem existsUnique_quotientCompare (f : M →ₗ[R] P) (g : M →ₗ[R] Q)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : LinearMap.ker f = LinearMap.ker g) :
    ∃! e : P ≃ₗ[R] Q, ∀ x, e (f x) = g x := by
  let e := (f.quotKerEquivOfSurjective hf).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (g.quotKerEquivOfSurjective hg))
  have he (x : M) : e (f x) = g x := by
    have hf' : (f.quotKerEquivOfSurjective hf).symm (f x) = Submodule.Quotient.mk x :=
      (LinearEquiv.symm_apply_eq _).mpr (f.quotKerEquivOfSurjective_apply_mk hf x).symm
    simp only [e, LinearEquiv.trans_apply, hf', Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
  refine ⟨e, he, ?_⟩
  intro e' he'
  ext y
  obtain ⟨x, rfl⟩ := hf y
  exact (he' x).trans (he x).symm

/-- Check the conjugate-reduction square on integral ideals coprime to a
chosen nonzero modulus (in the application supported on `qN`). With the
two orbit calculations supplied independently, this proves the full
correspondence. -/
theorem orientedCorrespondence_of_primeTo_representatives
    {F : Type*} [Field F] [NumberField F] {X Y : Type*}
    [MulAction (ClassGroup (𝓞 F)) X] [MulAction (ClassGroup (𝓞 F)) Y]
    (red : X → Y) (x₀ : X)
    (hx : Function.Bijective (fun a : ClassGroup (𝓞 F) => a • x₀))
    (hy : Function.Bijective (fun a : ClassGroup (𝓞 F) => a • red x₀))
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (he : ∀ (a : (Ideal (𝓞 F))⁰), IsCoprime (a : Ideal (𝓞 F)) m →
      red (ClassGroup.mk0 a • x₀) = ClassGroup.mk0 a • red x₀) :
    OrientedCorrespondence (C := ClassGroup (𝓞 F)) red := by
  have h₀ (a : ClassGroup (𝓞 F)) : red (a • x₀) = a • red x₀ := by
    obtain ⟨I, hI, rfl⟩ := exists_integral_class_prime_to m hm a
    exact he I hI
  apply orientedCorrespondence_of_orbit_maps red x₀ hx hy
  intro a x
  obtain ⟨b, rfl⟩ := hx.surjective x
  rw [← mul_smul, h₀, mul_smul, h₀]

end ZInQ.Manuscript.RC.HCMV21
