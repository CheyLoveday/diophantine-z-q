import ZInQKernel.OneProof.H.TailE
import ZInQKernel.OneProof.H.TailQ
import ZInQKernel.Contrib.AVB1.AlgClosed

/-!
# homfree-proof: Mumford §19 Thm 3 for abelian varieties over fields that embed into `ℂ`

From the bundle fields `uniformizationLeafAll` (AN3, `A(ℂ) ≅ ℂ^g/Λ`) and `mumfordTorsionAlgClosed`
(Mumford §4 App. 2 (iv)) only.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

namespace ZInQ.Contrib.OneProof.HomFreeC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ZInQ.LeafPush2 (CPts IsUniformization)

variable {K : Type} [Field K]

/-! ## 1. A homomorphism killing all complex points is zero -/

/-- **A homomorphism of abelian varieties over `K` that is trivial on `A(ℂ)_σ` is zero (proved).**
Base change to `ℂ` along `σ` (`bcHom` is injective), then Mathlib's `ext_of_apply_eq` over `ℂ`
(hom-unify's `hom_ext_of_cpts`). -/
theorem hom_eq_zero_of_cpts (σ : K →+* ℂ) {A B : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom A B)
    (h : ∀ p : CPts A σ, p ≫ f.hom = 1) : f = 0 := by
  letI : Algebra K ℂ := σ.toAlgebra
  have hC : ZInQ.Contrib.AVB1.bcHom ℂ A B f = 0 := by
    apply PkgI3.AbVar.Hom.ext'
    apply ZInQ.HomUnify.hom_ext_of_cpts
    intro q
    rw [PkgI3.AbVar.Hom.hom_zero, MonObj.comp_one]
    have h1 := ZInQ.Contrib.AVB1.bcPt_ptMap (A := A) (B := B) ℂ f q
    have h2 : PkgI3.AbVar.ptMap f (ZInQ.Contrib.AbVarBC.bcPt A ℂ q) = 1 :=
      h (ZInQ.Contrib.AbVarBC.bcPt A ℂ q)
    rw [h2] at h1
    have h3 : PkgI3.AbVar.ptMap (ZInQ.Contrib.AVB1.bcHom ℂ A B f) q = 1 :=
      (MulEquiv.map_eq_one_iff _).1 h1
    exact h3
  apply ZInQ.Contrib.AVB1.bcHom_injective (L := ℂ) A B
  rw [hC, map_zero]

/-! ## 2. Linear lifts are unique, additive, and determine the homomorphism -/

section Lift

variable {σ : K →+* ℂ} {A B : PkgI3.AbVar K} {g h : ℕ}
  {ΛA : Submodule ℤ (Fin g → ℂ)} {ΛB : Submodule ℤ (Fin h → ℂ)}
  {ΦA : (Fin g → ℂ) → CPts A σ} {ΦB : (Fin h → ℂ) → CPts B σ}

/-- Two linear lifts of the same map agree (`Λ_B` is discrete). -/
theorem lift_unique [DiscreteTopology ΛB] [IsZLattice ℝ ΛB] (hB : IsUniformization σ ΛB ΦB)
    (ψ : (Fin g → ℂ) → CPts B σ) (M M' : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ))
    (hM : ∀ z, ΦB (M z) = ψ z) (hM' : ∀ z, ΦB (M' z) = ψ z) : M = M' := by
  have key : ∀ w, M w - M' w ∈ ΛB := by
    intro w
    rw [← hB.2.1]
    have e : ΦB (M w) = ΦB (M w - M' w) * ΦB (M' w) := by
      rw [← hB.1, sub_add_cancel]
    rw [hM, hM'] at e
    have := congrArg (fun x => x * (ψ w)⁻¹) e
    simpa using this.symm
  apply LinearMap.ext
  intro z
  apply sub_eq_zero.1
  apply HDec.G0Galois.eq_zero_of_real_smul_mem ΛB
  intro t
  have := key ((t : ℂ) • z)
  rwa [map_smul, map_smul, ← smul_sub, Complex.coe_smul] at this

/-- The lift of `f + f'` is the sum of the lifts. -/
theorem lift_add [DiscreteTopology ΛB] [IsZLattice ℝ ΛB] (hB : IsUniformization σ ΛB ΦB)
    (f f' : PkgI3.AbVar.Hom A B) (M M' N : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ))
    (hM : ∀ z, ΦB (M z) = ΦA z ≫ f.hom) (hM' : ∀ z, ΦB (M' z) = ΦA z ≫ f'.hom)
    (hN : ∀ z, ΦB (N z) = ΦA z ≫ (f + f').hom) : N = M + M' := by
  refine lift_unique hB (fun z => ΦA z ≫ (f + f').hom) N (M + M') hN fun z => ?_
  rw [LinearMap.add_apply, hB.1, hM, hM', PkgI3.AbVar.Hom.hom_add, MonObj.comp_mul]

/-- A linear lift vanishing on `Λ_A` comes from the zero homomorphism. -/
theorem eq_zero_of_lift_lattice [DiscreteTopology ΛA] [IsZLattice ℝ ΛA] (hA : IsUniformization σ ΛA ΦA)
    (hB : IsUniformization σ ΛB ΦB) (f : PkgI3.AbVar.Hom A B) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ))
    (hM : ∀ z, ΦB (M z) = ΦA z ≫ f.hom) (h0 : ∀ lam ∈ ΛA, M lam = 0) : f = 0 := by
  have hMR : M.restrictScalars ℝ = 0 := by
    apply LinearMap.ext_on_range (v := fun lam : ΛA => (lam : Fin g → ℂ))
    · rw [Subtype.range_coe_subtype]
      exact IsZLattice.span_top
    · intro lam
      exact h0 lam lam.2
  apply hom_eq_zero_of_cpts σ f
  intro p
  obtain ⟨z, rfl⟩ := hA.2.2.1 p
  rw [← hM]
  have : M z = 0 := by
    have := LinearMap.congr_fun hMR z
    simpa using this
  rw [this]
  exact (hB.2.1 0).2 (zero_mem _)

end Lift

end ZInQ.Contrib.OneProof.HomFreeC
