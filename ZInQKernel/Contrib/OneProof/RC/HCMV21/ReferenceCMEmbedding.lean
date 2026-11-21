import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceOrder
import ZInQKernel.Contrib.OneProof.RC.HCMV21.ReferenceAdelic
import Mathlib.RingTheory.Flat.Basic

/-! Extend the specialized CM action to the field and its local algebras
in the single rational frame. Tex 9150–9169 and 9265–9279. -/

namespace ZInQ.Manuscript.RC.HCMV21

open Eichler Adelic NumberField PkgI3.AbVar
open scoped CategoryTheory.MonObj NumberField TensorProduct

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {a b : ℚ}
  {k : Type} [Field k] {A : PkgI3.AbVar k}

/-- The integral basis of the CM order becomes the rational basis of its field. -/
def ringOfIntegersRationalization (F : Type*) [Field F] [NumberField F] :
    (ℚ ⊗[ℤ] 𝓞 F) ≃ₐ[ℚ] F := by
  let f := AlgHom.liftEquiv ℤ ℚ (𝓞 F) F (IsScalarTower.toAlgHom ℤ (𝓞 F) F)
  let e := ((RingOfIntegers.basis F).baseChange ℚ).equiv (integralBasis F) (Equiv.refl _)
  have h : e.toLinearMap = f.toLinearMap := by
    apply ((RingOfIntegers.basis F).baseChange ℚ).ext
    intro i
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, integralBasis_apply]
    rw [Module.Basis.baseChange_apply]
    change _ = f (1 ⊗ₜ[ℤ] (RingOfIntegers.basis F i))
    rw [AlgHom.liftEquiv_tmul, one_smul]
    rfl
  have hb : Function.Bijective f.toLinearMap := h ▸ e.bijective
  exact AlgEquiv.ofBijective f hb

@[simp] theorem ringOfIntegersRationalization_one_tmul (x : 𝓞 F) :
    ringOfIntegersRationalization F (1 ⊗ₜ[ℤ] x) = algebraMap (𝓞 F) F x := by
  change AlgHom.liftEquiv ℤ ℚ (𝓞 F) F (IsScalarTower.toAlgHom ℤ (𝓞 F) F)
    (1 ⊗ₜ[ℤ] x) = _
  rw [AlgHom.liftEquiv_tmul, one_smul]
  rfl

/-- The rational extension of the same specialized CM action. -/
def referenceCMEmbedding (S : Order a b) (j : A.End ≃+* S.ring) (action : 𝓞 F →+* A.End) :
    F →ₐ[ℚ] B a b :=
  (AlgHom.liftEquiv ℤ ℚ (𝓞 F) (B a b)
    ((S.ring.subtype.comp j.toRingHom).comp action).toIntAlgHom).comp
      (ringOfIntegersRationalization F).symm.toAlgHom

theorem referenceCMEmbedding_on_order (S : Order a b) (j : A.End ≃+* S.ring)
    (action : 𝓞 F →+* A.End) (x : 𝓞 F) :
    referenceCMEmbedding S j action (algebraMap (𝓞 F) F x) = (j (action x) : B a b) := by
  rw [← ringOfIntegersRationalization_one_tmul x]
  change AlgHom.liftEquiv ℤ ℚ (𝓞 F) (B a b)
      ((S.ring.subtype.comp j.toRingHom).comp action).toIntAlgHom
      ((ringOfIntegersRationalization F).symm
        (ringOfIntegersRationalization F (1 ⊗ₜ[ℤ] x))) = _
  rw [AlgEquiv.symm_apply_apply, AlgHom.liftEquiv_tmul, one_smul]
  rfl

/-- Localize in the same rational frame at every prime. -/
def localCMEmbedding (p : Prime) (j : F →ₐ[ℚ] B a b) :
    (ℚ_[p.val] ⊗[ℚ] F) →ₐ[ℚ_[p.val]] Bp p.val a b :=
  (quaternionBaseChange p).toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id _ _) j)

theorem localCMEmbedding_injective (p : Prime) (j : F →ₐ[ℚ] B a b) :
    Function.Injective (localCMEmbedding p j) := by
  apply (quaternionBaseChange p).injective.comp
  exact Module.Flat.lTensor_preserves_injective_linearMap j.toLinearMap j.injective

@[simp] theorem localCMEmbedding_tmul (p : Prime) (j : F →ₐ[ℚ] B a b)
    (c : ℚ_[p.val]) (x : F) :
    localCMEmbedding p j (c ⊗ₜ[ℚ] x) = c • toLocal p.val (j x) := by
  change quaternionBaseChange p ((Algebra.TensorProduct.map (AlgHom.id ℚ ℚ_[p.val]) j)
    (c ⊗ₜ[ℚ] x)) = _
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, quaternionBaseChange_tmul]

/-- The integral tensor image preserves the geometric level whenever the
specialized CM order preserves it. -/
theorem localCMEmbedding_integral_tensors (p : Prime) (S : Order a b)
    (j : A.End ≃+* S.ring) (action : 𝓞 F →+* A.End) (C : Subgroup (A.Pt k))
    (N : ℕ) (hN : N ≠ 0) (hC : ∀ P ∈ C, P ^ N = 1)
    (hact : ∀ x : 𝓞 F, action x ∈ levelEnd A C) (c : ℤ_[p.val]) (x : 𝓞 F) :
    localCMEmbedding p (referenceCMEmbedding S j action)
      ((c : ℚ_[p.val]) ⊗ₜ[ℚ] (algebraMap (𝓞 F) F x)) ∈
        (levelOrderOfEndOrder S j C N hN hC).completion p.val := by
  rw [localCMEmbedding_tmul, referenceCMEmbedding_on_order]
  let R := levelOrderOfEndOrder S j C N hN hC
  change c • toLocal p.val (j (action x) : B a b) ∈ R.completion p.val
  rw [← SetLike.mem_coe, ← Subalgebra.coe_toSubmodule, R.completion_toSubmodule]
  exact (localLattice p.val R.lattice).smul_mem c
    (Submodule.subset_span ⟨(j (action x) : B a b), ⟨action x, hact x, rfl⟩, rfl⟩)

end

end ZInQ.Manuscript.RC.HCMV21
