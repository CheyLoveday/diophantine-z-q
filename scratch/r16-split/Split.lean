import ZInQKernel.HDecomp.ModCurves.Leaves

/-! # r16-split: `R16_EichlerShimuraJ1'` from a strictly weaker core and `TateModuleFree`

The dimension clause `dim A = [K_f : ℚ]` of R16 follows from the rank-two clause and `T_ℓ(A)` free of
rank `2 dim A` (`PkgI3.TateModuleFree`): `V_ℓ(A)^* ⊗ ℚ̄_ℓ` is the direct sum of the `ι`-eigenfunctionals
over the `[K_f : ℚ]` embeddings `ι : K_f → ℚ̄_ℓ`. -/

noncomputable section

set_option linter.unusedSectionVars false

namespace R16Split

open Module

/-! ## 1. Linear algebra: joint eigenspaces of a field acting on a finite-dimensional space -/

section LinAlg

variable {F Ω W : Type*} [Field F] [Field Ω] [AddCommGroup W] [Module Ω W]

/-- The joint eigenspace of `P : F → End_Ω(W)` for the character `ι : F → Ω`. -/
def jointEig (P : F →+* Module.End Ω W) (ι : F →+* Ω) : Submodule Ω W where
  carrier := {φ | ∀ a, P a φ = ι a • φ}
  zero_mem' := by intro a; simp
  add_mem' := by
    intro x y hx hy a
    simp only [Set.mem_ofPred_eq] at hx hy
    rw [map_add, hx a, hy a, smul_add]
  smul_mem' := by
    intro c x hx a
    simp only [Set.mem_ofPred_eq] at hx
    rw [map_smul, hx a, smul_comm]

/-- The elements `a` with `P a φ = ι a φ` form a subfield. -/
def eqSubfield (P : F →+* Module.End Ω W) (ι : F →+* Ω) (φ : W) : Subfield F where
  carrier := {a | P a φ = ι a • φ}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul, map_mul, mul_comm]
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_add, LinearMap.add_apply, ha, hb, map_add, add_smul]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_neg, LinearMap.neg_apply, ha, map_neg, neg_smul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    by_cases h0 : a = 0
    · simp [h0]
    have h1 : P a⁻¹ (P a φ) = φ := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel₀ h0, map_one, Module.End.one_apply]
    rw [ha, map_smul] at h1
    have hι : ι a ≠ 0 := (map_ne_zero ι).2 h0
    calc P a⁻¹ φ = (ι a)⁻¹ • (ι a • P a⁻¹ φ) := by rw [smul_smul, inv_mul_cancel₀ hι, one_smul]
      _ = ι a⁻¹ • φ := by rw [h1, map_inv₀]

variable [Algebra ℚ F]

/-- A joint eigenvector is an eigenvector of a generator. -/
theorem mem_jointEig_iff (P : F →+* Module.End Ω W) (ι : F →+* Ω) {α : F}
    (hα : Algebra.adjoin ℚ {α} = ⊤) (φ : W) :
    φ ∈ jointEig P ι ↔ P α φ = ι α • φ := by
  refine ⟨fun h => h α, fun h a => ?_⟩
  let M : Subalgebra ℚ F :=
    { (eqSubfield P ι φ).toSubring with
      algebraMap_mem' := fun q => by
        rw [eq_ratCast]
        exact SubfieldClass.ratCast_mem (eqSubfield P ι φ) q }
  have hle : Algebra.adjoin ℚ {α} ≤ M := Algebra.adjoin_le (by simpa [M, eqSubfield] using h)
  rw [hα] at hle
  exact hle (Algebra.mem_top (x := a))

variable [IsAlgClosed Ω] [CharZero Ω] [FiniteDimensional Ω W] [FiniteDimensional ℚ F]

/-- `P(μ_α)(P α) = 0`, written over `Ω`. -/
theorem aeval_minpoly_eq_zero (P : F →+* Module.End Ω W) (α : F) :
    Polynomial.aeval (P α) ((minpoly ℚ α).map (algebraMap ℚ Ω)) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  have hr : (algebraMap Ω (Module.End Ω W)).comp (algebraMap ℚ Ω) = P.comp (algebraMap ℚ F) :=
    RingHom.ext_rat _ _
  rw [hr, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]

/-- **The joint eigenspaces of a number field acting on a finite-dimensional space over an
algebraically closed field of characteristic `0` add up to the whole space.** -/
theorem sum_finrank_jointEig (P : F →+* Module.End Ω W) :
    ∑ ι : F →ₐ[ℚ] Ω, finrank Ω (jointEig P ι.toRingHom) = finrank Ω W := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable ℚ F
  set α := pb.gen with hαdef
  have hα : Algebra.adjoin ℚ {α} = ⊤ := pb.adjoin_gen_eq_top
  set S := P α with hSdef
  have hE : ∀ ι : F →ₐ[ℚ] Ω, jointEig P ι.toRingHom = S.eigenspace (ι α) := by
    intro ι; ext φ
    rw [mem_jointEig_iff P ι.toRingHom hα, Module.End.mem_eigenspace_iff]
    rfl
  have hinj : Function.Injective (fun ι : F →ₐ[ℚ] Ω => ι α) := fun ι ι' h => pb.algHom_ext h
  have hind : iSupIndep (fun ι : F →ₐ[ℚ] Ω => S.eigenspace (ι α)) :=
    (S.eigenspaces_iSupIndep).comp hinj
  -- semisimplicity
  have hsep : (minpoly ℚ α).Separable := Algebra.IsSeparable.isSeparable ℚ α
  have hsq : Squarefree ((minpoly ℚ α).map (algebraMap ℚ Ω)) := (hsep.map).squarefree
  have hss : S.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq (aeval_minpoly_eq_zero P α)
  have hspan : ⨆ ι : F →ₐ[ℚ] Ω, S.eigenspace (ι α) = ⊤ := by
    rw [eq_top_iff, ← hss.iSup_eigenspace_eq_top]
    refine iSup_le fun r => ?_
    by_cases hr : S.eigenspace r = ⊥
    · rw [hr]; exact bot_le
    obtain ⟨x, hx⟩ := Module.End.HasEigenvalue.exists_hasEigenvector (f := S) (μ := r)
      (Module.End.hasEigenvalue_of_hasGenEigenvalue (k := 1) (by
        rw [Module.End.hasGenEigenvalue_iff]; simpa using hr))
    have h0 := Module.End.aeval_apply_of_hasEigenvector (p := (minpoly ℚ α).map (algebraMap ℚ Ω)) hx
    rw [aeval_minpoly_eq_zero P α, LinearMap.zero_apply] at h0
    have hroot : Polynomial.aeval r (minpoly ℚ α) = 0 := by
      have := (smul_eq_zero.mp h0.symm).resolve_right hx.2
      rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    let ι : F →ₐ[ℚ] Ω := pb.lift r hroot
    have hι : ι α = r := pb.lift_gen r hroot
    rw [← hι]
    exact le_iSup (fun ι : F →ₐ[ℚ] Ω => S.eigenspace (ι α)) ι
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hspan
  have e := LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hint
  rw [← e.finrank_eq, Module.finrank_directSum]
  exact Finset.sum_congr rfl fun ι _ => by rw [hE]

end LinAlg

end R16Split
