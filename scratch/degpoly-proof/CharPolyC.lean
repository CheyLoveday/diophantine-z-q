import ZInQKernel.Contrib.OneProof.HomFreeFiniteAlgClosed
import ZInQKernel.Contrib.OneProof.DegEqDetTate

/-! degpoly-proof scratch: the characteristic polynomial of `V_ℓ(φ)` is the integral characteristic
polynomial of `φ` on the period lattice (fields with `K̄ → ℂ`). -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

namespace DegPolyScratch

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj Polynomial
open scoped TensorProduct
open ZInQ.LeafPush2 (CPts IsUniformization)

variable {K : Type} [Field K]

/-- The lattice endomorphism of a lift preserving `Λ`. -/
def latEnd {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hM : ∀ lam : Λ, M lam ∈ Λ) : Λ →ₗ[ℤ] Λ :=
  (M.restrictScalars ℤ).restrict (fun x hx => hM ⟨x, hx⟩)

theorem latEnd_apply {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hM : ∀ lam : Λ, M lam ∈ Λ) (lam : Λ) : ((latEnd Λ M hM lam : Λ) : Fin g → ℂ) = M lam := rfl

/-- **`charpoly V_ℓ(φ) = charpoly_ℤ(φ on Λ)`.** -/
theorem charpoly_V_eq (HT : AvSplit.MumfordTorsionAlgClosed) (emb : AlgebraicClosure K →+* ℂ)
    (A : PkgI3.AbVar K) (φ : PkgI3.AbVar.End A) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞))
    (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (hlat : IsZLattice ℝ Λ)
    (Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap K (AlgebraicClosure K))))
    (hA : IsUniformization (emb.comp (algebraMap K (AlgebraicClosure K))) Λ Φ)
    (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hM : ∀ z, Φ (M z) = Φ z ≫ φ.hom)
    (hMlat : ∀ lam : Λ, M lam ∈ Λ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) (I : Type) [Fintype I] [DecidableEq I]
    (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)) :
    haveI := ZLattice.module_finite ℝ Λ
    haveI := ZLattice.module_free ℝ Λ
    (LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
      (latEnd Λ M hMlat).charpoly.map (Int.castRingHom ℚ_[ℓ]) := by
  classical
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  set X := latEnd Λ M hMlat with hX
  obtain ⟨α, hαinj, hα⟩ := HDec.G0Galois.tateLatticeInj_of_T5 (AvSplit.Final.h25 HT) K A emb g Λ Φ
    hg hlat hA ℓ
  -- intertwining over `ℤ_ℓ`
  have hint : ∀ x, α (X.baseChange ℤ_[ℓ] x) = PkgI3.AbVar.homT (ℓ := ℓ) φ (α x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a lam =>
      rw [LinearMap.baseChange_tmul]
      have e1 : ∀ y : Λ, a ⊗ₜ[ℤ] y = a • ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] y) := fun y => by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e1, e1, map_smul, map_smul, map_smul,
        HDec.G0Galois.homT_tateLattice emb ℓ α hα α hα φ M hM lam (hMlat lam)]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  -- `T_ℓ` is free of rank `2g`
  have hcard := ZInQ.Contrib.OneProof.DegDet.card_tb_of_mumford HT A ℓ hℓ g hg
  obtain ⟨E⟩ := T5Torsion.TateFree.tate_linearEquiv (2 * g) hcard
  haveI : Module.Free ℤ_[ℓ] (A.T ℓ) := Module.Free.of_equiv E.symm
  haveI : Module.Finite ℤ_[ℓ] (A.T ℓ) := Module.Finite.equiv E.symm
  -- base change to `ℚ_ℓ`
  haveI : Module.Flat ℤ_[ℓ] ℚ_[ℓ] := IsLocalization.flat ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ])
  set β := α.baseChange ℚ_[ℓ] with hβ
  have hβinj : Function.Injective β := by
    rw [hβ, LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hαinj
  have hdim : Module.finrank ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] Λ)) =
      Module.finrank ℚ_[ℓ] (A.V ℓ) := by
    change _ = Module.finrank ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] A.T ℓ)
    rw [Module.finrank_baseChange, Module.finrank_baseChange, Module.finrank_baseChange,
      E.finrank_eq, Module.finrank_fin_fun, ZInQ.Contrib.OneProof.HomFreeC.finrank_lattice Λ]
  haveI : Module.Finite ℚ_[ℓ] (A.V ℓ) := Module.Finite.of_basis b
  set e := LinearMap.linearEquivOfInjective β hβinj hdim with he
  set Y := (X.baseChange ℤ_[ℓ]).baseChange ℚ_[ℓ] with hY
  have hcomm : (PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ] ∘ₗ β = β ∘ₗ Y := by
    rw [hβ, hY, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    congr 1
    exact LinearMap.ext fun x => (hint x).symm
  have hconj : e.conj Y = (PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ] := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := e.surjective v
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    exact (LinearMap.congr_fun hcomm w).symm
  rw [LinearMap.charpoly_toMatrix, ← hconj, LinearEquiv.charpoly_conj, hY,
    LinearMap.charpoly_baseChange, LinearMap.charpoly_baseChange, Polynomial.map_map,
    RingHom.ext_int ((algebraMap ℤ_[ℓ] ℚ_[ℓ]).comp (algebraMap ℤ ℤ_[ℓ])) (Int.castRingHom ℚ_[ℓ])]

/-- **Mumford §19 Thm 4 (second assertion) when `K̄ → ℂ`.** -/
theorem charPolyIndep_of_emb (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (HT : AvSplit.MumfordTorsionAlgClosed) (emb : AlgebraicClosure K →+* ℂ)
    (A : PkgI3.AbVar K) (φ : PkgI3.AbVar.End A) :
    ∃ P : ℤ[X], P.Monic ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        (LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
          P.map (Int.castRingHom ℚ_[ℓ]) := by
  classical
  set σ : K →+* ℂ := emb.comp (algebraMap K (AlgebraicClosure K)) with hσ
  have h35 := AvSplit.Final.h38 HL HT
  have hN2 := ZInQ.HomLattice.homLinearLift_of_analyticHomLift
    (AvSplit.HomLatticeAN3.analyticHomLift_of_C (ZInQ.HomLattice.analyticHomLiftC_of_leaf HL))
  obtain ⟨g, hg⟩ := PkgI3.AbVar.dim_finite A
  obtain ⟨Λ, Φ, hd, hlat, hA⟩ := h35 K A σ g hg
  obtain ⟨M, hM⟩ := hN2 K A A σ g g Λ Λ Φ Φ hg hg hA hA φ
  have hMlat : ∀ lam : Λ, M lam ∈ Λ := fun lam =>
    HDec.G0Galois.lift_mem_lattice hA hA φ M hM lam
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  refine ⟨(latEnd Λ M hMlat).charpoly, LinearMap.charpoly_monic _, fun ℓ _ hℓ I _ _ b => ?_⟩
  exact charpoly_V_eq HT emb A φ g hg Λ hlat Φ hA M hM hMlat ℓ hℓ I b

end DegPolyScratch
