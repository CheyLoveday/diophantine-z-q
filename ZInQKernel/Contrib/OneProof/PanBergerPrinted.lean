import ZInQKernel.Contrib.OneProof.PanBergerFix

/-!
# `PanBerger` from Pan's and Berger's theorems, each stated for one representation (task pb-fix2)

Work in progress.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace PanBergerSplit

open Module
open scoped TensorProduct Matrix

/-! ## §1. The contragredient of a matrix representation -/

section DualHom

variable {G : Type*} [Group G] {R : Type*} [CommRing R] {n : ℕ}

/-- The contragredient `σ ↦ ρ(σ⁻¹)ᵀ` of a matrix representation (the action on the dual basis). -/
def dualHom (ρ : G →* GL (Fin n) R) : G →* GL (Fin n) R where
  toFun σ := ⟨(ρ σ⁻¹ : Matrix (Fin n) (Fin n) R)ᵀ, (ρ σ : Matrix (Fin n) (Fin n) R)ᵀ,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, Matrix.transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' σ τ := Units.ext (by simp [Matrix.transpose_mul])

theorem dualHom_val (ρ : G →* GL (Fin n) R) (σ : G) :
    ((dualHom ρ σ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      (ρ σ⁻¹ : Matrix (Fin n) (Fin n) R)ᵀ := rfl

theorem dualHom_map {S : Type*} [CommRing S] (f : R →+* S) (ρ : G →* GL (Fin n) R) (σ : G) :
    Matrix.GeneralLinearGroup.map f (dualHom ρ σ) =
      dualHom ((Matrix.GeneralLinearGroup.map f).comp ρ) σ := by
  apply Units.ext
  ext i j
  rfl

theorem dualHom_model {S : Type*} [CommRing S] (f : R →+* S) (ρ : G →* GL (Fin n) R)
    (ρ' : G →* GL (Fin n) S) (h : ∀ σ, Matrix.GeneralLinearGroup.map f (ρ σ) = ρ' σ) (σ : G) :
    Matrix.GeneralLinearGroup.map f (dualHom ρ σ) = dualHom ρ' σ := by
  rw [dualHom_map, show (Matrix.GeneralLinearGroup.map f).comp ρ = ρ' from MonoidHom.ext h]

end DualHom

/-! ## §2. The contragredient of a Galois representation, and what it preserves -/

section DualRep

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

/-- The contragredient `ρ^∨ : σ ↦ ρ(σ⁻¹)ᵀ` of a continuous `ρ : G_ℚ → GL_n(ℚ̄_ℓ)`. -/
def dualRep (ρ : GaloisRep ℓ n) : GaloisRep ℓ n where
  toHom := dualHom ρ.toHom
  continuous_toHom := by
    rw [Units.continuous_iff]
    constructor
    · exact (Units.continuous_val.comp (ρ.continuous_toHom.comp continuous_inv)).matrix_transpose
    · exact (Units.continuous_val.comp ρ.continuous_toHom).matrix_transpose

theorem dualRep_mat (ρ : GaloisRep ℓ n) (σ : GQ) : (dualRep ρ).mat σ = (ρ.mat σ⁻¹)ᵀ := rfl

theorem dualRep_mat_inv (ρ : GaloisRep ℓ n) (σ : GQ) : (dualRep ρ).mat σ⁻¹ = (ρ.mat σ)ᵀ := by
  rw [dualRep_mat, inv_inv]

theorem trace_dualRep_inv (ρ : GaloisRep ℓ n) (σ : GQ) :
    ((dualRep ρ).mat σ⁻¹).trace = (ρ.mat σ).trace := by
  rw [dualRep_mat_inv, Matrix.trace_transpose]

theorem dualRep_restrictLocal (p : ℕ) [Fact p.Prime] (ρ : GaloisRep ℓ n) :
    (dualRep ρ).restrictLocal p = dualHom (ρ.restrictLocal p) := by
  ext σ i j
  change (ρ.toHom (decomp p σ)⁻¹ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))ᵀ i j =
    (ρ.toHom (decomp p σ⁻¹) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))ᵀ i j
  rw [map_inv (decomp p), map_inv ρ.toHom]

/-- `ρ` irreducible (Burnside form) implies `ρ^∨` irreducible. -/
theorem dualRep_isIrreducible (ρ : GaloisRep ℓ n) (h : ρ.IsIrreducible) :
    (dualRep ρ).IsIrreducible := by
  unfold GaloisRep.IsIrreducible at *
  set A := Algebra.adjoin (PadicAlgCl ℓ) (Set.range (dualRep ρ).mat) with hA
  let S : Subalgebra (PadicAlgCl ℓ) (Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) :=
    { carrier := {X | Xᵀ ∈ A}
      mul_mem' := fun {X Y} hX hY => by
        simp only [Set.mem_ofPred_eq, Matrix.transpose_mul] at *
        exact A.mul_mem hY hX
      add_mem' := fun {X Y} hX hY => by
        simp only [Set.mem_ofPred_eq, Matrix.transpose_add] at *
        exact A.add_mem hX hY
      algebraMap_mem' := fun r => by
        simp only [Set.mem_ofPred_eq, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_transpose]
        rw [← Matrix.algebraMap_eq_diagonal]
        exact A.algebraMap_mem r }
  have hle : Algebra.adjoin (PadicAlgCl ℓ) (Set.range ρ.mat) ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨σ, rfl⟩
    show (ρ.mat σ)ᵀ ∈ A
    rw [← dualRep_mat_inv]
    exact Algebra.subset_adjoin ⟨_, rfl⟩
  rw [h] at hle
  refine eq_top_iff.mpr fun X _ => ?_
  have hX : Xᵀ ∈ S := hle Algebra.mem_top
  simpa [S] using hX

theorem dualRep_unramifiedAt (ρ : GaloisRep ℓ n) (q : ℕ) (h : ρ.UnramifiedAt q) :
    (dualRep ρ).UnramifiedAt q := by
  intro v hv σ hσ
  have h1 := h v hv σ hσ
  apply Units.ext
  change (ρ.toHom _⁻¹ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))ᵀ = 1
  rw [map_inv, h1, inv_one, Units.val_one, Matrix.transpose_one]

theorem dualRep_finitelyRamified (ρ : GaloisRep ℓ n) (h : ρ.FinitelyRamified) :
    (dualRep ρ).FinitelyRamified := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun q hq hqS => dualRep_unramifiedAt ρ q (hS q hq hqS)⟩

theorem dualRep_isOdd (ρ : GaloisRep ℓ 2) (h : ρ.IsOdd) : (dualRep ρ).IsOdd := by
  intro c hc
  have h1 := h c hc
  rw [dualRep_mat, Matrix.det_transpose]
  have h2 : (ρ.mat c).det * (ρ.mat c⁻¹).det = 1 := by
    rw [← Matrix.det_mul]
    simp only [GaloisRep.mat, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.det_one]
  rw [h1] at h2
  linear_combination -h2

end DualRep

/-! ## §3. Fontaine's functors in the printed tensor form, and the trace pairing -/

section Tensor

variable (p : ℕ) [Fact p.Prime]
variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {n : ℕ}

/-- **`(B ⊗_{ℚ_p} V)^H`**, Fontaine's `D_B` in the printed tensor form, for a `ℚ_p`-linear action
`act` of `G_{ℚ_p}` on a period ring (or module) `B`, a subgroup `H` (`G_K`), and `V = E^n` with
the action `ρ` (`ℚ_p`-linearly). -/
def tensorInv {B : Type*} [AddCommGroup B] [Module ℚ_[p] B] (act : GQp p → B →ₗ[ℚ_[p]] B)
    (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    Submodule ℚ_[p] (B ⊗[ℚ_[p]] (Fin n → E)) where
  carrier := {x | ∀ σ ∈ H, TensorProduct.map (act σ) (vAct p ρ σ) x = x}
  zero_mem' σ _ := map_zero _
  add_mem' ha hb σ hσ := by rw [map_add, ha σ hσ, hb σ hσ]
  smul_mem' c x hx σ hσ := by rw [map_smul, hx σ hσ]

/-- `Hom_H(V, B)`: `H`-equivariant `ℚ_p`-linear maps `V → B` (the form of pkg-I4's `ddrSpace`,
`htSpace` and pb-bypass's `dstSpace`). -/
def homInv {B : Type*} [AddCommGroup B] [Module ℚ_[p] B] (act : GQp p → B →ₗ[ℚ_[p]] B)
    (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    Submodule ℚ_[p] ((Fin n → E) →ₗ[ℚ_[p]] B) where
  carrier := {φ | ∀ σ ∈ H, ∀ v, φ (Matrix.mulVec (ρ σ : Matrix (Fin n) (Fin n) E) v) = act σ (φ v)}
  zero_mem' := by intro σ _ v; simp
  add_mem' := by
    intro φ ψ hφ hψ σ hσ v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ σ hσ v, hψ σ hσ v, map_add]
  smul_mem' := by
    intro c φ hφ σ hσ v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ σ hσ v, map_smul]

/-- The trace pairing `E^n × E^n → ℚ_p`, `(w, v) ↦ Tr_{E/ℚ_p}(Σ v_i w_i)`. -/
def trPair : (Fin n → E) →ₗ[ℚ_[p]] Module.Dual ℚ_[p] (Fin n → E) :=
  LinearMap.mk₂ ℚ_[p] (fun w v => Algebra.trace ℚ_[p] E (v ⬝ᵥ w))
    (fun w w' v => by rw [dotProduct_add, map_add])
    (fun c w v => by rw [dotProduct_smul, map_smul])
    (fun w v v' => by rw [add_dotProduct, map_add])
    (fun c w v => by rw [smul_dotProduct, map_smul])

theorem trPair_apply (w v : Fin n → E) : trPair p w v = Algebra.trace ℚ_[p] E (v ⬝ᵥ w) := rfl

theorem trPair_injective : Function.Injective (trPair p (E := E) (n := n)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  funext i
  have : PerfectField ℚ_[p] := PerfectField.ofCharZero
  have : Algebra.IsAlgebraic ℚ_[p] E := Algebra.IsAlgebraic.of_finite ℚ_[p] E
  have : Algebra.IsSeparable ℚ_[p] E := Algebra.IsAlgebraic.isSeparable_of_perfectField
  refine (traceForm_nondegenerate ℚ_[p] E).1 (w i) fun c => ?_
  have := LinearMap.congr_fun hw (Pi.single i c)
  rw [trPair_apply, single_dotProduct, LinearMap.zero_apply] at this
  rw [Algebra.traceForm_apply, mul_comm]
  exact this

/-- The trace pairing as an isomorphism `E^n ≅ (E^n)^* = Hom_{ℚ_p}(E^n, ℚ_p)`. -/
def trEquiv : (Fin n → E) ≃ₗ[ℚ_[p]] Module.Dual ℚ_[p] (Fin n → E) :=
  LinearEquiv.ofBijective (trPair p) ⟨trPair_injective p,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq).symm).mp (trPair_injective p)⟩

theorem trEquiv_apply (w v : Fin n → E) : trEquiv p w v = Algebra.trace ℚ_[p] E (v ⬝ᵥ w) := rfl

/-- The trace pairing intertwines the contragredient matrix action with the dual action:
`⟨ρ(σ⁻¹)ᵀ w, v⟩ = ⟨w, ρ(σ⁻¹) v⟩`. -/
theorem trPair_dual (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) (w v : Fin n → E) :
    trPair p (vAct p (dualHom ρ) σ w) v = trPair p w (vAct p ρ σ⁻¹ v) := by
  rw [trPair_apply, trPair_apply, vAct_apply, vAct_apply, dualHom_val, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

variable {B : Type*} [AddCommGroup B] [Module ℚ_[p] B]

/-- `B ⊗ E^n ≅ Hom_{ℚ_p}(E^n, B)`, `b ⊗ w ↦ (v ↦ ⟨w, v⟩ b)`, through the trace pairing. -/
def tensorHomEquiv : (B ⊗[ℚ_[p]] (Fin n → E)) ≃ₗ[ℚ_[p]] ((Fin n → E) →ₗ[ℚ_[p]] B) :=
  haveI : Module.Free ℚ_[p] (Fin n → E) := Module.Free.of_divisionRing _ _
  haveI : Module.Finite ℚ_[p] (Fin n → E) := Module.Finite.pi
  (TensorProduct.congr (LinearEquiv.refl ℚ_[p] B) (trEquiv p)).trans
    ((TensorProduct.comm ℚ_[p] B (Module.Dual ℚ_[p] (Fin n → E))).trans
      (dualTensorHomEquiv ℚ_[p] (Fin n → E) B))

theorem tensorHomEquiv_tmul (b : B) (w v : Fin n → E) :
    tensorHomEquiv p (b ⊗ₜ w) v = trPair p w v • b := rfl

theorem tensorHomEquiv_map (act : GQp p → B →ₗ[ℚ_[p]] B) (ρ : GQp p →* GL (Fin n) E)
    (σ : GQp p) (x : B ⊗[ℚ_[p]] (Fin n → E)) (v : Fin n → E) :
    tensorHomEquiv p (TensorProduct.map (act σ) (vAct p (dualHom ρ) σ) x) v =
      act σ (tensorHomEquiv p x (vAct p ρ σ⁻¹ v)) := by
  induction x using TensorProduct.inductionOn with
  | tmul b w =>
    rw [TensorProduct.map_tmul, tensorHomEquiv_tmul, tensorHomEquiv_tmul, map_smul, trPair_dual]
  | add x y hx hy =>
    rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add, LinearMap.add_apply, map_add]

/-- **`(B ⊗ V^∨)^H ≅ Hom_H(V, B)`**, with `V^∨` realized as `E^n` with the contragredient matrix
action (`dualHom`) through the trace pairing. -/
theorem map_tensorInv_dualHom (act : GQp p → B →ₗ[ℚ_[p]] B) (H : Subgroup (GQp p))
    (ρ : GQp p →* GL (Fin n) E) :
    Submodule.map (tensorHomEquiv p).toLinearMap (tensorInv p act H (dualHom ρ)) =
      homInv p act H ρ := by
  ext φ
  constructor
  · rintro ⟨x, hx, rfl⟩ σ hσ w
    have h := congrArg (fun y => tensorHomEquiv p y (vAct p ρ σ w)) (hx σ hσ)
    rw [tensorHomEquiv_map, vAct_inv_mul] at h
    exact h.symm
  · intro hφ
    refine ⟨(tensorHomEquiv p).symm φ, fun σ hσ => ?_, by simp⟩
    apply (tensorHomEquiv p).injective
    refine LinearMap.ext fun v => ?_
    rw [tensorHomEquiv_map, LinearEquiv.apply_symm_apply]
    have := hφ σ hσ (vAct p ρ σ⁻¹ v)
    rw [← vAct_apply, vAct_mul_inv] at this
    exact this.symm

theorem finrank_tensorInv_dualHom (act : GQp p → B →ₗ[ℚ_[p]] B) (H : Subgroup (GQp p))
    (ρ : GQp p →* GL (Fin n) E) :
    finrank ℚ_[p] (tensorInv p act H (dualHom ρ)) = finrank ℚ_[p] (homInv p act H ρ) := by
  rw [← map_tensorInv_dualHom, LinearEquiv.finrank_map_eq]

end Tensor

end PanBergerSplit
end PkgI4
end HDec
