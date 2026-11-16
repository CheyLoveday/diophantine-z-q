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

/-! ## §4. The actions on `B_dR` and `ℂ_p(i)`, and pkg-I4's spaces as `Hom` forms -/

section Actions

variable (p : ℕ) [Fact p.Prime]
variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {n : ℕ}

/-- `σ` on `B_dR`, as a `ℚ_p`-linear map. -/
def bdrLin (σ : GQp p) : BdR p →ₗ[ℚ_[p]] BdR p where
  toFun := bdrAct p σ
  map_add' := map_add _
  map_smul' := bdrAct_smul p σ

/-- `σ` on `ℂ_p`, as a `ℚ_p`-linear map. -/
def cpLin (σ : GQp p) : ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p] where
  toFun := cpAct p σ
  map_add' := map_add _
  map_smul' c x := by
    rw [RingHom.id_apply, Algebra.smul_def, map_mul, cpAct_algebraMap, ← Algebra.smul_def]

/-- `σ` on the Tate twist `ℂ_p(i)`: `x ↦ χ(σ)^i σ(x)`. -/
def htLin (i : ℤ) (σ : GQp p) : ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p] := cycPow p σ i • cpLin p σ

omit [FiniteDimensional ℚ_[p] E] in
/-- pkg-I4's `ddrSpace` is `Hom_{G_{ℚ_p}}(V, B_dR)`. -/
theorem homInv_bdr (ρ : GQp p →* GL (Fin n) E) : homInv p (bdrLin p) ⊤ ρ = ddrSpace p ρ := by
  ext φ
  exact ⟨fun h σ v => h σ (Subgroup.mem_top σ) v, fun h σ _ v => h σ v⟩

omit [FiniteDimensional ℚ_[p] E] in
/-- pkg-I4's `htSpace ρ i` is `Hom_{G_{ℚ_p}}(V, ℂ_p(i))`. -/
theorem homInv_ht (ρ : GQp p →* GL (Fin n) E) (i : ℤ) :
    homInv p (htLin p i) ⊤ ρ = htSpace p ρ i := by
  ext φ
  exact ⟨fun h σ v => h σ (Subgroup.mem_top σ) v, fun h σ _ v => h σ v⟩

end Actions

/-! ## §5a. `W(k)[1/p]` for a field `k` of characteristic `p`, as a `ℚ_p`-algebra -/

section WittLoc

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p]

/-- `ℤ_p = W(𝔽_p) → W(k)` (Mathlib's `WittVector.equiv` and functoriality). -/
def zpToWitt : ℤ_[p] →+* WittVector p k :=
  (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom

/-- **`W(k)[1/p]`** (Mathlib's `Localization.Away`), as a type with its instances. -/
def WittLoc : Type _ := Localization.Away (p : WittVector p k)

instance : CommRing (WittLoc p k) :=
  inferInstanceAs (CommRing (Localization.Away (p : WittVector p k)))

instance : Algebra (WittVector p k) (WittLoc p k) :=
  inferInstanceAs (Algebra (WittVector p k) (Localization.Away (p : WittVector p k)))

instance : IsLocalization (Submonoid.powers (p : WittVector p k)) (WittLoc p k) :=
  inferInstanceAs (IsLocalization (Submonoid.powers (p : WittVector p k))
    (Localization.Away (p : WittVector p k)))

/-- `ℚ_p = ℤ_p[1/p] → W(k)[1/p]`. -/
def qpToWittLoc : ℚ_[p] →+* WittLoc p k :=
  IsLocalization.lift (M := Submonoid.powers (p : ℤ_[p]))
    (g := (algebraMap _ _).comp (zpToWitt p k)) (by
      rintro ⟨_, j, rfl⟩
      have := (IsLocalization.Away.algebraMap_isUnit (S := WittLoc p k)
        (p : WittVector p k)).pow j
      rw [map_natCast] at this
      simpa only [RingHom.comp_apply, map_pow, map_natCast] using this)

instance : Algebra ℚ_[p] (WittLoc p k) := (qpToWittLoc p k).toAlgebra

end WittLoc

/-! ## §5. `K_0 = W(k)[1/p]` -/

section K0

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- **`𝓞_K`**, the valuation ring of `K ⊆ ℚ̄_p`: the elements of `K` of norm `≤ 1` (the norm of
`ℚ̄_p` is the unique extension of `|·|_p`). -/
def intRing : Subring (PadicAlgCl p) where
  carrier := {x | x ∈ K ∧ ‖x‖ ≤ 1}
  mul_mem' := fun ha hb => ⟨K.mul_mem ha.1 hb.1, by
    rw [norm_mul]; exact (mul_le_mul ha.2 hb.2 (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)⟩
  one_mem' := ⟨K.one_mem, by rw [norm_one]⟩
  add_mem' := fun ha hb => ⟨K.add_mem ha.1 hb.1,
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha.2 hb.2)⟩
  zero_mem' := ⟨K.zero_mem, by rw [norm_zero]; exact zero_le_one⟩
  neg_mem' := fun ha => ⟨K.neg_mem ha.1, by rw [norm_neg]; exact ha.2⟩

/-- **`𝔪_K`**, the maximal ideal of `𝓞_K`: the elements of norm `< 1`. -/
def maxIdeal : Ideal (intRing p K) where
  carrier := {x | ‖(x : PadicAlgCl p)‖ < 1}
  add_mem' := fun {a b} ha hb => by
    show ‖(a : PadicAlgCl p) + b‖ < 1
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by
    show ‖((0 : intRing p K) : PadicAlgCl p)‖ < 1
    rw [ZeroMemClass.coe_zero, norm_zero]; exact zero_lt_one
  smul_mem' := fun c x hx => by
    show ‖(c : PadicAlgCl p) * x‖ < 1
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) c.2.2) hx

instance maxIdeal_isMaximal : (maxIdeal p K).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => ?_, fun J x hle hx hxJ => ?_⟩
  · change ‖((1 : intRing p K) : PadicAlgCl p)‖ < 1 at h
    rw [OneMemClass.coe_one, norm_one] at h
    exact lt_irrefl _ h
  · have hx1 : ‖(x : PadicAlgCl p)‖ = 1 := le_antisymm x.2.2 (not_lt.mp hx)
    have hx0 : (x : PadicAlgCl p) ≠ 0 := by
      intro h; rw [h, norm_zero] at hx1; exact zero_ne_one hx1
    let y : intRing p K := ⟨(x : PadicAlgCl p)⁻¹, K.inv_mem x.2.1, by rw [norm_inv, hx1, inv_one]⟩
    have hxy : x * y = 1 := Subtype.ext (mul_inv_cancel₀ hx0)
    rw [← hxy]
    exact J.mul_mem_right y hxJ

/-- **`k_K = 𝓞_K / 𝔪_K`**, the residue field of `K`. -/
abbrev resField : Type := intRing p K ⧸ maxIdeal p K

instance : Field (resField p K) := Ideal.Quotient.field _

theorem natCast_p_mem_maxIdeal : (p : intRing p K) ∈ maxIdeal p K := by
  show ‖((p : intRing p K) : PadicAlgCl p)‖ < 1
  rw [show ((p : intRing p K) : PadicAlgCl p) = (p : PadicAlgCl p) by simp]
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, norm_algebraMap', Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

instance resField_charP : CharP (resField p K) p :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk (maxIdeal p K)) p, Ideal.Quotient.eq_zero_iff_mem]
    exact natCast_p_mem_maxIdeal p K)

/-- **`K_0 = W(k_K)[1/p]`**, Fontaine's `K_0` for `K` (Berger 2002, §0: `K_0 = W(k)[1/p]`;
Fontaine, Astérisque 223 (1994), Exp. III; numbers UNVERIFIED): the Witt vectors of the residue
field of `K` with `p` inverted (Mathlib's `WittVector`, `Localization.Away`; `WittLoc` below). -/
abbrev K0W : Type := WittLoc p (resField p K)

end K0

/-! ## §6. Fontaine's de Rham, Hodge–Tate and semistable conditions on the underlying space -/

section Predicates

variable (p : ℕ) [Fact p.Prime]
variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {n : ℕ}

/-- **`D_dR(V) = (B_dR ⊗_{ℚ_p} V)^{G_{ℚ_p}}`** for `V = E^n` with the action `ρ`. -/
def ddrU (ρ : GQp p →* GL (Fin n) E) : Submodule ℚ_[p] (BdR p ⊗[ℚ_[p]] (Fin n → E)) :=
  tensorInv p (bdrLin p) ⊤ ρ

/-- **`V` is de Rham** (Fontaine): `dim_{ℚ_p} D_dR(V) = dim_{ℚ_p} V` (`K = K_0 = ℚ_p`). -/
def IsDeRhamU (ρ : GQp p →* GL (Fin n) E) : Prop :=
  finrank ℚ_[p] (ddrU p ρ) = finrank ℚ_[p] (Fin n → E)

/-- A `ℚ̄_p`-valued representation of `G_{ℚ_p}` is de Rham: it takes values in `GL_n(E)` for a
finite `E/ℚ_p` inside `ℚ̄_p`, and the `ℚ_p`-representation `E^n` is de Rham. -/
def LocalIsDeRhamU (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    IsDeRhamU p ρE

/-- **`(ℂ_p(w) ⊗_{ℚ_p} V)^{G_{ℚ_p}}`**. -/
def htU (ρ : GQp p →* GL (Fin n) E) (w : ℤ) : Submodule ℚ_[p] (ℂ_[p] ⊗[ℚ_[p]] (Fin n → E)) :=
  tensorInv p (htLin p w) ⊤ ρ

/-- **Multiplicity of the Hodge–Tate weight `w`** of the `E`-linear `V = E^n`:
`dim_E (ℂ_p(w) ⊗_{ℚ_p} V)^{G_{ℚ_p}}` (cyclotomic character of weight `−1`, Pan's convention). -/
def htMultU (ρ : GQp p →* GL (Fin n) E) (w : ℤ) : ℕ :=
  finrank ℚ_[p] (htU p ρ w) / finrank ℚ_[p] E

/-- **`ρ|_{G_{ℚ_p}}` is Hodge–Tate with distinct Hodge–Tate weights** (2-dimensional case): in a
model over a finite `E ⊆ ℚ̄_p`, the weights (with multiplicity, over `E`) are two distinct
integers `a ≠ b`. -/
def LocalDistinctHTU (ρ : GQp p →* GL (Fin 2) (PadicAlgCl p)) : Prop :=
  ∃ a b : ℤ, a ≠ b ∧ ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin 2) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    ∀ w : ℤ, htMultU p ρE w = Multiset.count w {a, b}

/-- **`D_st,K(V) = (B_st ⊗_{ℚ_p} V)^{G_K}`**. -/
def dstU (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (ρ : GQp p →* GL (Fin n) E) :
    Submodule ℚ_[p] (Bst p ⊗[ℚ_[p]] (Fin n → E)) :=
  tensorInv p (stLin p) K.fixingSubgroup ρ

/-- **`V` is semistable over `K`** (Fontaine): `dim_{K_0} D_st,K(V) = dim_{ℚ_p} V`, written in
`ℚ_p`-dimensions with `K_0 = W(k_K)[1/p]` (`K0W`):
`dim_{ℚ_p} D_st,K(V) = [K_0 : ℚ_p] · dim_{ℚ_p} V`. -/
def IsSemistableOverU (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (ρ : GQp p →* GL (Fin n) E) :
    Prop :=
  finrank ℚ_[p] (dstU p K ρ) = finrank ℚ_[p] (K0W p K) * finrank ℚ_[p] (Fin n → E)

/-- **`V` is potentially semistable** (Fontaine): semistable over some finite `K/ℚ_p`. -/
def IsPstU (ρ : GQp p →* GL (Fin n) E) : Prop :=
  ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
    IsSemistableOverU p K ρ

/-- A `ℚ̄_p`-valued representation of `G_{ℚ_p}` is potentially semistable: it takes values in
`GL_n(E)` for a finite `E/ℚ_p` inside `ℚ̄_p`, and the `ℚ_p`-representation `E^n` is potentially
semistable. -/
def LocalIsPstU (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    IsPstU p ρE

theorem finrank_fun :
    finrank ℚ_[p] (Fin n → E) = n * finrank ℚ_[p] E := by
  have : Module.Free ℚ_[p] E := Module.Free.of_divisionRing _ _
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- pkg-I4's `LocalIsDeRham ρ` (computed on `Hom_G(V, B_dR)`) is the printed de Rham condition for
the contragredient. -/
theorem localIsDeRhamU_dualHom (ρ : GQp p →* GL (Fin n) (PadicAlgCl p))
    (h : LocalIsDeRham p n ρ) : LocalIsDeRhamU p n (dualHom ρ) := by
  obtain ⟨E, hE, ρE, hmod, hdr⟩ := h
  refine ⟨E, hE, dualHom ρE, dualHom_model _ ρE ρ hmod, ?_⟩
  rw [IsDeRhamU, ddrU, finrank_tensorInv_dualHom, homInv_bdr, finrank_fun]
  exact hdr

theorem count_neg_pair (a b w : ℤ) :
    Multiset.count w ({-a, -b} : Multiset ℤ) = Multiset.count (-w) ({a, b} : Multiset ℤ) := by
  have h : ({-a, -b} : Multiset ℤ) = Multiset.map Neg.neg {a, b} := by simp
  rw [h, ← Multiset.count_map_eq_count' Neg.neg _ neg_injective (-w), neg_neg]

/-- pkg-I4's `DistinctHTWeights ρ` (computed on `Hom_G(V, ℂ_p(i))`) gives the printed condition
"Hodge–Tate with distinct weights" for the contragredient (weights `−a ≠ −b`). -/
theorem localDistinctHTU_dualHom (ρ : GaloisRep p 2)
    (h : GaloisRep.DistinctHTWeights (ρ := ρ) p) :
    LocalDistinctHTU p (dualHom (ρ.restrictLocal p)) := by
  obtain ⟨a, b, hab, E, hE, ρE, hmod, hw⟩ := h
  refine ⟨-a, -b, fun h => hab (neg_inj.mp h), E, hE, dualHom ρE,
    dualHom_model _ ρE _ hmod, fun w => ?_⟩
  have h1 := hw (-w)
  rw [htMult, neg_neg] at h1
  rw [htMultU, htU, finrank_tensorInv_dualHom, homInv_ht, h1, count_neg_pair]

end Predicates

/-! ## §7. The two printed leaves -/

/-- Berger (leaf). -/
def BergerPrintedU : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)),
    Continuous ρ → LocalIsDeRhamU p n ρ → LocalIsPstU p n ρ

/-- Pan (leaf). -/
def PanPrintedU : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (ιp : PadicAlgCl p ≃+* ℂ) (ρ : GaloisRep p 2),
    ρ.IsIrreducible → ρ.FinitelyRamified → LocalIsPstU p 2 (ρ.restrictLocal p) → ρ.IsOdd →
    LocalDistinctHTU p (ρ.restrictLocal p) →
    ∃ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k), 0 < N ∧ 1 ≤ k ∧
      IsNormalizedEigenform g χ ∧
      ∃ (ψ : GaloisChar p) (S : Finset ℕ), ∀ q : ℕ, q.Prime → q ∉ S →
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v q → IsArithFrob σ v q →
          (ρ.mat σ⁻¹).trace = (ψ.toHom σ⁻¹ : PadicAlgCl p) * ιp.symm (coeff g q)

/-! ## §8. Glue: `PanBerger` -/

/-- The inverse of a continuous character. -/
def charInv {ℓ : ℕ} [Fact ℓ.Prime] (ψ : GaloisChar ℓ) : GaloisChar ℓ where
  toHom := ψ.toHom⁻¹
  continuous_toHom := ψ.continuous_toHom.inv

theorem charInv_apply {ℓ : ℕ} [Fact ℓ.Prime] (ψ : GaloisChar ℓ) (σ : GQ) :
    (charInv ψ).toHom σ = ψ.toHom σ⁻¹ := by
  rw [map_inv]
  rfl

theorem panBerger_of_printedU (hP : PanPrintedU) (hB : BergerPrintedU)
    (hD : ZInQ.Contrib.HodgeSplit.DSThm965) (hDS : ZInQ.Contrib.HodgeSplit.DSThm966) :
    PanBerger := by
  intro p _ hp ρ hirr hfr hdr hodd hdist
  have hdr' : LocalIsDeRhamU p 2 ((dualRep ρ).restrictLocal p) := by
    rw [dualRep_restrictLocal]
    exact localIsDeRhamU_dualHom p _ hdr
  have hpst' := hB p 2 _ ((dualRep ρ).continuous_toHom.comp
    (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous) hdr'
  have hht' : LocalDistinctHTU p ((dualRep ρ).restrictLocal p) := by
    rw [dualRep_restrictLocal]
    exact localDistinctHTU_dualHom p ρ hdist
  obtain ⟨Φ⟩ := exists_complex_equiv p
  obtain ⟨N, k, χ, g, hN, hk, hg, ψ, S, htr⟩ := hP p hp Φ.symm (dualRep ρ)
    (dualRep_isIrreducible ρ hirr) (dualRep_finitelyRamified ρ hfr) hpst'
    (dualRep_isOdd ρ hodd) hht'
  obtain ⟨Sr, hSr⟩ := hfr
  let ιC : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let ιL : Qbar →ₐ[ℚ] PadicAlgCl p := (Φ : ℂ →+* PadicAlgCl p).toRatAlgHom.comp ιC
  refine ⟨N, k, χ, g, hN, hk, hg, charInv ψ, ιC, ιL, S ∪ Sr ∪ Finset.range (N * p + 1), ?_⟩
  intro q hq hqS
  simp only [Finset.mem_union, Finset.mem_range, not_or, not_lt] at hqS
  obtain ⟨⟨hqS, hqSr⟩, hqNp⟩ := hqS
  have hNp : 0 < N * p := Nat.mul_pos hN (Fact.out : p.Prime).pos
  have hqdvd : ¬ q ∣ N * p := fun h => by
    have := Nat.le_of_dvd hNp h
    omega
  refine ⟨hSr q hq hqSr, ?_⟩
  obtain ⟨α, hα⟩ := coeff_mem_range hD hDS p ιC ιL hN hk hg hq hqdvd
  refine ⟨α, hα, fun v σ hv hσ => ?_⟩
  have h1 := htr q hq hqS v σ hv hσ
  rw [trace_dualRep_inv] at h1
  rw [h1, charInv_apply]
  congr 1
  change Φ.symm.symm (coeff g q) = Φ (ιC α)
  rw [hα]
  rfl

end PanBergerSplit
end PkgI4
end HDec
