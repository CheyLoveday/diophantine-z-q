import Mathlib

set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000

noncomputable section

namespace AfTateLam

open scoped TensorProduct

/-! ## Generic: functionals semilinear along `ι = ε ∘ ρ_L` and the base change `L ⊗_R V` -/

section Generic

variable {k R V Ω L : Type*} [Field k] [CommRing R] [Algebra k R] [AddCommGroup V] [Module k V]
  [Module R V] [IsScalarTower k R V] [Field Ω] [Algebra k Ω] [Field L] [Algebra R L]
  (ι : R →+* Ω) (hιk : ∀ x : k, ι (algebraMap k R x) = algebraMap k Ω x)
  (ε : L →+* Ω) (hε : ∀ r : R, ε (algebraMap R L r) = ι r)
  (E : Submodule Ω (V →ₗ[k] Ω)) (hE : ∀ φ : V →ₗ[k] Ω, φ ∈ E ↔ ∀ (r : R) (v : V), φ (r • v) = ι r * φ v)

/-- `v ↦ 1 ⊗ v`, `V → L ⊗_R V`. -/
def mk1 : V →ₗ[R] L ⊗[R] V := TensorProduct.mk R L V 1

omit [IsScalarTower k R V] in
theorem span_mk1 : Submodule.span L (Set.range (mk1 (L := L) (R := R) (V := V))) = ⊤ := by
  refine eq_top_iff.2 fun t _ => ?_
  induction t using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul l v =>
    have : l ⊗ₜ[R] v = l • mk1 (L := L) v := by
      simp [mk1, TensorProduct.smul_tmul']
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- The additive lift `l ⊗ v ↦ ε(l) φ(v)` of a semilinear functional. -/
def liftφ (φ : V →ₗ[k] Ω) (hφ : ∀ (r : R) (v : V), φ (r • v) = ι r * φ v) :
    L ⊗[R] V →+ Ω :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun l : L => AddMonoidHom.mk' (fun v : V => ε l * φ v)
        (by intro a b; rw [map_add, mul_add]))
      (by intro a b; ext v; simp [add_mul]))
    (by
      intro r l v
      simp only [AddMonoidHom.mk'_apply, Algebra.smul_def, map_mul, hε, hφ]
      ring)

include hε in
theorem liftφ_tmul (φ : V →ₗ[k] Ω) (hφ : ∀ (r : R) (v : V), φ (r • v) = ι r * φ v) (l : L) (v : V) :
    liftφ ι ε hε φ hφ (l ⊗ₜ v) = ε l * φ v := by
  simp [liftφ]

theorem liftφ_smul (φ : V →ₗ[k] Ω) (hφ : ∀ (r : R) (v : V), φ (r • v) = ι r * φ v) (l : L)
    (t : L ⊗[R] V) : liftφ ι ε hε φ hφ (l • t) = ε l * liftφ ι ε hε φ hφ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l' v =>
    rw [TensorProduct.smul_tmul', liftφ_tmul, liftφ_tmul, smul_eq_mul, map_mul, mul_assoc]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]

variable [FiniteDimensional L (L ⊗[R] V)]

/-- A finite set of vectors `1 ⊗ v` forming a basis of `L ⊗_R V`. -/
theorem exists_basis_mk1 :
    ∃ s : Set (L ⊗[R] V), s ⊆ Set.range (mk1 (L := L) (R := R) (V := V)) ∧
      LinearIndependent L ((↑) : s → L ⊗[R] V) ∧ Submodule.span L s = ⊤ := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent L (Set.range (mk1 (L := L) (R := R) (V := V)))
  exact ⟨s, hs, hli, hspan.trans span_mk1⟩

/-- The chosen spanning set. -/
def sB : Set (L ⊗[R] V) := (exists_basis_mk1 (L := L) (R := R) (V := V)).choose

theorem sB_sub : sB (L := L) (R := R) (V := V) ⊆ Set.range (mk1 (L := L) (R := R) (V := V)) :=
  (exists_basis_mk1 (L := L) (R := R) (V := V)).choose_spec.1

/-- The basis of `L ⊗_R V` by vectors `1 ⊗ v`. -/
def bL : Module.Basis (sB (L := L) (R := R) (V := V)) L (L ⊗[R] V) :=
  Module.Basis.mk (exists_basis_mk1 (L := L) (R := R) (V := V)).choose_spec.2.1
    (by simp only [Subtype.range_coe_subtype, Set.setOf_mem_eq]; exact (exists_basis_mk1 (L := L) (R := R) (V := V)).choose_spec.2.2.ge)

instance : Fintype (sB (L := L) (R := R) (V := V)) :=
  @Fintype.ofFinite _ (Module.Finite.finite_basis (bL (L := L) (R := R) (V := V)))

/-- `v_i ∈ V` with `1 ⊗ v_i = b_i`. -/
def vB (i : sB (L := L) (R := R) (V := V)) : V := (sB_sub i.2).choose

theorem mk1_vB (i : sB (L := L) (R := R) (V := V)) : mk1 (L := L) (vB i) = bL (L := L) (R := R) (V := V) i := by
  rw [bL, Module.Basis.mk_apply]; exact (sB_sub i.2).choose_spec


end Generic

end AfTateLam
