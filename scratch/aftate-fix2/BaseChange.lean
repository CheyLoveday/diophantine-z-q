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

include hιk hε in
/-- The functional `φ_j : v ↦ ε(b_j^*(1 ⊗ v))`. -/
def phiB (j : sB (L := L) (R := R) (V := V)) : V →ₗ[k] Ω where
  toFun v := ε ((bL (L := L) (R := R) (V := V)).coord j (mk1 (L := L) v))
  map_add' u v := by rw [map_add, map_add, map_add]
  map_smul' c v := by
    rw [RingHom.id_apply, ← algebraMap_smul R c v, LinearMap.map_smul, ← algebraMap_smul L,
      LinearMap.map_smul, smul_eq_mul, map_mul, hε, ← IsScalarTower.algebraMap_apply, hιk,
      Algebra.smul_def]

theorem phiB_apply (j : sB (L := L) (R := R) (V := V)) (v : V) :
    phiB ι hιk ε hε j v = ε ((bL (L := L) (R := R) (V := V)).coord j (mk1 (L := L) v)) := rfl

theorem phiB_semilin (j : sB (L := L) (R := R) (V := V)) (r : R) (v : V) :
    phiB ι hιk ε hε j (r • v) = ι r * phiB ι hιk ε hε j v := by
  rw [phiB_apply, phiB_apply, LinearMap.map_smul, ← algebraMap_smul L, LinearMap.map_smul,
    smul_eq_mul, map_mul, hε]

theorem phiB_vB (i j : sB (L := L) (R := R) (V := V)) :
    phiB ι hιk ε hε j (vB i) = if i = j then 1 else 0 := by
  rw [phiB_apply, mk1_vB, Module.Basis.coord_apply, Module.Basis.repr_self]
  by_cases h : i = j
  · subst h; simp
  · rw [Finsupp.single_eq_of_ne (Ne.symm h), map_zero, if_neg h]

/-- **Expansion of a semilinear functional** in the `φ_j`. -/
theorem eq_sum_phiB (φ : V →ₗ[k] Ω) (hφ : ∀ (r : R) (v : V), φ (r • v) = ι r * φ v) (v : V) :
    φ v = ∑ j, φ (vB j) * phiB ι hιk ε hε j v := by
  have h1 : φ v = liftφ ι ε hε φ hφ (mk1 (L := L) v) := by
    rw [mk1, TensorProduct.mk_apply, liftφ_tmul, map_one, one_mul]
  rw [h1, ← (bL (L := L) (R := R) (V := V)).sum_repr (mk1 (L := L) v), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [liftφ_smul, ← mk1_vB, mk1, TensorProduct.mk_apply, liftφ_tmul, map_one, one_mul, phiB_apply,
    Module.Basis.coord_apply, mk1, TensorProduct.mk_apply, mul_comm]

include hE in
theorem phiB_mem (j : sB (L := L) (R := R) (V := V)) : phiB ι hιk ε hε j ∈ E :=
  (hE _).2 (phiB_semilin ι hιk ε hε j)

/-- The coordinate isomorphism `E ≃ Ω^s`, `φ ↦ (φ(v_j))_j`. -/
def coordE : E ≃ₗ[Ω] (sB (L := L) (R := R) (V := V) → Ω) where
  toFun φ j := (φ : V →ₗ[k] Ω) (vB j)
  map_add' _ _ := by ext j; simp
  map_smul' _ _ := by ext j; simp
  invFun a := ⟨∑ j, a j • phiB ι hιk ε hε j, Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (phiB_mem ι hιk ε hε E hE j)⟩
  left_inv φ := by
    apply Subtype.ext; apply LinearMap.ext; intro v
    simp only [LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    exact (eq_sum_phiB ι hιk ε hε (φ : V →ₗ[k] Ω) ((hE _).1 φ.2) v).symm
  right_inv a := by
    funext i
    simp only [LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      phiB_vB, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem finrank_E : Module.finrank Ω E = Module.finrank L (L ⊗[R] V) := by
  rw [(coordE ι hιk ε hε E hE).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Module.finrank_eq_card_basis (bL (L := L) (R := R) (V := V))]

/-- The basis of `E` dual to `(v_i)`. -/
def basisE : Module.Basis (sB (L := L) (R := R) (V := V)) Ω E :=
  Module.Basis.ofEquivFun (coordE ι hιk ε hε E hE)

theorem basisE_repr (φ : E) (i : sB (L := L) (R := R) (V := V)) :
    (basisE ι hιk ε hε E hE).repr φ i = (φ : V →ₗ[k] Ω) (vB i) := by
  rw [basisE, Module.Basis.ofEquivFun_repr_apply]; rfl

/-- **Precomposition by `g` on `E` is the transpose of `ε(g_L)`.** -/
theorem toMatrix_precomp (g : V →ₗ[R] V) (T : E →ₗ[Ω] E)
    (hT : ∀ φ : E, (T φ : V →ₗ[k] Ω) = (φ : V →ₗ[k] Ω) ∘ₗ (g.restrictScalars k)) :
    LinearMap.toMatrix (basisE ι hιk ε hε E hE) (basisE ι hιk ε hε E hE) T =
      ((LinearMap.toMatrix (bL (L := L) (R := R) (V := V)) (bL (L := L) (R := R) (V := V))
        (g.baseChange L)).map ε).transpose := by
  ext i j
  rw [LinearMap.toMatrix_apply, basisE_repr, hT, Matrix.transpose_apply, Matrix.map_apply,
    LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  have hj : ((basisE ι hιk ε hε E hE j : E) : V →ₗ[k] Ω) = phiB ι hιk ε hε j := by
    rw [basisE, Module.Basis.coe_ofEquivFun]
    change (∑ i, (Pi.single j (1 : Ω) : _ → Ω) i • phiB ι hιk ε hε i) = phiB ι hιk ε hε j
    simp [Pi.single_apply]
  rw [hj, phiB_apply, ← mk1_vB, mk1, TensorProduct.mk_apply, TensorProduct.mk_apply,
    LinearMap.baseChange_tmul, Module.Basis.coord_apply]

theorem trace_det_precomp (g : V →ₗ[R] V) (T : E →ₗ[Ω] E)
    (hT : ∀ φ : E, (T φ : V →ₗ[k] Ω) = (φ : V →ₗ[k] Ω) ∘ₗ (g.restrictScalars k)) :
    LinearMap.trace Ω E T = ε (LinearMap.trace L _ (g.baseChange L)) ∧
      LinearMap.det T = ε (LinearMap.det (g.baseChange L)) := by
  have h := toMatrix_precomp ι hιk ε hε E hE g T hT
  constructor
  · rw [LinearMap.trace_eq_matrix_trace Ω (basisE ι hιk ε hε E hE), h, Matrix.trace_transpose,
      LinearMap.trace_eq_matrix_trace L (bL (L := L) (R := R) (V := V)), Matrix.trace,
      Matrix.trace, map_sum]
    rfl
  · rw [← LinearMap.det_toMatrix (basisE ι hιk ε hε E hE), h, Matrix.det_transpose,
      ← LinearMap.det_toMatrix (bL (L := L) (R := R) (V := V)), RingHom.map_det]

end Generic

end AfTateLam
