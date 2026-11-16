import Mathlib

set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000

attribute [local instance] Classical.propDecidable

noncomputable section

namespace AfTateLam

open scoped TensorProduct

/-! ## Generic: functionals semilinear along `ι = ε ∘ ρ_L` and the base change `L ⊗_R V` -/

section Generic

variable {k R V Ω L : Type*} [Field k] [CommRing R] [Algebra k R] [AddCommGroup V] [Module k V]
  [Module R V] [IsScalarTower k R V] [Field Ω] [Algebra k Ω] [Field L] [Algebra R L]
  (ι : R →+* Ω) (ε : L →+* Ω) (E : Submodule Ω (V →ₗ[k] Ω))

/-- `v ↦ 1 ⊗ v`, `V → L ⊗_R V`. -/
def mk1 : V →ₗ[R] L ⊗[R] V := TensorProduct.mk R L V 1

theorem span_mk1 : Submodule.span L (Set.range (mk1 (L := L) (R := R) (V := V))) = ⊤ := by
  have key : ∀ t : L ⊗[R] V, t ∈ Submodule.span L (Set.range (mk1 (L := L) (R := R) (V := V))) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul l v =>
      have : l ⊗ₜ[R] v = l • mk1 (L := L) v := by
        simp [mk1, TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  exact eq_top_iff.2 fun t _ => key t

/-- The additive lift `l ⊗ v ↦ ε(l) φ(v)` of a semilinear functional. -/
def liftφ (hε : ∀ r : R, ε (algebraMap R L r) = ι r) (φ : V →ₗ[k] Ω) (hφ : ∀ (r : R) (v : V), φ (r • v) = ι r * φ v) :
    L ⊗[R] V →+ Ω :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun l : L => AddMonoidHom.mk' (fun v : V => ε l * φ v)
        (by intro a b; rw [map_add, mul_add]))
      (by intro a b; ext v; simp [add_mul]))
    (by
      intro r l v
      simp only [AddMonoidHom.mk'_apply, Algebra.smul_def, map_mul, hε, hφ]
      ring)

theorem liftφ_tmul (hε : ∀ r : R, ε (algebraMap R L r) = ι r) (φ : V →ₗ[k] Ω) (hφ : ∀ (r : R) (v : V), φ (r • v) = ι r * φ v) (l : L) (v : V) :
    liftφ ι ε hε φ hφ (l ⊗ₜ v) = ε l * φ v := by
  simp [liftφ]

theorem liftφ_smul (hε : ∀ r : R, ε (algebraMap R L r) = ι r) (φ : V →ₗ[k] Ω) (hφ : ∀ (r : R) (v : V), φ (r • v) = ι r * φ v) (l : L)
    (t : L ⊗[R] V) : liftφ ι ε hε φ hφ (l • t) = ε l * liftφ ι ε hε φ hφ t := by
  induction t using TensorProduct.inductionOn with
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

theorem sB_li : LinearIndependent L ((↑) : sB (L := L) (R := R) (V := V) → L ⊗[R] V) :=
  (exists_basis_mk1 (L := L) (R := R) (V := V)).choose_spec.2.1

theorem sB_span : Submodule.span L (sB (L := L) (R := R) (V := V)) = ⊤ :=
  (exists_basis_mk1 (L := L) (R := R) (V := V)).choose_spec.2.2

/-- The basis of `L ⊗_R V` by vectors `1 ⊗ v`. -/
def bL : Module.Basis (sB (L := L) (R := R) (V := V)) L (L ⊗[R] V) :=
  Module.Basis.mk (sB_li (L := L) (R := R) (V := V))
    (by rw [Subtype.range_coe]; exact (sB_span (L := L) (R := R) (V := V)).ge)

instance : Fintype (sB (L := L) (R := R) (V := V)) :=
  @Fintype.ofFinite _ (Module.Finite.finite_basis (bL (L := L) (R := R) (V := V)))

/-- `v_i ∈ V` with `1 ⊗ v_i = b_i`. -/
def vB (i : sB (L := L) (R := R) (V := V)) : V := (sB_sub i.2).choose

theorem mk1_vB (i : sB (L := L) (R := R) (V := V)) : mk1 (L := L) (vB i) = bL (L := L) (R := R) (V := V) i := by
  rw [bL, Module.Basis.mk_apply]; exact (sB_sub i.2).choose_spec

/-- The functional `φ_j : v ↦ ε(b_j^*(1 ⊗ v))`. -/
def phiB (hιk : ∀ x : k, ι (algebraMap k R x) = algebraMap k Ω x) (hε : ∀ r : R, ε (algebraMap R L r) = ι r) (j : sB (L := L) (R := R) (V := V)) : V →ₗ[k] Ω where
  toFun v := ε ((bL (L := L) (R := R) (V := V)).coord j (mk1 (L := L) v))
  map_add' u v := by rw [map_add, map_add, map_add]
  map_smul' c v := by
    rw [RingHom.id_apply, ← algebraMap_smul R c v, LinearMap.map_smul, ← algebraMap_smul L,
      LinearMap.map_smul, smul_eq_mul, map_mul, hε, hιk, Algebra.smul_def]

theorem phiB_apply (hιk : ∀ x : k, ι (algebraMap k R x) = algebraMap k Ω x) (hε : ∀ r : R, ε (algebraMap R L r) = ι r) (j : sB (L := L) (R := R) (V := V)) (v : V) :
    phiB ι ε hιk hε j v = ε ((bL (L := L) (R := R) (V := V)).coord j (mk1 (L := L) v)) := rfl

theorem phiB_semilin (hιk : ∀ x : k, ι (algebraMap k R x) = algebraMap k Ω x) (hε : ∀ r : R, ε (algebraMap R L r) = ι r) (j : sB (L := L) (R := R) (V := V)) (r : R) (v : V) :
    phiB ι ε hιk hε j (r • v) = ι r * phiB ι ε hιk hε j v := by
  rw [phiB_apply, phiB_apply, LinearMap.map_smul, ← algebraMap_smul L, LinearMap.map_smul,
    smul_eq_mul, map_mul, hε]

theorem phiB_vB (hιk : ∀ x : k, ι (algebraMap k R x) = algebraMap k Ω x) (hε : ∀ r : R, ε (algebraMap R L r) = ι r) (i j : sB (L := L) (R := R) (V := V)) :
    phiB ι ε hιk hε j (vB i) = if i = j then 1 else 0 := by
  rw [phiB_apply, mk1_vB, Module.Basis.coord_apply, Module.Basis.repr_self]
  by_cases h : i = j
  · subst h; simp
  · rw [Finsupp.single_eq_of_ne (Ne.symm h), map_zero, if_neg h]

/-- **Expansion of a semilinear functional** in the `φ_j`. -/
theorem eq_sum_phiB (hιk : ∀ x : k, ι (algebraMap k R x) = algebraMap k Ω x) (hε : ∀ r : R, ε (algebraMap R L r) = ι r) (φ : V →ₗ[k] Ω) (hφ : ∀ (r : R) (v : V), φ (r • v) = ι r * φ v) (v : V) :
    φ v = ∑ j, φ (vB j) * phiB ι ε hιk hε j v := by
  have h1 : φ v = liftφ ι ε hε φ hφ (mk1 (L := L) v) := by
    rw [mk1, TensorProduct.mk_apply, liftφ_tmul, map_one, one_mul]
  rw [h1, ← (bL (L := L) (R := R) (V := V)).sum_repr (mk1 (L := L) v), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [liftφ_smul, ← mk1_vB]
  simp only [mk1, TensorProduct.mk_apply, liftφ_tmul, map_one, one_mul, phiB_apply,
    Module.Basis.coord_apply]
  ring

theorem phiB_mem (hιk : ∀ x : k, ι (algebraMap k R x) = algebraMap k Ω x) (hε : ∀ r : R, ε (algebraMap R L r) = ι r) (hE : ∀ φ : V →ₗ[k] Ω, φ ∈ E ↔ ∀ (r : R) (v : V), φ (r • v) = ι r * φ v) (j : sB (L := L) (R := R) (V := V)) : phiB ι ε hιk hε j ∈ E :=
  (hE _).2 (phiB_semilin ι ε hιk hε j)

/-- The coordinate isomorphism `E ≃ Ω^s`, `φ ↦ (φ(v_j))_j`. -/
def coordE (hιk : ∀ x : k, ι (algebraMap k R x) = algebraMap k Ω x) (hε : ∀ r : R, ε (algebraMap R L r) = ι r) (hE : ∀ φ : V →ₗ[k] Ω, φ ∈ E ↔ ∀ (r : R) (v : V), φ (r • v) = ι r * φ v) : E ≃ₗ[Ω] (sB (L := L) (R := R) (V := V) → Ω) where
  toFun φ j := (φ : V →ₗ[k] Ω) (vB j)
  map_add' _ _ := by ext j; simp
  map_smul' _ _ := by ext j; simp
  invFun a := ⟨∑ j, a j • phiB ι ε hιk hε j, Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (phiB_mem ι ε E hιk hε hE j)⟩
  left_inv φ := by
    apply Subtype.ext; apply LinearMap.ext; intro v
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    exact (eq_sum_phiB ι ε hιk hε (φ : V →ₗ[k] Ω) ((hE _).1 φ.2) v).symm
  right_inv a := by
    funext i
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      phiB_vB, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem finrank_E (hιk : ∀ x : k, ι (algebraMap k R x) = algebraMap k Ω x) (hε : ∀ r : R, ε (algebraMap R L r) = ι r) (hE : ∀ φ : V →ₗ[k] Ω, φ ∈ E ↔ ∀ (r : R) (v : V), φ (r • v) = ι r * φ v) : Module.finrank Ω E = Module.finrank L (L ⊗[R] V) := by
  rw [(coordE ι ε E hιk hε hE).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Module.finrank_eq_card_basis (bL (L := L) (R := R) (V := V))]

/-- The basis of `E` dual to `(v_i)`. -/
def basisE (hιk : ∀ x : k, ι (algebraMap k R x) = algebraMap k Ω x) (hε : ∀ r : R, ε (algebraMap R L r) = ι r) (hE : ∀ φ : V →ₗ[k] Ω, φ ∈ E ↔ ∀ (r : R) (v : V), φ (r • v) = ι r * φ v) : Module.Basis (sB (L := L) (R := R) (V := V)) Ω E :=
  Module.Basis.ofEquivFun (coordE ι ε E hιk hε hE)

theorem basisE_repr (hιk : ∀ x : k, ι (algebraMap k R x) = algebraMap k Ω x) (hε : ∀ r : R, ε (algebraMap R L r) = ι r) (hE : ∀ φ : V →ₗ[k] Ω, φ ∈ E ↔ ∀ (r : R) (v : V), φ (r • v) = ι r * φ v) (φ : E) (i : sB (L := L) (R := R) (V := V)) :
    (basisE ι ε E hιk hε hE).repr φ i = (φ : V →ₗ[k] Ω) (vB i) := by
  rw [basisE, Module.Basis.ofEquivFun_repr_apply]; rfl

/-- **Precomposition by `g` on `E` is the transpose of `ε(g_L)`.** -/
theorem toMatrix_precomp (hιk : ∀ x : k, ι (algebraMap k R x) = algebraMap k Ω x) (hε : ∀ r : R, ε (algebraMap R L r) = ι r) (hE : ∀ φ : V →ₗ[k] Ω, φ ∈ E ↔ ∀ (r : R) (v : V), φ (r • v) = ι r * φ v) (g : V →ₗ[R] V) (T : E →ₗ[Ω] E)
    (hT : ∀ φ : E, (T φ : V →ₗ[k] Ω) = (φ : V →ₗ[k] Ω) ∘ₗ (g.restrictScalars k)) :
    LinearMap.toMatrix (basisE ι ε E hιk hε hE) (basisE ι ε E hιk hε hE) T =
      ((LinearMap.toMatrix (bL (L := L) (R := R) (V := V)) (bL (L := L) (R := R) (V := V))
        (g.baseChange L)).map ε).transpose := by
  ext i j
  rw [LinearMap.toMatrix_apply, basisE_repr, hT, Matrix.transpose_apply, Matrix.map_apply,
    LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  have hj : ((basisE ι ε E hιk hε hE j : E) : V →ₗ[k] Ω) = phiB ι ε hιk hε j := by
    rw [basisE, Module.Basis.coe_ofEquivFun]
    change (∑ i, (Pi.single j (1 : Ω) : _ → Ω) i • phiB ι ε hιk hε i) = phiB ι ε hιk hε j
    simp [Pi.single_apply]
  rw [hj, phiB_apply, ← mk1_vB, mk1, TensorProduct.mk_apply, TensorProduct.mk_apply,
    LinearMap.baseChange_tmul, Module.Basis.coord_apply]

theorem trace_det_precomp (hιk : ∀ x : k, ι (algebraMap k R x) = algebraMap k Ω x) (hε : ∀ r : R, ε (algebraMap R L r) = ι r) (hE : ∀ φ : V →ₗ[k] Ω, φ ∈ E ↔ ∀ (r : R) (v : V), φ (r • v) = ι r * φ v) (g : V →ₗ[R] V) (T : E →ₗ[Ω] E)
    (hT : ∀ φ : E, (T φ : V →ₗ[k] Ω) = (φ : V →ₗ[k] Ω) ∘ₗ (g.restrictScalars k)) :
    LinearMap.trace Ω E T = ε (LinearMap.trace L _ (g.baseChange L)) ∧
      @LinearMap.det E _ Ω _ _ T = ε (LinearMap.det (g.baseChange L)) := by
  have h := toMatrix_precomp ι ε E hιk hε hE g T hT
  constructor
  · rw [LinearMap.trace_eq_matrix_trace Ω (basisE ι ε E hιk hε hE), h, Matrix.trace_transpose,
      LinearMap.trace_eq_matrix_trace L (bL (L := L) (R := R) (V := V)), Matrix.trace,
      Matrix.trace, map_sum]
    rfl
  · rw [← LinearMap.det_toMatrix (basisE ι ε E hιk hε hE), h, Matrix.det_transpose,
      ← LinearMap.det_toMatrix (bL (L := L) (R := R) (V := V)), RingHom.map_det]
    rfl

end Generic

end AfTateLam
