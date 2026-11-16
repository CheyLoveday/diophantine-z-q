import ZInQKernel.Contrib.OneProof.AfTateOr
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Completion

noncomputable section

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 40000

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

namespace AfTateLam

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar
open PkgI4 (Qbar GQ CF coeff IsNewform)
open scoped TensorProduct MatrixGroups

/-! ## 0. Generic: functionals semilinear along `ι = ε ∘ ρ_L` and the base change `L ⊗_R V` -/

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

/-! ## 1. The uniformization `τ ↦ x_τ ∈ X(ℂ)` of a model of `X₁(N)_alg` -/

/-- `X(ℂ)`: the complex points of a `ℚ`-scheme. -/
abbrev CPt (X : Over SpecQ) : Type := ptObj (K := ℚ) ℂ ⟶ X

/-- Diamond–Shurman's `X₁(N)_alg` with chosen generators `j_X, t_X` of `K(X)` (the body of
`AfTateOr.IsX1AlgDS` with the generators named): `K(X) = ℚ(j_X, t_X)` and the integer relations of
`(j_X, t_X)` are those of `(j(τ), f₁(τ))` on `ℍ`. -/
def IsX1Gen (N : ℕ) (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField) : Prop :=
  Subfield.closure {jX, tX} = ⊤ ∧
    ∀ F : Polynomial (Polynomial ℤ), AfTateOr.ev2 F jX tX = 0 ↔
      ∀ τ : UpperHalfPlane, (T5Glue.pp τ).g₂ ≠ 0 → (T5Glue.pp τ).g₃ ≠ 0 →
        X1Igusa.Weber.evAn N (AfTateOr.toQ F) τ = 0

/-- The rational function `g ∈ K(X)` is regular at the complex point `x` with value `c`: it is the
germ of a section `s` over an open `U` containing (the image of) `x`, and `s(x) = c`. -/
def RegAt {X : Over SpecQ} [IsIntegral X.left] (x : CPt X) (g : X.left.functionField) (c : ℂ) :
    Prop :=
  ∃ (U : X.left.Opens) (_ : Nonempty U) (s : Γ(X.left, U)) (h : ⊤ ≤ x.left ⁻¹ᵁ U),
    X.left.germToFunctionField U s = g ∧
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (x.left.appLE U ⊤ h s) = c

/-- **`x = x_τ`, the point of `X(ℂ)` at `τ ∈ ℍ`** (Diamond–Shurman §7.5–7.7: `X₁(N)(ℂ) ⊇ Γ₁(N)\ℍ`
through `ℂ(X₁(N)) = ℂ(j, f₁)`). Every `g = P(j_X, t_X)/Q(j_X, t_X) ∈ K(X)` whose meromorphic function
`P(j, f₁)/Q(j, f₁)` on `ℍ` has a limit `c` at `τ` is regular at `x` with value `c`. (Limits over the
punctured neighbourhood avoid the values of `T5Glue.weber` off Weber's generic branch. For every
`τ` exactly one complex point satisfies this: the uniformization `ℍ → X(ℂ)` is holomorphic and
non-constant, and the rational functions regular at a point determine it.) -/
def AtTau (N : ℕ) {X : Over SpecQ} [IsIntegral X.left] (jX tX : X.left.functionField) (x : CPt X)
    (τ : UpperHalfPlane) : Prop :=
  ∀ (P Q : Polynomial (Polynomial ℤ)) (c : ℂ), AfTateOr.ev2 Q jX tX ≠ 0 →
    Filter.Tendsto (fun τ' => X1Igusa.Weber.evAn N (AfTateOr.toQ P) τ' /
        X1Igusa.Weber.evAn N (AfTateOr.toQ Q) τ') (nhdsWithin τ {τ}ᶜ) (nhds c) →
      RegAt x (AfTateOr.ev2 P jX tX / AfTateOr.ev2 Q jX tX) c

/-! ## 2. Hecke operators on `J₁(N)` (Diamond–Shurman §6.3, §7.9) -/

/-- `τ ↦ (τ + j)/p`. -/
def shiftDiv (p j : ℕ) (τ : UpperHalfPlane) : UpperHalfPlane :=
  if hp : 0 < p then
    ⟨((τ : ℂ) + j) / p, by
      have h := τ.coe_im_pos
      rw [Complex.div_natCast_im, Complex.add_im, Complex.natCast_im, add_zero]
      exact div_pos h (by exact_mod_cast hp)⟩
  else τ

/-- `τ ↦ pτ`. -/
def mulNat (p : ℕ) (τ : UpperHalfPlane) : UpperHalfPlane :=
  if hp : 0 < p then
    ⟨(p : ℂ) * τ, by
      have h := τ.coe_im_pos
      simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
      exact mul_pos (by exact_mod_cast hp) h⟩
  else τ

variable {X : Over SpecQ} [IsIntegral X.left] {J : AbVar ℚ}

/-- The image `aj(x) ∈ J(ℂ)` of a complex point under the Abel–Jacobi map. -/
abbrev ajC (aj : X ⟶ J.X) (x : CPt X) : J.Pt ℂ := x ≫ aj

/-- An endomorphism acting on `J(ℂ)`. -/
abbrev endC (t : AbVar.End J) (y : J.Pt ℂ) : J.Pt ℂ := y ≫ t.hom

/-- **`t` is the Hecke operator `T_p` on `J₁(N) = Pic⁰(X₁(N))`** (Diamond–Shurman §6.3, with the coset
representatives of Prop. 5.2.1): on divisor classes of degree `0` supported on the points `x_τ`,
`T_p[x_τ] = Σ_{j<p} [x_{(τ+j)/p}] + [x_{γ(pτ)}]`, the last term only for `p ∤ N`, with
`γ = (a b; c d) ∈ SL₂(ℤ)`, `N ∣ c`, `d ≡ p (mod N)`. Classes `[x_τ] − [x_{τ'}]` are written
`aj(x_τ)/aj(x_{τ'})` in `J(ℂ)` (Abel–Jacobi). -/
def IsHeckeT (N : ℕ) (jX tX : X.left.functionField) (aj : X ⟶ J.X) (p : ℕ) (t : AbVar.End J) :
    Prop :=
  ∀ (τ τ' : UpperHalfPlane) (x x' : CPt X) (y y' : Fin p → CPt X),
    AtTau N jX tX x τ → AtTau N jX tX x' τ' →
    (∀ i : Fin p, AtTau N jX tX (y i) (shiftDiv p i τ)) →
    (∀ i : Fin p, AtTau N jX tX (y' i) (shiftDiv p i τ')) →
    (p ∣ N → endC t (ajC aj x / ajC aj x') = ∏ i, ajC aj (y i) / ajC aj (y' i)) ∧
    (¬ p ∣ N → ∀ g : SL(2, ℤ), (N : ℤ) ∣ g 1 0 → ((g 1 1 : ℤ) : ZMod N) = (p : ZMod N) →
      ∀ z z' : CPt X, AtTau N jX tX z (g • mulNat p τ) → AtTau N jX tX z' (g • mulNat p τ') →
        endC t (ajC aj x / ajC aj x') = (∏ i, ajC aj (y i) / ajC aj (y' i)) * (ajC aj z / ajC aj z'))

/-- **`δ` is the diamond operator `⟨d⟩` on `J₁(N)`** (Diamond–Shurman §6.3): `⟨d⟩[x_τ] = [x_{γτ}]` for
`γ = (a b; c d') ∈ SL₂(ℤ)` with `N ∣ c`, `d' ≡ d (mod N)`. -/
def IsDiamond (N : ℕ) (jX tX : X.left.functionField) (aj : X ⟶ J.X) (d : (ZMod N)ˣ)
    (δ : AbVar.End J) : Prop :=
  ∀ g : SL(2, ℤ), (N : ℤ) ∣ g 1 0 → ((g 1 1 : ℤ) : ZMod N) = (d : ZMod N) →
    ∀ (τ τ' : UpperHalfPlane) (x x' z z' : CPt X),
      AtTau N jX tX x τ → AtTau N jX tX x' τ' → AtTau N jX tX z (g • τ) → AtTau N jX tX z' (g • τ') →
        endC δ (ajC aj x / ajC aj x') = ajC aj z / ajC aj z'

/-! ## 3. The Hecke algebra, `I_f` and `A_f = J₁(N)/I_f J₁(N)` (Diamond–Shurman §6.6) -/

/-- Generators `T_p` (`p` prime) and `⟨d⟩` (`d ∈ (ℤ/N)^×`) of `𝕋_ℤ`. -/
abbrev HeckeGen (N : ℕ) : Type := Nat.Primes ⊕ (ZMod N)ˣ

/-- The free algebra on the generators; `𝕋_ℤ` is its image in `End(J₁(N))`. -/
abbrev HeckeFree (N : ℕ) : Type := FreeAlgebra ℤ (HeckeGen N)

/-- Eigenvalues of `f`: `T_p ↦ a_p(f)`, `⟨d⟩ ↦ χ(d)`. Its kernel maps onto `I_f = {T ∈ 𝕋_ℤ : Tf = 0}`. -/
def evF {N : ℕ} (χ : DirichletCharacter ℂ N) (f : CF N 2) : HeckeFree N →ₐ[ℤ] ℂ :=
  FreeAlgebra.lift ℤ (Sum.elim (fun p => coeff f (p : ℕ)) (fun d => χ (d : ZMod N)))

/-- The action on `J` through given `T_p`, `⟨d⟩`. -/
def heckeJ {N : ℕ} (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J) :
    HeckeFree N →ₐ[ℤ] AbVar.End J :=
  FreeAlgebra.lift ℤ (Sum.elim tp δ)

/-- `φ : J → B` kills `I_f J`. -/
def KillsIf {N : ℕ} (χ : DirichletCharacter ℂ N) (f : CF N 2) (tp : Nat.Primes → AbVar.End J)
    (δ : (ZMod N)ˣ → AbVar.End J) {B : AbVar ℚ} (φ : AbVar.Hom J B) : Prop :=
  ∀ h : HeckeFree N, evF χ f h = 0 → (heckeJ tp δ h).hom ≫ φ.hom = (0 : AbVar.Hom J B).hom

/-- **`π : J → A` is `J ↠ J/I_f J = A_f`** (Diamond–Shurman Def. 6.6.3): surjective, kills `I_f J`,
and universal among homomorphisms to abelian varieties that kill `I_f J`. -/
def IsAfQuotient {N : ℕ} (χ : DirichletCharacter ℂ N) (f : CF N 2) (tp : Nat.Primes → AbVar.End J)
    (δ : (ZMod N)ˣ → AbVar.End J) (A : AbVar ℚ) (π : AbVar.Hom J A) : Prop :=
  AlgebraicGeometry.Surjective π.hom.left ∧ KillsIf χ f tp δ π ∧
    ∀ (B : AbVar ℚ) (φ : AbVar.Hom J B), KillsIf χ f tp δ φ →
      ∃! ψ : AbVar.Hom A B, π.hom ≫ ψ.hom = φ.hom

/-- **`θ` is Diamond–Shurman's action of `K_f = (𝕋_ℤ/I_f) ⊗ ℚ` on `A_f`** (Prop. 6.6.4): `θ(a_p(f))` is
the endomorphism of `A_f` induced by `T_p`, and `θ(χ(d))` the one induced by `⟨d⟩`. -/
def IsAfAction {N : ℕ} (χ : DirichletCharacter ℂ N) (f : CF N 2) (tp : Nat.Primes → AbVar.End J)
    (δ : (ZMod N)ˣ → AbVar.End J) {A : AbVar ℚ} (π : AbVar.Hom J A)
    (θ : coeffField f →+* A.End0) : Prop :=
  (∀ p : Nat.Primes, ∃ e : AbVar.End A, (tp p).hom ≫ π.hom = π.hom ≫ e.hom ∧
      θ ⟨coeff f (p : ℕ), coeff_mem_coeffField f p⟩ = (1 : ℚ) ⊗ₜ e) ∧
  (∀ d : (ZMod N)ˣ, ∃ (c : coeffField f) (e : AbVar.End A), (c : ℂ) = χ (d : ZMod N) ∧
      (δ d).hom ≫ π.hom = π.hom ≫ e.hom ∧ θ c = (1 : ℚ) ⊗ₜ e)

/-! ## 4. `K_{f,λ}`, `V_λ = K_λ ⊗_{ℚ_ℓ ⊗ K_f} V_ℓ(A)` and `ρ_{f,λ}` (Diamond–Shurman §9.5) -/

section Lambda

open IsDedekindDomain NumberField

/-- The `ℓ`-adic place of `ℚ`. -/
def vQ (ℓ : ℕ) [Fact ℓ.Prime] : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨ℓ, Fact.out⟩

variable {K : Type} [Field K] [NumberField K]

/-- `ℚ_ℓ → K_λ` for a place `λ ∣ ℓ` (Mathlib's `ℚ_ℓ ≅ ℚ_{v_ℓ}`, then Tau Ceti's completion map). -/
def algQl (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 K))
    [lam.asIdeal.LiesOver (vQ ℓ).asIdeal] : ℚ_[ℓ] →+* lam.adicCompletion K :=
  ((vQ ℓ).adicCompletionExtension ℚ K lam).comp
    (RingHomClass.toRingHom (Padic.adicCompletionEquiv (𝓞 ℚ) ⟨ℓ, Fact.out⟩))

/-- `ℚ_ℓ ⊗_ℚ K → K_λ`, `x ⊗ a ↦ x · a`. -/
def rhoLam (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 K))
    [lam.asIdeal.LiesOver (vQ ℓ).asIdeal] : ℚ_[ℓ] ⊗[ℚ] K →+* lam.adicCompletion K :=
  letI : Algebra ℚ_[ℓ] (lam.adicCompletion K) := (algQl ℓ lam).toAlgebra
  R16Used.liftHom (algebraMap K (lam.adicCompletion K))

/-- `σ ∈ G_ℚ` on `V_ℓ(A)`, linear over `ℚ_ℓ ⊗ F` (endomorphisms are defined over `ℚ`). -/
def galR (ℓ : ℕ) [Fact ℓ.Prime] (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F]
    (θ : F →+* A.End0) (σ : GQ) :
    letI := R16Used.tensorModule ℓ A θ; A.V ℓ →ₗ[ℚ_[ℓ] ⊗[ℚ] F] A.V ℓ :=
  letI := R16Used.tensorModule ℓ A θ
  { toFun := A.galRep ℓ σ
    map_add' := map_add _
    map_smul' := fun r v => R16Used.galRep_tsmul ℓ A θ σ r v }

/-- **`ρ_{f,λ}(σ)`**: `σ` acting on `V_λ = K_λ ⊗_{ℚ_ℓ ⊗ K} V_ℓ(A)`. -/
def frobLam (ℓ : ℕ) [Fact ℓ.Prime] (A : AbVar ℚ) (θ : K →+* A.End0) (lam : HeightOneSpectrum (𝓞 K))
    [lam.asIdeal.LiesOver (vQ ℓ).asIdeal] (σ : GQ) :
    letI := R16Used.tensorModule ℓ A θ
    letI := (rhoLam ℓ lam).toAlgebra
    (lam.adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ) →ₗ[lam.adicCompletion K]
      (lam.adicCompletion K ⊗[ℚ_[ℓ] ⊗[ℚ] K] A.V ℓ) :=
  letI := R16Used.tensorModule ℓ A θ
  letI := (rhoLam ℓ lam).toAlgebra
  (galR ℓ A θ σ).baseChange _

end Lambda

end AfTateLam
