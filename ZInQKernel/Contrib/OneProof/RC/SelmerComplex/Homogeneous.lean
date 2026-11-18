import Mathlib

/-!
# Lane RC26 (round 3): homogeneous continuous cochains of a group acting on a space

For a group `U` acting on a topological space `X` and a topological `U`-module `M` (over a
commutative ring `k`), the **homogeneous continuous cochains** are the continuous `U`-equivariant
maps `Θ : X^{n+1} → M` (`U` acting diagonally on `X^{n+1}`), with the alternating coface
differential
```text
(dΘ)(x₀, …, x_{n+1}) = Σ_{i=0}^{n+1} (−1)^i Θ(x₀, …, x̂_i, …, x_{n+1}).
```
They form the alternating coface map complex of a cosimplicial module (`homCosimp`), so `d² = 0` is
Mathlib's `AlternatingCofaceMapComplex.d_squared`. For `X = G` a topological group containing `U`,
with `U` acting by left multiplication, this is the complex `Hom_U(ℤ[G^{•+1}], M)` (continuous
version) used for Shapiro's lemma and the transfer (Nekovář, *Selmer complexes*, Astérisque 310,
8.1.1–8.1.4; Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, I §2, I §5).

* `homCochain k U X M n`, `homCosimp`, `homCx` (a Mathlib `CochainComplex` indexed by `ℕ`),
  `homCx_d_apply` (the explicit differential);
* `homMap φ`: the cochain map `Θ ↦ Θ ∘ φ^{n+1}` induced by a continuous `U`-equivariant map
  `φ : X → Y`, with `homMap_id`, `homMap_comp`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory AlgebraicTopology

universe u

section Homogeneous

variable (k : Type u) [CommRing k] (U : Type u) [Group U] (X : Type u) [MulAction U X]
  [TopologicalSpace X] (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction U M]
  [SMulCommClass U k M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M]

/-- **Homogeneous continuous `n`-cochains**: continuous maps `Θ : X^{n+1} → M` with
`Θ(u • x) = u • Θ(x)` (`U` acting diagonally). -/
def homCochain (n : ℕ) : Submodule k ((Fin (n + 1) → X) → M) where
  carrier := {Θ | Continuous Θ ∧ ∀ (u : U) (x : Fin (n + 1) → X), Θ (u • x) = u • Θ x}
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, fun u x => by
    change a (u • x) + b (u • x) = u • (a x + b x)
    rw [ha.2 u x, hb.2 u x, smul_add]⟩
  zero_mem' := ⟨continuous_const, fun u x => by
    change (0 : M) = u • (0 : M)
    rw [smul_zero]⟩
  smul_mem' c a ha := ⟨ha.1.const_smul c, fun u x => by
    change c • a (u • x) = u • (c • a x)
    rw [ha.2 u x, smul_comm u c (a x)]⟩

variable {k U X M} in
theorem mem_homCochain {n : ℕ} {Θ : (Fin (n + 1) → X) → M} :
    Θ ∈ homCochain k U X M n ↔ Continuous Θ ∧ ∀ (u : U) (x : Fin (n + 1) → X), Θ (u • x) = u • Θ x :=
  Iff.rfl

/-- The coface operator induced by a morphism `θ : [m] → [n]` of the simplex category:
`Θ ↦ (x ↦ Θ (x ∘ θ))`. -/
def homCochainMap {m n : SimplexCategory} (θ : m ⟶ n) :
    homCochain k U X M m.len →ₗ[k] homCochain k U X M n.len where
  toFun Θ := ⟨fun x => Θ.1 (x ∘ θ.toOrderHom),
    Θ.2.1.comp (continuous_pi fun _ => continuous_apply _),
    fun u x => Θ.2.2 u (x ∘ θ.toOrderHom)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The cosimplicial module of homogeneous continuous cochains.** -/
def homCosimp : CosimplicialObject (ModuleCat.{u} k) where
  obj n := ModuleCat.of k (homCochain k U X M n.len)
  map θ := ModuleCat.ofHom (homCochainMap k U X M θ)
  map_id _ := by
    ext Θ
    rfl
  map_comp _ _ := by
    ext Θ
    rfl

/-- **The complex of homogeneous continuous cochains** `C^•_hom(U; X, M)`: the alternating coface
map complex of `homCosimp`. -/
def homCx : CochainComplex (ModuleCat.{u} k) ℕ :=
  AlternatingCofaceMapComplex.obj (homCosimp k U X M)

theorem homCx_X (n : ℕ) : (homCx k U X M).X n = ModuleCat.of k (homCochain k U X M n) :=
  rfl

/-- An element of `(homCx k U X M).X n` as a homogeneous cochain. -/
abbrev homEl {n : ℕ} (Θ : (homCx k U X M).X n) : homCochain k U X M n := Θ

/-- A homogeneous cochain as an element of `(homCx k U X M).X n`. -/
abbrev homOf {n : ℕ} (Θ : homCochain k U X M n) : (homCx k U X M).X n := Θ

/-- An element of `(homCosimp k U X M).obj (SimplexCategory.mk n)` as a homogeneous cochain. -/
abbrev cosEl {n : ℕ} (Θ : (homCosimp k U X M).obj (SimplexCategory.mk n)) : homCochain k U X M n := Θ

/-- The alternating coface differential of `homCosimp`, explicitly. -/
theorem homObjD_apply (n : ℕ) (Θ : (homCosimp k U X M).obj (SimplexCategory.mk n)) (x : Fin (n + 2) → X) :
    (cosEl k U X M ((AlternatingCofaceMapComplex.objD (homCosimp k U X M) n).hom Θ)).1 x =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (cosEl k U X M Θ).1 (x ∘ Fin.succAbove i) := by
  simp only [AlternatingCofaceMapComplex.objD, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply, LinearMap.smul_apply]
  have key : ∀ y : homCochain k U X M (n + 1),
      y.1 x = (LinearMap.proj x ∘ₗ (homCochain k U X M (n + 1)).subtype) y := fun _ => rfl
  rw [key]
  dsimp only [cosEl]
  erw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  erw [map_zsmul]
  rfl

/-- **The differential**: `(dΘ)(x) = Σ_i (−1)^i Θ(x ∘ δ_i)`, `δ_i = Fin.succAbove i`. -/
theorem homCx_d_apply (n : ℕ) (Θ : (homCx k U X M).X n) (x : Fin (n + 2) → X) :
    (homEl k U X M (((homCx k U X M).d n (n + 1)).hom Θ)).1 x =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (homEl k U X M Θ).1 (x ∘ Fin.succAbove i) := by
  have hd : (homCx k U X M).d n (n + 1) = AlternatingCofaceMapComplex.objD (homCosimp k U X M) n :=
    CochainComplex.of_d (fun m => (homCosimp k U X M).obj (SimplexCategory.mk m))
      (AlternatingCofaceMapComplex.objD (homCosimp k U X M)) n
  rw [hd]
  exact homObjD_apply k U X M n Θ x

/-- The differential with `k`-scalars. -/
theorem homCx_d_apply' (n : ℕ) (Θ : (homCx k U X M).X n) (x : Fin (n + 2) → X) :
    (homEl k U X M (((homCx k U X M).d n (n + 1)).hom Θ)).1 x =
      ∑ i : Fin (n + 2), (-1 : k) ^ (i : ℕ) • (homEl k U X M Θ).1 (x ∘ Fin.succAbove i) := by
  rw [homCx_d_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Int.cast_smul_eq_zsmul k, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-! ### Functoriality in equivariant maps -/

variable {k U M}
variable {X} {Y Z : Type u} [MulAction U Y] [TopologicalSpace Y] [MulAction U Z] [TopologicalSpace Z]

/-- Pullback of homogeneous cochains along a continuous `U`-equivariant map `φ : X → Y`,
degreewise. -/
def homPullLin (φ : X → Y) (hφ : Continuous φ) (hφe : ∀ (u : U) (x : X), φ (u • x) = u • φ x)
    (n : ℕ) : homCochain k U Y M n →ₗ[k] homCochain k U X M n where
  toFun Θ := ⟨fun x => Θ.1 (φ ∘ x), Θ.2.1.comp (continuous_pi fun i => hφ.comp (continuous_apply i)),
    fun u x => by
      change Θ.1 (φ ∘ (u • x)) = u • Θ.1 (φ ∘ x)
      have : φ ∘ (u • x) = u • (φ ∘ x) := funext fun i => hφe u (x i)
      rw [this, Θ.2.2]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Pullback along `φ` as a morphism of cosimplicial modules. -/
def homPull (φ : X → Y) (hφ : Continuous φ) (hφe : ∀ (u : U) (x : X), φ (u • x) = u • φ x) :
    homCosimp k U Y M ⟶ homCosimp k U X M where
  app n := ModuleCat.ofHom (homPullLin φ hφ hφe n.len)
  naturality _ _ _ := by
    ext Θ
    rfl

/-- **The cochain map induced by a continuous `U`-equivariant map** `φ : X → Y`:
`Θ ↦ Θ ∘ φ^{n+1}`. -/
def homMap (φ : X → Y) (hφ : Continuous φ) (hφe : ∀ (u : U) (x : X), φ (u • x) = u • φ x) :
    homCx k U Y M ⟶ homCx k U X M :=
  AlternatingCofaceMapComplex.map (homPull φ hφ hφe)

theorem homMap_f_apply (φ : X → Y) (hφ : Continuous φ)
    (hφe : ∀ (u : U) (x : X), φ (u • x) = u • φ x) (n : ℕ) (Θ : (homCx k U Y M).X n)
    (x : Fin (n + 1) → X) :
    (homEl k U X M (((homMap φ hφ hφe).f n).hom Θ)).1 x = (homEl k U Y M Θ).1 (φ ∘ x) :=
  rfl

variable (k U X M) in
theorem homMap_id : homMap (k := k) (U := U) (M := M) (id : X → X) continuous_id (fun _ _ => rfl) =
    𝟙 _ := by
  ext n Θ
  rfl

theorem homMap_comp (φ : X → Y) (hφ : Continuous φ) (hφe : ∀ (u : U) (x : X), φ (u • x) = u • φ x)
    (ψ : Y → Z) (hψ : Continuous ψ) (hψe : ∀ (u : U) (y : Y), ψ (u • y) = u • ψ y) :
    homMap (k := k) (M := M) (ψ ∘ φ) (hψ.comp hφ) (fun u x => by simp [hφe, hψe]) =
      homMap ψ hψ hψe ≫ homMap φ hφ hφe := by
  ext n Θ
  rfl

end Homogeneous

end ZInQ.Manuscript.RC.SelmerComplex
