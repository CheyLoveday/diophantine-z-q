import Mathlib

/-!
# RC53 MinimalComplexes: homotopy equivalences of minimal complexes are degreewise invertible

Proof of Lemma `ex:limits-fixed-field-budget`, tex L5404–5411:

> Cancel unit disks in `C_0`. [...] Decompose `D` over `Λ` into a minimal complex `D_min` and unit
> disks `E`. The actual comparison gives a homotopy equivalence `C'_0 ≃ D_min`. A homotopy
> equivalence between minimal bounded free complexes over a local ring is degreewise invertible,
> by reduction modulo its maximal ideal and Nakayama.

The same textbook fact is the "minimal-complex reduction" cited as GLUE in the central lane's
base-zero file (`RC/Central/BaseZero.lean`, module docstring, form note at its lines 18–24).

A cochain complex `K` over a local ring `R` with maximal ideal `𝔪` is *minimal* if its differential
has image in `𝔪 K`: `d(K^i) ⊆ 𝔪 · K^j` for all `i, j` (equivalently `K ⊗ R/𝔪` has zero
differential).

Nodes (PROVED):
* `IdAddRadicalBijective` (Nakayama): on a finitely generated module over a local ring, `1 + N` is
  bijective whenever `N` has image in `𝔪 M`.
* `MinimalHomotopyEquivDegreewise` (tex L5409–5411): a homotopy equivalence between minimal
  bounded complexes of finite free modules over a local ring is bijective in every degree (so it
  is an isomorphism of graded modules). The proof uses only finite generation in each degree;
  boundedness and freeness are the text's hypotheses and are kept in the statement.
-/

namespace ZInQ.Contrib.CloudB3RC53.MinimalComplexes

open CategoryTheory

universe u

/-- Linear maps preserve `I • ⊤`. -/
theorem map_mem_smul_top {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (I : Ideal R) (f : M →ₗ[R] N) {x : M}
    (hx : x ∈ I • (⊤ : Submodule R M)) : f x ∈ I • (⊤ : Submodule R N) := by
  have h : (I • (⊤ : Submodule R M)).map f ≤ I • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact h ⟨x, hx, rfl⟩

/-- **Nakayama: `1 + N` is bijective when `N` has image in `𝔪 M`** (the "reduction modulo its
maximal ideal and Nakayama" of tex L5410–5411). For a local ring `R` and a finitely generated
`R`-module `M`, every endomorphism `N` with `N(M) ⊆ 𝔪 M` makes `1 + N` bijective.
Classification: PROVED. -/
def IdAddRadicalBijective : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (N : M →ₗ[R] M),
    (∀ x, N x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) →
      Function.Bijective (LinearMap.id + N : M →ₗ[R] M)

theorem idAddRadicalBijective_proof : IdAddRadicalBijective.{u} := by
  intro R _ _ M _ _ _ N hN
  have hsurj : Function.Surjective (LinearMap.id + N : M →ₗ[R] M) := by
    rw [← LinearMap.range_eq_top]
    apply top_le_iff.mp
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal R)
      (Module.finite_def.mp inferInstance) (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_
    intro x _
    have hx : x = (LinearMap.id + N : M →ₗ[R] M) x - N x := by simp
    rw [hx]
    exact Submodule.sub_mem_sup (LinearMap.mem_range_self _ x) (hN x)
  exact OrzechProperty.bijective_of_surjective_endomorphism _ hsurj

/-- In a homotopy `φ ≃ 𝟙` of a minimal complex, `φ` is the identity plus a map into `𝔪 K`. -/
theorem homotopy_id_add_radical {R : Type u} [CommRing R] [IsLocalRing R]
    {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : ∀ i j x, (K.d i j).hom x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (K.X j)))
    {φ : K ⟶ K} (h : Homotopy φ (𝟙 K)) (i : ℤ) :
    ∃ N : K.X i →ₗ[R] K.X i, (∀ x, N x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (K.X i))) ∧
      (φ.f i).hom = LinearMap.id + N := by
  refine ⟨(dNext i h.hom + prevD i h.hom).hom, fun x => ?_, ?_⟩
  · rw [ModuleCat.hom_add, LinearMap.add_apply]
    refine Submodule.add_mem _ ?_ ?_
    · rw [dNext_eq_dFrom_fromNext, ModuleCat.hom_comp, LinearMap.comp_apply]
      exact map_mem_smul_top _ _ (hK _ _ x)
    · rw [prevD_eq_toPrev_dTo, ModuleCat.hom_comp, LinearMap.comp_apply]
      exact hK _ _ _
  · rw [h.comm i]
    simp only [HomologicalComplex.id_f, ModuleCat.hom_add, ModuleCat.hom_id]
    abel

/-- **A homotopy equivalence between minimal bounded free complexes over a local ring is
degreewise invertible** (Lemma `ex:limits-fixed-field-budget`, tex L5409–5411; the
"minimal-complex reduction" of the central lane's base-zero lemma). Let `R` be a local ring and
`K, L` cochain complexes of `R`-modules that are bounded (`K.IsStrictlyGE a`, `K.IsStrictlyLE b`,
same for `L`), finite free in each degree, and minimal (`d(K^i) ⊆ 𝔪 K^j`, `d(L^i) ⊆ 𝔪 L^j`). Then
for every homotopy equivalence `e : K ≃ L`, each component `e.hom.f i` is bijective, i.e. a linear
isomorphism `K^i ≃ L^i`. Classification: PROVED. -/
def MinimalHomotopyEquivDegreewise : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (K L : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] [L.IsStrictlyGE a] [L.IsStrictlyLE b]
    [∀ i, Module.Free R (K.X i)] [∀ i, Module.Finite R (K.X i)]
    [∀ i, Module.Free R (L.X i)] [∀ i, Module.Finite R (L.X i)],
    (∀ i j x, (K.d i j).hom x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (K.X j))) →
    (∀ i j x, (L.d i j).hom x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (L.X j))) →
    ∀ (e : HomotopyEquiv K L) (i : ℤ), Function.Bijective (e.hom.f i).hom

theorem minimalHomotopyEquivDegreewise_proof : MinimalHomotopyEquivDegreewise.{u} := by
  intro R _ _ K L a b _ _ _ _ _ _ _ _ hK hL e i
  obtain ⟨N₁, hN₁, h₁⟩ := homotopy_id_add_radical hK e.homotopyHomInvId i
  obtain ⟨N₂, hN₂, h₂⟩ := homotopy_id_add_radical hL e.homotopyInvHomId i
  have b₁ := idAddRadicalBijective_proof R (K.X i) N₁ hN₁
  have b₂ := idAddRadicalBijective_proof R (L.X i) N₂ hN₂
  rw [← h₁, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.coe_comp] at b₁
  rw [← h₂, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.coe_comp] at b₂
  exact ⟨b₁.injective.of_comp, b₂.surjective.of_comp⟩

/-- The degreewise isomorphisms as linear equivalences (tex L5409–5414: "lift the resulting
graded isomorphism"). PROVED. -/
theorem minimalHomotopyEquiv_linearEquiv {R : Type u} [CommRing R] [IsLocalRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] [L.IsStrictlyGE a] [L.IsStrictlyLE b]
    [∀ i, Module.Free R (K.X i)] [∀ i, Module.Finite R (K.X i)]
    [∀ i, Module.Free R (L.X i)] [∀ i, Module.Finite R (L.X i)]
    (hK : ∀ i j x, (K.d i j).hom x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (K.X j)))
    (hL : ∀ i j x, (L.d i j).hom x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (L.X j)))
    (e : HomotopyEquiv K L) (i : ℤ) :
    ∃ φ : K.X i ≃ₗ[R] L.X i, ⇑φ = ⇑(e.hom.f i).hom :=
  ⟨LinearEquiv.ofBijective _ (minimalHomotopyEquivDegreewise_proof R K L a b hK hL e i), rfl⟩

/-- Non-vacuity: complexes with zero differential are minimal, so the hypotheses hold for the
identity homotopy equivalence of any bounded finite free complex with zero differential. PROVED. -/
theorem zero_differential_minimal {R : Type u} [CommRing R] [IsLocalRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (h0 : ∀ i j, K.d i j = 0) :
    ∀ i j x, (K.d i j).hom x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (K.X j)) := by
  intro i j x
  rw [h0]
  exact Submodule.zero_mem _

end ZInQ.Contrib.CloudB3RC53.MinimalComplexes
