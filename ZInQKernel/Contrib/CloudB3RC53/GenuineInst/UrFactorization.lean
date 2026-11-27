import ZInQKernel.Contrib.CloudB3RC53.TameModel.UnramifiedQIso
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Dual

/-!
# Genuine instantiations, part 11: the unramified condition is a quasi-isomorphism followed by
inflation

Manuscript `diophantine_zq.tex`, tex 3478–3487 (the unramified complex `[Φ − 1]` as the local
condition at the new places) and tex 4699–4701.

For `H ≃ₜ* ℤ̂`, a continuous `π : G → H`, a finite discrete representation `X` of `H` on `W` and a
compatible `f : W → M` (`f (π g • x) = g • f x`), the other team's unramified condition
`urToLocal e π X f hf : [W --(Φ−1)--> W] ⟶ C^•_cont(G, M)` **factors** as

`[W --(Φ−1)--> W] --urSelf--> C^•_cont(H, W) --infl--> C^•_cont(G, M)`

(`urToLocal_eq_urSelf_comp`), where `urSelf` is the clearing lane's quasi-isomorphism
(`urSelf_quasiIso`) and `infl` is the cochain map of the compatible pair `(π, f)`
(`contCochainsMap π f`, inflation for `π` a quotient map). At a place `w ∈ S` of a number field
(node `UrToLocalFactorization`): `urToLocal_galois` is the quasi-isomorphism
`[W --(Φ_w−1)--> W] ≃_{qis} C^•_cont(Gal(K_w^ur/K_w), W)` followed by inflation along
`resUr : G_{K_w} → Gal(K_w^ur/K_w)` composed with `f`. This is the precise sense in which the
unramified condition is "the unramified part" of the local complex.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenuineInst

open CategoryTheory TauCeti.ContCohomology ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.TameModel
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

section Generic

variable {k : Type} [CommRing k] [TopologicalSpace k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (X : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (f : X.V →ₗ[k] M) (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x)

/-- **Inflation** `C^•_cont(H, W) → C^•_cont(G, M)`, `c ↦ f ∘ c ∘ πⁿ`, on the `ℤ`-indexed
complexes: the cochain map of the compatible pair `(π, f)`. -/
def inflCC : locCC (k := k) (G := H) (M := X.V) ⟶ locCC (k := k) (G := G) (M := M) :=
  GHom.toCC (natHom (contCochainsMap π f continuous_of_discreteTopology hf))

/-- **The unramified condition is the quasi-isomorphism `urSelf` followed by inflation.**
PROVED. -/
theorem urToLocal_eq_urSelf_comp :
    urToLocal e π X f hf = urSelf e X ≫ inflCC π X f hf := by
  ext n x
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  by_cases h0 : n = 0
  · subst h0
    have h1 := congrArg (fun φ => φ.hom x) (urToLocal_f₀ e π X f hf)
    refine h1.trans ?_
    rw [urSelf_f₀]
    rfl
  by_cases h1 : n = 1
  · subst h1
    have h2 := congrArg (fun φ => φ.hom x) (urToLocal_f₁ e π X f hf)
    refine h2.trans ?_
    rw [urSelf_f₁]
    rfl
  · rw [frobCx_eq_zero e X n h0 h1 x, map_zero, map_zero, map_zero]

/-- Both maps of the factorization: `urSelf` is a quasi-isomorphism (the clearing lane's
`urSelf_quasiIso`). -/
theorem quasiIso_urSelf [CompactSpace H] [TotallyDisconnectedSpace H] [LocallyCompactSpace H] :
    QuasiIso (urSelf e X) :=
  urSelf_quasiIso e X

end Generic

section Galois

open NumberField IsDedekindDomain ZInQ.Contrib.CloudB3RC53.RankCounts

/-- **`urToLocal_galois` factors through the quasi-isomorphism `urSelf` onto
`C^•_cont(Gal(K_w^ur/K_w), W)`, followed by inflation along `resUr` and `f`** (tex 3478–3487,
4699–4701). Kind: PROVED. -/
def UrToLocalFactorization : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (w : Places K S)
    (k : Type) [CommRing k] [TopologicalSpace k] (M : Type) [AddCommGroup M] [Module k M]
    [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
    (X : TopRep.{0} k (GUr K w.1)) [ContinuousSMul (GUr K w.1) X.V] [DiscreteTopology X.V]
    [Finite X.V] (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x),
    QuasiIso (urSelf (eUr K w.1) X) ∧
      urToLocal_galois K S w X f hf =
        urSelf (eUr K w.1) X ≫
          @inflCC k _ _ (Gloc K w.1) _ _ _ (GUr K w.1) _ _ _ (resUr K w.1) X _ _
            (ResMod (locMap K S w.1) M) _ _ _ (instSMulCommClassResMod (locMap K S w.1) M) _ _ _
            f hf

theorem urToLocalFactorization_proof : UrToLocalFactorization := by
  intro K _ _ S w k _ _ M _ _ _ _ _ _ _ X _ _ _ f hf
  exact ⟨urSelf_galois_quasiIso K w X,
    @urToLocal_eq_urSelf_comp k _ _ (Gloc K w.1) _ _ _ (GUr K w.1) _ _ _ (eUr K w.1)
      (resUr K w.1) X _ _ _ (ResMod (locMap K S w.1) M) _ _ _
      (instSMulCommClassResMod (locMap K S w.1) M) _ _ _ f hf⟩

end Galois

end ZInQ.Contrib.CloudB3RC53.GenuineInst
