import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Homogeneous
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Cochains

/-!
# Lane RC26 (round 3): homogeneous and inhomogeneous continuous cochains

For a topological group `G` acting on itself by left multiplication and a topological `G`-module
`M` (continuous addition, continuous scalar multiplications, jointly continuous action
`G × M → M`), the complex `C^•_cont(G, M)` of continuous inhomogeneous cochains (`contCochains`)
is isomorphic to the complex `C^•_hom(G; G, M)` of continuous `G`-equivariant maps
`G^{•+1} → M` (`homCx k G G M`). The dictionary is
```text
Θ(x₀, …, xₙ) = x₀ • c(x₀⁻¹x₁, x₁⁻¹x₂, …, x_{n−1}⁻¹xₙ),
c(g₁, …, gₙ) = Θ(1, g₁, g₁g₂, …, g₁⋯gₙ)
```
(Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed., I §2). It is the continuous
analogue of Mathlib's algebraic dictionary (`Rep.diagonalHomEquiv`,
`groupCohomology.inhomogeneousCochainsIso`).

Main declarations:

* `homToInhom`, `inhomToHom`: the two directions, degreewise `k`-linear maps (continuity uses that
  `G` is a topological group; `inhomToHom` lands in equivariant cochains);
* `homInhomEquiv`: they are mutually inverse (`Fin.partialProd_left_inv`,
  `Fin.partialProd_right_inv`);
* `homToInhom_comm`: compatibility with the differentials (`Fin.partialProd_contractNth`);
* `homIso : contCochains k G M ≅ homCx k G G M`, with the formula lemmas `homIso_hom_apply`
  (`Θ(x) = x 0 • c (fun i => (x i.castSucc)⁻¹ * x i.succ)`) and `homIso_inv_apply`
  (`c(g) = Θ (Fin.partialProd g)`), and `contCohomologyIsoHom` on cohomology;
* naturality in compatible pairs `(φ, f)`: the cochain map `homCompatMap` (`Θ ↦ f ∘ Θ ∘ φ^{n+1}`,
  with `homCompatMap_id`, `homCompatMap_comp`) and the squares `homIso_hom_naturality`,
  `homIso_inv_naturality`; for restriction along `φ : H →ₜ* G` (e.g. the inclusion of a subgroup
  with the subspace topology), `homResMap : C^•_hom(G; G, M) → C^•_hom(H; H, ResMod φ M)` and the
  squares `homIso_hom_res`, `homIso_inv_res`; on cohomology `contCohomologyIsoHom_naturality`;
* change of group on a fixed space (`homChangeMap`, and `homResChangeMap` for `ResMod φ M`), and
  the factorizations `homCompatMap_eq_comp`, `homResMap_eq_comp` of `homCompatMap` and `homResMap`
  through `C^•_hom(H; G, ·)` (for a subgroup `V ≤ G`: through `V`-equivariant cochains on
  `G^{•+1}`, the complex used for Shapiro's lemma) followed by the pullback `homMap` along
  `φ : H → G`.

Kinds: all declarations are genuine definitions or PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory AlgebraicTopology

universe u

section PartialProd

/-- The partial products `(g₁, …, gₙ) ↦ (1, g₁, g₁g₂, …, g₁⋯gₙ)` form a continuous map
`Gⁿ → Gⁿ⁺¹` for a topological monoid `G`. -/
theorem continuous_partialProd_pi {G : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G]
    (n : ℕ) : Continuous (fun g : Fin n → G => Fin.partialProd g) := by
  refine continuous_pi fun i => ?_
  induction i using Fin.induction with
  | zero => simpa only [Fin.partialProd_zero] using continuous_const
  | succ i ih =>
    simp only [Fin.partialProd_succ]
    exact ih.mul (continuous_apply i)

/-- The successive quotients `(x₀, …, xₙ) ↦ (x₀⁻¹x₁, …, x_{n−1}⁻¹xₙ)` form a continuous map
`Gⁿ⁺¹ → Gⁿ` for a topological group `G`. -/
theorem continuous_succQuot {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) :
    Continuous (fun x : Fin (n + 1) → G => fun i : Fin n => (x i.castSucc)⁻¹ * x i.succ) :=
  continuous_pi fun i => ((continuous_apply i.castSucc).inv).mul (continuous_apply i.succ)

end PartialProd

/-! ### The dictionary -/

section Dictionary

variable (k : Type u) [CommRing k] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]
  (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

/-- Read a function `Gⁿ → M` as an inhomogeneous `n`-cochain of `rep k G M`. -/
abbrev inhomOfFun {n : ℕ} (f : (Fin n → G) → M) :
    (groupCohomology.inhomogeneousCochains (rep k G M)).X n :=
  f

/-- **From homogeneous to inhomogeneous cochains**, degreewise:
`c(g₁, …, gₙ) = Θ(1, g₁, g₁g₂, …, g₁⋯gₙ)`, i.e. `c = Θ ∘ Fin.partialProd`
(Neukirch–Schmidt–Wingberg I §2). -/
def homToInhom (n : ℕ) : homCochain k G G M n →ₗ[k] contCochain k G M n where
  toFun Θ := ⟨inhomOfFun k G M (fun g => Θ.1 (Fin.partialProd g)),
    Θ.2.1.comp (continuous_partialProd_pi n)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **From inhomogeneous to homogeneous cochains**, degreewise:
`Θ(x₀, …, xₙ) = x₀ • c(x₀⁻¹x₁, …, x_{n−1}⁻¹xₙ)` (Neukirch–Schmidt–Wingberg I §2). The cochain `Θ`
is continuous (`G` a topological group acting continuously on `M`) and `G`-equivariant. -/
def inhomToHom (n : ℕ) : contCochain k G M n →ₗ[k] homCochain k G G M n where
  toFun c := ⟨fun x => x 0 • asFun k G M c.1 (fun i => (x i.castSucc)⁻¹ * x i.succ),
    (continuous_apply 0).smul ((mem_contCochain.1 c.2).comp (continuous_succQuot n)),
    fun u x => by
      have h : (fun i : Fin n => ((u • x) i.castSucc)⁻¹ * (u • x) i.succ) =
          fun i => (x i.castSucc)⁻¹ * x i.succ := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      change (u • x) 0 • asFun k G M c.1 (fun i => ((u • x) i.castSucc)⁻¹ * (u • x) i.succ) =
        u • (x 0 • asFun k G M c.1 (fun i => (x i.castSucc)⁻¹ * x i.succ))
      rw [h, Pi.smul_apply, smul_eq_mul, mul_smul]⟩
  map_add' c c' := by
    apply Subtype.ext
    funext x
    exact smul_add (x 0) (asFun k G M c.1 _) (asFun k G M c'.1 _)
  map_smul' r c := by
    apply Subtype.ext
    funext x
    exact smul_comm (x 0) r (asFun k G M c.1 _)

omit [ContinuousSMul G M] in
/-- The inhomogeneous cochain attached to a homogeneous one, explicitly:
`c(g) = Θ(1, g₁, g₁g₂, …, g₁⋯gₙ)` (Neukirch–Schmidt–Wingberg I §2). -/
theorem homToInhom_apply (n : ℕ) (Θ : homCochain k G G M n) (g : Fin n → G) :
    asFun k G M (homToInhom k G M n Θ).1 g = Θ.1 (Fin.partialProd g) :=
  rfl

/-- The homogeneous cochain attached to an inhomogeneous one, explicitly:
`Θ(x) = x₀ • c(x₀⁻¹x₁, …, x_{n−1}⁻¹xₙ)` (Neukirch–Schmidt–Wingberg I §2). -/
theorem inhomToHom_apply (n : ℕ) (c : contCochain k G M n) (x : Fin (n + 1) → G) :
    (inhomToHom k G M n c).1 x = x 0 • asFun k G M c.1 (fun i => (x i.castSucc)⁻¹ * x i.succ) :=
  rfl

/-- **The dictionary is a linear isomorphism** in each degree: `homToInhom` and `inhomToHom` are
mutually inverse (Neukirch–Schmidt–Wingberg I §2): `x₀ • (1, x₀⁻¹x₁, …, x₀⁻¹xₙ) = x` and the
successive quotients of the partial products of `g` are the entries of `g`. -/
def homInhomEquiv (n : ℕ) : homCochain k G G M n ≃ₗ[k] contCochain k G M n :=
  { homToInhom k G M n with
    invFun := inhomToHom k G M n
    left_inv := fun Θ => by
      apply Subtype.ext
      funext x
      change x 0 • Θ.1 (Fin.partialProd fun i => (x i.castSucc)⁻¹ * x i.succ) = Θ.1 x
      rw [← Θ.2.2, Fin.partialProd_left_inv]
    right_inv := fun c => by
      apply Subtype.ext
      refine groupCohomology.inhomogeneousCochains.ext fun g => ?_
      change Fin.partialProd g 0 • asFun k G M c.1
          (fun i => (Fin.partialProd g i.castSucc)⁻¹ * Fin.partialProd g i.succ) =
        asFun k G M c.1 g
      simp only [Fin.partialProd_zero, one_smul, Fin.partialProd_right_inv] }

/-- The forward map of `homInhomEquiv` is `homToInhom` (homogeneous to inhomogeneous,
Neukirch–Schmidt–Wingberg I §2). -/
theorem homInhomEquiv_toLinearMap (n : ℕ) :
    (homInhomEquiv k G M n).toLinearMap = homToInhom k G M n :=
  rfl

/-- The inverse map of `homInhomEquiv` is `inhomToHom` (inhomogeneous to homogeneous,
Neukirch–Schmidt–Wingberg I §2). -/
theorem homInhomEquiv_symm_toLinearMap (n : ℕ) :
    (homInhomEquiv k G M n).symm.toLinearMap = inhomToHom k G M n :=
  rfl

omit [IsTopologicalGroup G] [ContinuousSMul G M] in
/-- The combinatorial identity behind the compatibility of the dictionary with the differentials:
for a homogeneous cochain `Θ` and `p = (1, g₀, g₀g₁, …)` the partial products of `g`,
`Σ_i (−1)^i Θ(p ∘ δ_i)` is the inhomogeneous differential of `g ↦ Θ(p(g))`: the face `i = 0` gives
`g₀ • Θ(p(g₁, …))` by equivariance, the face `i = j + 1` gives the contraction of `g_j, g_{j+1}`
(Neukirch–Schmidt–Wingberg I §2). -/
theorem homToInhom_d_aux (n : ℕ) (Θ : homCochain k G G M n) (g : Fin (n + 1) → G) :
    ∑ i : Fin (n + 2), (-1 : k) ^ (i : ℕ) • Θ.1 (Fin.partialProd g ∘ Fin.succAbove i) =
      g 0 • Θ.1 (Fin.partialProd fun i => g i.succ) +
        ∑ j : Fin (n + 1), (-1 : k) ^ ((j : ℕ) + 1) •
          Θ.1 (Fin.partialProd (Fin.contractNth j (· * ·) g)) := by
  rw [Fin.sum_univ_succ]
  congr 1
  · have h : Fin.partialProd g ∘ Fin.succAbove 0 =
        g 0 • Fin.partialProd fun i : Fin n => g i.succ := by
      funext j
      simp only [Function.comp_apply, Fin.succAbove_zero, Fin.partialProd_succ', Pi.smul_apply,
        smul_eq_mul]
      rfl
    rw [h, Θ.2.2, Fin.val_zero, pow_zero, one_smul]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.partialProd_contractNth, Fin.val_succ]

/-- **The dictionary commutes with the differentials**: for a homogeneous `n`-cochain `Θ`, the
inhomogeneous cochain attached to `dΘ` is the inhomogeneous differential of the one attached to `Θ`
(Neukirch–Schmidt–Wingberg I §2). -/
@[reassoc]
theorem homToInhom_comm (n : ℕ) :
    ModuleCat.ofHom (homToInhom k G M n) ≫ (contCochains k G M).d n (n + 1) =
      (homCx k G G M).d n (n + 1) ≫ ModuleCat.ofHom (homToInhom k G M (n + 1)) := by
  ext Θ
  apply Subtype.ext
  refine groupCohomology.inhomogeneousCochains.ext fun g => ?_
  have h1 := contCochains_d_apply (k := k) (G := G) (M := M) n
    ((contSubCx k G M).ofSub (homToInhom k G M n (homEl k G G M Θ))) g
  have h2 := homCx_d_apply' k G G M n Θ (Fin.partialProd g)
  rw [homToInhom_d_aux] at h2
  exact h1.trans h2.symm

/-- The isomorphism of complexes `C^•_hom(G; G, M) ≅ C^•_cont(G, M)`, assembled degreewise from
`homInhomEquiv` (Neukirch–Schmidt–Wingberg I §2). -/
def homInhomIso : homCx k G G M ≅ contCochains k G M :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (homInhomEquiv k G M n).toModuleIso)
    (by
      rintro i j (rfl : i + 1 = j)
      exact homToInhom_comm k G M i)

/-- **The homogeneous/inhomogeneous dictionary for continuous cochains**: for a topological group
`G` acting on itself by left multiplication and a topological `G`-module `M`, the complex
`C^•_cont(G, M)` of continuous inhomogeneous cochains is isomorphic to the complex
`C^•_hom(G; G, M)` of continuous `G`-equivariant maps `G^{•+1} → M`, via
`Θ(x₀, …, xₙ) = x₀ • c(x₀⁻¹x₁, …, x_{n−1}⁻¹xₙ)` and `c(g₁, …, gₙ) = Θ(1, g₁, …, g₁⋯gₙ)`
(Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, I §2). -/
def homIso : contCochains k G M ≅ homCx k G G M :=
  (homInhomIso k G M).symm

/-- **Formula for the dictionary, inhomogeneous to homogeneous**:
`Θ(x₀, …, xₙ) = x₀ • c(x₀⁻¹x₁, x₁⁻¹x₂, …, x_{n−1}⁻¹xₙ)` (Neukirch–Schmidt–Wingberg I §2). -/
theorem homIso_hom_apply (n : ℕ) (c : (contCochains k G M).X n) (x : Fin (n + 1) → G) :
    (homEl k G G M (((homIso k G M).hom.f n).hom c)).1 x =
      x 0 • asFun k G M ((contSubCx k G M).el c : contCochain k G M n)
        (fun i => (x i.castSucc)⁻¹ * x i.succ) :=
  rfl

/-- **Formula for the dictionary, homogeneous to inhomogeneous**:
`c(g₁, …, gₙ) = Θ(1, g₁, g₁g₂, …, g₁⋯gₙ)` (Neukirch–Schmidt–Wingberg I §2). -/
theorem homIso_inv_apply (n : ℕ) (Θ : (homCx k G G M).X n) (g : Fin n → G) :
    asFun k G M ((contSubCx k G M).el (((homIso k G M).inv.f n).hom Θ) : contCochain k G M n) g =
      (homEl k G G M Θ).1 (Fin.partialProd g) :=
  rfl

/-- The components of `homIso` are the degreewise maps `inhomToHom` (inhomogeneous to homogeneous,
Neukirch–Schmidt–Wingberg I §2). -/
theorem homIso_hom_f (n : ℕ) :
    (homIso k G M).hom.f n = ModuleCat.ofHom (inhomToHom k G M n) :=
  rfl

/-- The components of the inverse of `homIso` are the degreewise maps `homToInhom` (homogeneous to
inhomogeneous, Neukirch–Schmidt–Wingberg I §2). -/
theorem homIso_inv_f (n : ℕ) :
    (homIso k G M).inv.f n = ModuleCat.ofHom (homToInhom k G M n) :=
  rfl

/-- **Continuous cohomology via homogeneous cochains**: `Hⁿ_cont(G, M)` is the cohomology of the
complex of continuous homogeneous cochains `C^•_hom(G; G, M)` (Neukirch–Schmidt–Wingberg I §2). -/
def contCohomologyIsoHom (n : ℕ) :
    contCohomology k G M n ≅ (homCx k G G M).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) n).mapIso
    (homIso k G M)

end Dictionary

/-! ### Homogeneous cochain maps of compatible pairs -/

section CompatMap

variable {k : Type u} [CommRing k]
  {G : Type u} [Group G] [TopologicalSpace G]
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M]
  {H : Type u} [Group H] [TopologicalSpace H]
  {N : Type u} [AddCommGroup N] [Module k N] [DistribMulAction H N] [SMulCommClass H k N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul k N]

/-- The map of homogeneous cochains attached to a compatible pair `(φ, f)` (a continuous
homomorphism `φ : H → G` and a continuous `k`-linear `f : M → N` with `f (φ h • m) = h • f m`),
degreewise: `Θ ↦ f ∘ Θ ∘ φ^{n+1}` (Neukirch–Schmidt–Wingberg I §5). -/
def homCompatLin (φ : H →ₜ* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (n : ℕ) :
    homCochain k G G M n →ₗ[k] homCochain k H H N n where
  toFun Θ := ⟨fun x => f (Θ.1 (φ ∘ x)),
    hfc.comp (Θ.2.1.comp (continuous_pi fun i => φ.continuous.comp (continuous_apply i))),
    fun h x => by
      change f (Θ.1 (φ ∘ (h • x))) = h • f (Θ.1 (φ ∘ x))
      have e : φ ∘ (h • x) = φ h • (φ ∘ x) := funext fun i => map_mul φ h (x i)
      rw [e, Θ.2.2, hf]⟩
  map_add' Θ Θ' := Subtype.ext (funext fun x => map_add f (Θ.1 (φ ∘ x)) (Θ'.1 (φ ∘ x)))
  map_smul' r Θ := Subtype.ext (funext fun x => map_smul f r (Θ.1 (φ ∘ x)))

/-- The map of homogeneous cochains of a compatible pair, as a morphism of cosimplicial modules
(Neukirch–Schmidt–Wingberg I §5). -/
def homCompatCosimp (φ : H →ₜ* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    homCosimp k G G M ⟶ homCosimp k H H N where
  app n := ModuleCat.ofHom (homCompatLin φ f hfc hf n.len)
  naturality _ _ _ := by
    ext Θ
    rfl

/-- **The cochain map `C^•_hom(G; G, M) → C^•_hom(H; H, N)` of a compatible pair** `(φ, f)`:
`Θ ↦ f ∘ Θ ∘ φ^{n+1}` (Neukirch–Schmidt–Wingberg I §5). For `f` the identity of `M` read in
`ResMod φ M` this is restriction (`homResMap`). -/
def homCompatMap (φ : H →ₜ* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    homCx k G G M ⟶ homCx k H H N :=
  AlternatingCofaceMapComplex.map (homCompatCosimp φ f hfc hf)

/-- The cochain map of a compatible pair on homogeneous cochains, explicitly:
`(f ∘ Θ ∘ φ^{n+1})(x₀, …, xₙ) = f (Θ (φ x₀, …, φ xₙ))` (Neukirch–Schmidt–Wingberg I §5). -/
theorem homCompatMap_f_apply (φ : H →ₜ* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (n : ℕ) (Θ : (homCx k G G M).X n)
    (x : Fin (n + 1) → H) :
    (homEl k H H N (((homCompatMap φ f hfc hf).f n).hom Θ)).1 x =
      f ((homEl k G G M Θ).1 (φ ∘ x)) :=
  rfl

variable (k G M) in
/-- The identity pair induces the identity on homogeneous cochains (Neukirch–Schmidt–Wingberg
I §5). -/
theorem homCompatMap_id :
    homCompatMap (ContinuousMonoidHom.id G) (LinearMap.id : M →ₗ[k] M) continuous_id
      (fun _ _ => rfl) = 𝟙 (homCx k G G M) := by
  ext n Θ
  rfl

/-- Composition of compatible pairs on homogeneous cochains (Neukirch–Schmidt–Wingberg I §5). -/
theorem homCompatMap_comp {L : Type u} [Group L] [TopologicalSpace L]
    {P : Type u} [AddCommGroup P] [Module k P] [DistribMulAction L P] [SMulCommClass L k P]
    [TopologicalSpace P] [ContinuousAdd P] [ContinuousConstSMul k P]
    (φ : H →ₜ* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (ψ : L →ₜ* H) (g : N →ₗ[k] P) (hgc : Continuous g)
    (hg : ∀ (l : L) (n : N), g (ψ l • n) = l • g n) :
    homCompatMap (φ.comp ψ) (g ∘ₗ f) (hgc.comp hfc)
        (fun l m => by
          change g (f (φ (ψ l) • m)) = l • g (f m)
          rw [hf, hg]) =
      homCompatMap φ f hfc hf ≫ homCompatMap ψ g hgc hg := by
  ext n Θ
  rfl

omit [DistribMulAction G M] [SMulCommClass G k M] [ContinuousAdd M] [ContinuousConstSMul k M] in
/-- The identification `M → ResMod φ M` of a module with its restriction along `φ : H →ₜ* G` is
continuous (it is the identity of `M`). Stated with the topology of `ResMod φ M`, so that passing
it as the continuity hypothesis of a compatible pair fixes the intended instances. -/
theorem toResMod_continuous (φ : H →ₜ* G) : Continuous (toResMod (k := k) (M := M) φ) :=
  continuous_id

/-- **Restriction on homogeneous cochains** along a continuous homomorphism `φ : H →ₜ* G` (with `H`
acting on `M` through `φ`): `Θ ↦ Θ ∘ φ^{n+1}`. For a subgroup `V ≤ G` (subspace topology) and `φ`
its inclusion this is the restriction `C^•_hom(G; G, M) → C^•_hom(V; V, M)`
(Neukirch–Schmidt–Wingberg I §5). -/
abbrev homResMap (φ : H →ₜ* G) : homCx k G G M ⟶ homCx k H H (ResMod φ M) :=
  homCompatMap φ (toResMod (k := k) φ) (toResMod_continuous φ) (toResMod_compat φ)

end CompatMap

/-! ### Change of group on a fixed space -/

section Change

variable {k : Type u} [CommRing k] {G : Type u} [Group G] {H : Type u} [Group H]
  {X : Type u} [TopologicalSpace X] [MulAction G X] [MulAction H X]
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M]
  {N : Type u} [AddCommGroup N] [Module k N] [DistribMulAction H N] [SMulCommClass H k N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul k N]

/-- **Change of group** on homogeneous cochains on a fixed space `X`, degreewise: for a
homomorphism `φ : H → G` through which `H` acts on `X` (`hX`) and a continuous `k`-linear
`f : M → N` with `f (φ h • m) = h • f m`, the map `Θ ↦ f ∘ Θ` from `G`-equivariant to
`H`-equivariant cochains (Neukirch–Schmidt–Wingberg I §2, I §5). -/
def homChangeLin (φ : H →* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (hX : ∀ (h : H) (x : X), h • x = φ h • x)
    (n : ℕ) : homCochain k G X M n →ₗ[k] homCochain k H X N n where
  toFun Θ := ⟨fun x => f (Θ.1 x), hfc.comp Θ.2.1, fun h x => by
    change f (Θ.1 (h • x)) = h • f (Θ.1 x)
    have e : h • x = φ h • x := funext fun i => hX h (x i)
    rw [e, Θ.2.2, hf]⟩
  map_add' Θ Θ' := Subtype.ext (funext fun x => map_add f (Θ.1 x) (Θ'.1 x))
  map_smul' r Θ := Subtype.ext (funext fun x => map_smul f r (Θ.1 x))

/-- Change of group, as a morphism of cosimplicial modules (Neukirch–Schmidt–Wingberg I §5). -/
def homChangeCosimp (φ : H →* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (hX : ∀ (h : H) (x : X), h • x = φ h • x) :
    homCosimp k G X M ⟶ homCosimp k H X N where
  app n := ModuleCat.ofHom (homChangeLin φ f hfc hf hX n.len)
  naturality _ _ _ := by
    ext Θ
    rfl

/-- **The change-of-group cochain map** `C^•_hom(G; X, M) → C^•_hom(H; X, N)`, `Θ ↦ f ∘ Θ`
(Neukirch–Schmidt–Wingberg I §2, I §5). -/
def homChangeMap (φ : H →* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (hX : ∀ (h : H) (x : X), h • x = φ h • x) :
    homCx k G X M ⟶ homCx k H X N :=
  AlternatingCofaceMapComplex.map (homChangeCosimp φ f hfc hf hX)

/-- The change-of-group cochain map, explicitly: `Θ ↦ f ∘ Θ` (Neukirch–Schmidt–Wingberg I §5). -/
theorem homChangeMap_f_apply (φ : H →* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (hX : ∀ (h : H) (x : X), h • x = φ h • x)
    (n : ℕ) (Θ : (homCx k G X M).X n) (x : Fin (n + 1) → X) :
    (homEl k H X N (((homChangeMap φ f hfc hf hX).f n).hom Θ)).1 x =
      f ((homEl k G X M Θ).1 x) :=
  rfl

end Change

section Factor

variable {k : Type u} [CommRing k]
  {G : Type u} [Group G] [TopologicalSpace G]
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M]
  {H : Type u} [Group H] [TopologicalSpace H]
  {N : Type u} [AddCommGroup N] [Module k N] [DistribMulAction H N] [SMulCommClass H k N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul k N]

/-- **Factorization of the cochain map of a compatible pair** through `C^•_hom(H; G, N)`: if `H`
acts on `G` by `h • g = φ h * g` (for a subgroup `V ≤ G` and its inclusion: Mathlib's action of `V`
on `G`), then `Θ ↦ f ∘ Θ ∘ φ^{n+1}` is the change of group `Θ ↦ f ∘ Θ` on `G^{•+1}` followed by
the pullback along the `H`-equivariant map `φ : H → G` (Neukirch–Schmidt–Wingberg I §2, I §5). -/
theorem homCompatMap_eq_comp [MulAction H G] (φ : H →ₜ* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (hG : ∀ (h : H) (g : G), h • g = φ h * g) :
    homCompatMap φ f hfc hf =
      homChangeMap (X := G) (φ : H →* G) f hfc hf hG ≫
        homMap (U := H) (φ : H → G) φ.continuous
          (fun h h' => (map_mul φ h h').trans (hG h (φ h')).symm) := by
  ext n Θ
  rfl

variable {X : Type u} [TopologicalSpace X] [MulAction G X] [MulAction H X] in
/-- **Restriction of the equivariance group** along a continuous homomorphism `φ : H →ₜ* G`
through which `H` acts on the space `X` (`hX`), with `H` acting on `M` through `φ`: the cochain
map `C^•_hom(G; X, M) → C^•_hom(H; X, ResMod φ M)`, `Θ ↦ Θ` (Neukirch–Schmidt–Wingberg I §2, I §5).
For a subgroup `V ≤ G` acting on `X = G` by left multiplication this is the map from
`G`-equivariant to `V`-equivariant cochains on `G^{•+1}` used for Shapiro's lemma. -/
abbrev homResChangeMap (φ : H →ₜ* G) (hX : ∀ (h : H) (x : X), h • x = φ h • x) :
    homCx k G X M ⟶ homCx k H X (ResMod φ M) :=
  homChangeMap (φ : H →* G) (toResMod (k := k) φ) (toResMod_continuous φ) (toResMod_compat φ) hX

/-- **Factorization of restriction** through `C^•_hom(H; G, ResMod φ M)`: if `H` acts on `G` by
`h • g = φ h * g` (for a subgroup `V ≤ G` and its inclusion: Mathlib's action of `V` on `G`, with
`hG := fun _ _ => rfl`), restriction `Θ ↦ Θ ∘ φ^{n+1}` is the restriction of the equivariance
group `Θ ↦ Θ` on `G^{•+1}` followed by the pullback along the `H`-equivariant map `φ : H → G`
(Neukirch–Schmidt–Wingberg I §5). -/
theorem homResMap_eq_comp [MulAction H G] (φ : H →ₜ* G)
    (hG : ∀ (h : H) (g : G), h • g = φ h * g) :
    homResMap (k := k) (M := M) φ =
      homResChangeMap (X := G) φ hG ≫
        homMap (U := H) (M := ResMod φ M) (φ : H → G) φ.continuous
          (fun h h' => (map_mul φ h h').trans (hG h (φ h')).symm) :=
  homCompatMap_eq_comp φ _ _ _ hG

end Factor

/-! ### Naturality of the dictionary: restriction and inflation -/

section Naturality

variable {k : Type u} [CommRing k]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]
  {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {N : Type u} [AddCommGroup N] [Module k N] [DistribMulAction H N] [SMulCommClass H k N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul k N] [ContinuousSMul H N]

/-- **Naturality of the dictionary in compatible pairs**: the square formed by `homIso` and the
cochain maps of a compatible pair `(φ, f)` on inhomogeneous (`contCochainsMap`) and homogeneous
(`homCompatMap`) cochains commutes (Neukirch–Schmidt–Wingberg I §2, I §5). -/
@[reassoc]
theorem homIso_hom_naturality (φ : H →ₜ* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    contCochainsMap φ f hfc hf ≫ (homIso k H N).hom =
      (homIso k G M).hom ≫ homCompatMap φ f hfc hf := by
  ext n c
  apply Subtype.ext
  funext x
  change x 0 • f (asFun k G M ((contSubCx k G M).el c : contCochain k G M n)
      (φ ∘ fun i => (x i.castSucc)⁻¹ * x i.succ)) =
    f (φ (x 0) • asFun k G M ((contSubCx k G M).el c : contCochain k G M n)
      (fun i => (φ (x i.castSucc))⁻¹ * φ (x i.succ)))
  rw [hf]
  congr 3
  funext i
  simp only [Function.comp_apply, map_mul, map_inv]

/-- **Naturality of the inverse dictionary in compatible pairs**: `homCompatMap` followed by the
inverse dictionary is the inverse dictionary followed by `contCochainsMap`
(Neukirch–Schmidt–Wingberg I §2, I §5). -/
@[reassoc]
theorem homIso_inv_naturality (φ : H →ₜ* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    homCompatMap φ f hfc hf ≫ (homIso k H N).inv =
      (homIso k G M).inv ≫ contCochainsMap φ f hfc hf := by
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  exact (homIso_hom_naturality φ f hfc hf).symm

/-- **The dictionary commutes with restriction**: `resCochains φ ≫ homIso = homIso ≫ homResMap φ`,
i.e. restricting an inhomogeneous cochain and passing to homogeneous cochains agrees with passing to
homogeneous cochains and restricting (Neukirch–Schmidt–Wingberg I §2, I §5). -/
@[reassoc]
theorem homIso_hom_res (φ : H →ₜ* G) :
    resCochains (k := k) (M := M) φ ≫ (homIso k H (ResMod φ M)).hom =
      (homIso k G M).hom ≫ homResMap φ :=
  homIso_hom_naturality φ _ _ _

/-- **The inverse dictionary commutes with restriction**:
`homResMap φ ≫ homIso⁻¹ = homIso⁻¹ ≫ resCochains φ` (Neukirch–Schmidt–Wingberg I §2, I §5). -/
@[reassoc]
theorem homIso_inv_res (φ : H →ₜ* G) :
    homResMap (k := k) (M := M) φ ≫ (homIso k H (ResMod φ M)).inv =
      (homIso k G M).inv ≫ resCochains φ :=
  homIso_inv_naturality φ _ _ _

/-- **Naturality of `Hⁿ_cont ≅ Hⁿ_hom` in compatible pairs**: the map on continuous cohomology of a
compatible pair corresponds to the map induced by `homCompatMap` on the cohomology of homogeneous
cochains (Neukirch–Schmidt–Wingberg I §2, I §5). -/
theorem contCohomologyIsoHom_naturality (φ : H →ₜ* G) (f : M →ₗ[k] N) (hfc : Continuous f)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (n : ℕ) :
    contCohomologyMap φ f hfc hf n ≫ (contCohomologyIsoHom k H N n).hom =
      (contCohomologyIsoHom k G M n).hom ≫
        HomologicalComplex.homologyMap (homCompatMap φ f hfc hf) n := by
  change HomologicalComplex.homologyMap (contCochainsMap φ f hfc hf) n ≫
      HomologicalComplex.homologyMap (homIso k H N).hom n =
    HomologicalComplex.homologyMap (homIso k G M).hom n ≫
      HomologicalComplex.homologyMap (homCompatMap φ f hfc hf) n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    homIso_hom_naturality]

end Naturality

end ZInQ.Manuscript.RC.SelmerComplex
