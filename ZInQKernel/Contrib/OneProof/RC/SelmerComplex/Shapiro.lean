import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Prism
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.HomogeneousIso
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Induced
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Transversal

/-!
# Lane RC26 (round 3): Shapiro's lemma on cochains, and `cor ∘ res = [G : U]`

Nekovář, *Selmer complexes* (Astérisque 310, 2006), 8.1.1 (Shapiro's lemma), 8.1.4 (the cochain
formula for corestriction); Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, I §5
(Shapiro's lemma, `cor ∘ res = [G : U]`); manuscript `diophantine_zq.tex`, tex 3205–3245 and
7039–7048 (Shapiro followed by equivariant coefficient maps, the transfer).

For a topological group `G`, a subgroup `U` of finite index which is open, a right transversal
`R` of `U\G` (`x ↦ x̂`, with the retraction `ρ(x) = x x̂⁻¹ : G → U`, `R.uPart`) and a discrete
`U`-module `M`:

* `shapiro : C^•(G, Ind_U^G M) → C^•(U, M)`, `c ↦ (u ↦ c(u)(1))` (restriction to `U` followed by
  evaluation at `1`; `shapiro_apply`), and `shapiroInv : C^•(U, M) → C^•(G, Ind_U^G M)`, built
  from the homogeneous description `indIso` and the pullbacks along `ι : U → G` and `ρ`;
* `shapiroInv_shapiro`: `shapiroInv ≫ shapiro = 𝟙` (for a normalized transversal, `1̂ = 1`);
* `shapiroHomotopy`: `shapiro ≫ shapiroInv ≃ 𝟙` (the prism homotopy between `ι ∘ ρ` and `id`);
* `shapiroEquiv`: Shapiro's lemma as a **homotopy equivalence** of complexes, hence
  `shapiro_quasiIso` and isomorphisms on all cohomology groups;
* compatibility with corestriction (for a `G`-module `M`): `corCochains_eq_shapiroInv_comp_norm`
  — **`cor = N_* ∘ shapiroInv`** on the nose, `N : Ind_U^G M → M`, `N f = Σ_{t∈T} t⁻¹ • f(t)` the
  norm map (`normMap`, `G`-equivariant); and restriction: `resCochains_eq` — **`res = shapiro ∘ η_*`**
  with `η : M → Ind_U^G M`, `η(m)(y) = y • m`;
* `corResHomotopy`: **`cor ∘ res ≃ [G : U]`** as cochain maps, with the explicit homotopy
  `N_* ∘ (prism homotopy) ∘ η_*`; `cor_res_cohomology`: `cor ∘ res = [G : U]` on `Hⁿ_cont` in every
  degree.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory

universe u

namespace RightTransversal

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {U : Subgroup G}
  (R : RightTransversal U)

/-- The retraction `ρ : G → U`, `ρ(x) = x x̂⁻¹`, is continuous for open `U` (the representative
map is locally constant). -/
theorem continuous_uPart (hU : IsOpen (U : Set G)) : Continuous R.uPart :=
  continuous_induced_rng.2 (continuous_id.mul (R.continuous_hat hU).inv)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The retraction `ρ : G → U` is `U`-equivariant for the left multiplication actions. -/
theorem uPart_smul (u : U) (x : G) : R.uPart (u • x) = u • R.uPart x :=
  R.uPart_mul u x

/-- The composite `ι ∘ ρ : G → G`, `x ↦ x x̂⁻¹`. -/
def iotaRho (x : G) : G := (R.uPart x : G)

/-- `ι ∘ ρ` is continuous for open `U`. -/
theorem continuous_iotaRho (hU : IsOpen (U : Set G)) : Continuous R.iotaRho :=
  continuous_subtype_val.comp (R.continuous_uPart hU)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- `ι ∘ ρ` is `U`-equivariant. -/
theorem iotaRho_smul (u : U) (x : G) : R.iotaRho (u • x) = u • R.iotaRho x := by
  change ((R.uPart (u • x) : U) : G) = u • ((R.uPart x : U) : G)
  rw [R.uPart_smul]
  rfl

end RightTransversal

/-! ### Shapiro's lemma -/

section Shapiro

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {U : Subgroup G}
  [U.FiniteIndex] (R : RightTransversal U) (hU : IsOpen (U : Set G))
  (k : Type u) [CommRing k] (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction U M]
  [SMulCommClass U k M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul U M]

omit [TopologicalSpace G] [IsTopologicalGroup G] [U.FiniteIndex] in
/-- The inclusion `ι : U → G` is `U`-equivariant. -/
theorem subtype_smul (u v : U) : ((u • v : U) : G) = u • (v : G) :=
  rfl

/-- **The Shapiro map** `C^•(G, Ind_U^G M) → C^•(U, M)` (Nekovář 8.1.1): restriction to `U`
followed by evaluation at `1` (`shapiro_apply`), as the composite of the homogeneous description
of `C^•(G, Ind_U^G M)` (`indIso`), the pullback along `ι : U → G`, and the inhomogeneous description
of `C^•(U, M)` (`homIso`). -/
def shapiro : contCochains k G (IndMod U k M) ⟶ contCochains k U M :=
  (indIso U k M).hom ≫ homMap (Subtype.val : U → G) continuous_subtype_val subtype_smul ≫
    (homIso k U M).inv

/-- **The inverse Shapiro map** `C^•(U, M) → C^•(G, Ind_U^G M)`: pullback along the retraction
`ρ = R.uPart : G → U` in homogeneous coordinates. -/
def shapiroInv : contCochains k U M ⟶ contCochains k G (IndMod U k M) :=
  (homIso k U M).hom ≫ homMap R.uPart (R.continuous_uPart hU) R.uPart_smul ≫ (indIso U k M).inv

omit [U.FiniteIndex] [ContinuousSMul U M] in
/-- For a normalized transversal, `ρ ∘ ι = id` on homogeneous cochains. -/
theorem homMap_uPart_subtype (h1 : R.hat 1 = 1) :
    homMap R.uPart (R.continuous_uPart hU) R.uPart_smul ≫
      homMap (k := k) (M := M) (Subtype.val : U → G) continuous_subtype_val subtype_smul = 𝟙 _ := by
  ext n Θ
  apply Subtype.ext
  funext x
  change (homEl k U U M Θ).1 (R.uPart ∘ (Subtype.val ∘ x)) = (homEl k U U M Θ).1 x
  rw [show R.uPart ∘ (Subtype.val ∘ x) = x from funext fun i => R.uPart_of_mem h1 (x i)]

/-- **`shapiroInv` is a section of `shapiro`** (for a normalized transversal): PROVED. -/
theorem shapiroInv_shapiro (h1 : R.hat 1 = 1) :
    shapiroInv R hU k M ≫ shapiro k M = 𝟙 _ := by
  simp only [shapiroInv, shapiro, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (homMap R.uPart _ _), homMap_uPart_subtype R hU k M h1, Category.id_comp,
    Iso.hom_inv_id]

omit [U.FiniteIndex] [ContinuousSMul U M] in
/-- `ι^* ≫ ρ^* = (ι ∘ ρ)^*` on homogeneous cochains on `G`. -/
theorem homMap_subtype_uPart :
    homMap (k := k) (M := M) (Subtype.val : U → G) continuous_subtype_val subtype_smul ≫
      homMap R.uPart (R.continuous_uPart hU) R.uPart_smul =
    homMap (R.iotaRho) (R.continuous_iotaRho hU) R.iotaRho_smul := by
  ext n Θ
  apply Subtype.ext
  rfl

/-- **Shapiro's lemma, the homotopy** (Nekovář 8.1.1): `shapiro ≫ shapiroInv ≃ 𝟙`, transported
from the prism homotopy between the `U`-equivariant maps `ι ∘ ρ` and `id` of `G`. -/
def shapiroHomotopy : Homotopy (shapiro k M ≫ shapiroInv R hU k M) (𝟙 _) :=
  (Homotopy.ofEq (by
    simp only [shapiro, shapiroInv, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (homMap (Subtype.val : U → G) _ _), homMap_subtype_uPart R hU k M])).trans
    ((((homPrism (k := k) (M := M) (id : G → G) R.iotaRho continuous_id (fun _ _ => rfl)
      (R.continuous_iotaRho hU) R.iotaRho_smul).compRight (indIso U k M).inv).compLeft
        (indIso U k M).hom).trans
      (Homotopy.ofEq (by
        rw [show homMap (k := k) (M := M) (id : G → G) continuous_id (fun _ _ => rfl) = 𝟙 _ from
          homMap_id k U G M, Category.id_comp, Iso.hom_inv_id])))

/-- **Shapiro's lemma on cochains** (Nekovář, *Selmer complexes*, 8.1.1): for an open subgroup `U`
of finite index with a normalized transversal, `C^•(G, Ind_U^G M) ≃ C^•(U, M)` as a **homotopy
equivalence** of complexes. PROVED. -/
def shapiroEquiv (h1 : R.hat 1 = 1) :
    HomotopyEquiv (contCochains k G (IndMod U k M)) (contCochains k U M) where
  hom := shapiro k M
  inv := shapiroInv R hU k M
  homotopyHomInvId := shapiroHomotopy R hU k M
  homotopyInvHomId := Homotopy.ofEq (shapiroInv_shapiro R hU k M h1)

/-- **The Shapiro map is a quasi-isomorphism**: `Hⁿ_cont(G, Ind_U^G M) ≅ Hⁿ_cont(U, M)` in every
degree. PROVED. -/
theorem shapiro_quasiIso (hU : IsOpen (U : Set G)) : QuasiIso (shapiro (G := G) (U := U) k M) :=
  (shapiroEquiv (RightTransversal.ofFiniteIndex U).normalize hU k M
    (RightTransversal.normalize_hat_one _)).quasiIso_hom

/-- **The Shapiro map is restriction followed by evaluation at `1`**:
`shapiro(c)(u₁, …, uₙ) = c(u₁, …, uₙ)(1)` (Nekovář 8.1.1). -/
theorem shapiro_apply (n : ℕ) (c : (contCochains k G (IndMod U k M)).X n) (u : Fin n → U) :
    asFun k U M ((contSubCx k U M).el (((shapiro k M).f n).hom c) : contCochain k U M n) u =
      asFun k G (IndMod U k M) ((contSubCx k G (IndMod U k M)).el c :
        contCochain k G (IndMod U k M) n) (fun i => (u i : G)) 1 := by
  change asFun k G (IndMod U k M) ((contSubCx k G (IndMod U k M)).el c :
      contCochain k G (IndMod U k M) n)
      (fun i => ((Fin.partialProd u i.castSucc : U) : G)⁻¹ * ((Fin.partialProd u i.succ : U) : G))
      ((Fin.partialProd u 0 : U) : G) = _
  have hq : (fun i => ((Fin.partialProd u i.castSucc : U) : G)⁻¹ *
      ((Fin.partialProd u i.succ : U) : G)) = fun i => (u i : G) := by
    funext i
    rw [Fin.partialProd_succ, Subgroup.coe_mul, ← mul_assoc, inv_mul_cancel, one_mul]
  have h0 : ((Fin.partialProd u 0 : U) : G) = 1 := by
    rw [Fin.partialProd_zero]
    rfl
  rw [hq, h0]

/-- **The inverse Shapiro map, explicitly**: `shapiroInv(c)(g)(y) = ρ(y) • c(ρ(y)⁻¹ρ(y g₁), …)`
with the partial products `y g₁⋯g_i` (Nekovář 8.1.1, 8.1.4). -/
theorem shapiroInv_apply (n : ℕ) (c : (contCochains k U M).X n) (g : Fin n → G) (y : G) :
    asFun k G (IndMod U k M) ((contSubCx k G (IndMod U k M)).el (((shapiroInv R hU k M).f n).hom c) :
      contCochain k G (IndMod U k M) n) g y =
      R.uPart (y * Fin.partialProd g 0) • asFun k U M ((contSubCx k U M).el c : contCochain k U M n)
        (fun i => (R.uPart (y * Fin.partialProd g i.castSucc))⁻¹ *
          R.uPart (y * Fin.partialProd g i.succ)) :=
  rfl

end Shapiro

/-! ### Corestriction, restriction and `cor ∘ res = [G : U]` -/

section Transfer

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {U : Subgroup G}
  [U.FiniteIndex] (R : RightTransversal U) (hU : IsOpen (U : Set G))
  (k : Type u) [CommRing k] (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction G M]
  [SMulCommClass G k M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- **The norm map** `N : Ind_U^G M → M`, `N(f) = Σ_{t∈T} t⁻¹ • f(t)`, for a `G`-module `M`
(with `U` acting through the inclusion); it does not depend on the transversal. -/
def normMap : IndMod U k (ResMod (subgroupIncl U) M) →ₗ[k] M where
  toFun f := ∑ t ∈ R.T, t⁻¹ • (show M from f t)
  map_add' f f' := by
    simp only [IndMod.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    exact smul_add _ _ _
  map_smul' c f := by
    simp only [IndMod.ksmul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    exact smul_comm t⁻¹ c (show M from f t)

omit [IsTopologicalGroup G] [U.FiniteIndex] [ContinuousSMul G M] in
/-- The norm map, explicitly. -/
theorem normMap_apply (f : IndMod U k (ResMod (subgroupIncl U) M)) :
    normMap R k M f = ∑ t ∈ R.T, t⁻¹ • (show M from f t) :=
  rfl

omit [U.FiniteIndex] [ContinuousSMul G M] in
/-- **The norm map is `G`-equivariant**: `N(g • f) = g • N(f)` (reindexing `t ↦ (t g)^`). -/
theorem normMap_smul (g : G) (f : IndMod U k (ResMod (subgroupIncl U) M)) :
    normMap R k M (g • f) = g • normMap R k M f := by
  rw [normMap_apply, normMap_apply, Finset.smul_sum]
  have key : ∀ t : G, t⁻¹ • (show M from (g • f) t) =
      g • ((R.hat (t * g))⁻¹ • (show M from f (R.hat (t * g)))) := by
    intro t
    rw [IndMod.smul_apply]
    conv_lhs => rw [← R.uPart_mul_hat (t * g), IndMod.map_mul_left]
    change t⁻¹ • ((R.uPart (t * g) : G) • (show M from f (R.hat (t * g)))) = _
    rw [smul_smul, smul_smul, RightTransversal.coe_uPart]
    congr 1
    group
  simp only [key]
  exact R.sum_hat_mul (fun t' => g • (t'⁻¹ • (show M from f t'))) g

/-- **The unit map** `η : M → Ind_U^G M`, `η(m)(y) = y • m`, for a `G`-module `M`. -/
def etaMap : M →ₗ[k] IndMod U k (ResMod (subgroupIncl U) M) where
  toFun m := IndMod.mk (fun y => (show ResMod (subgroupIncl U) M from (y • m : M)))
    (continuous_id.smul continuous_const : Continuous fun y : G => (y • m : M)) (fun u y => by
      change ((u : G) * y) • m = (u : G) • (y • m)
      rw [mul_smul])
  map_add' m m' := by
    ext y
    exact smul_add y m m'
  map_smul' c m := by
    ext y
    exact smul_comm y c m

omit [U.FiniteIndex] in
/-- **The unit map is `G`-equivariant**: `η(g • m) = g • η(m)`. -/
theorem etaMap_smul (g : G) (m : M) : etaMap k M (U := U) (g • m) = g • etaMap k M m := by
  ext y
  change y • g • m = (y * g) • m
  rw [mul_smul]

omit [IsTopologicalGroup G] [U.FiniteIndex] in
/-- `N ∘ η = [G : U]`: `N(η(m)) = Σ_{t∈T} t⁻¹ • t • m = |T| • m`. -/
theorem normMap_etaMap (m : M) : normMap R k M (etaMap k M m) = (U.index : k) • m := by
  rw [normMap_apply]
  change ∑ t ∈ R.T, t⁻¹ • t • m = _
  simp only [inv_smul_smul, Finset.sum_const, R.card_T_eq_index]
  rw [Nat.cast_smul_eq_nsmul]

/-- The cochain map `η_* : C^•(G, M) → C^•(G, Ind_U^G M)`. -/
abbrev etaCochains : contCochains k G M ⟶ contCochains k G (IndMod U k (ResMod (subgroupIncl U) M)) :=
  contCochainsMap (ContinuousMonoidHom.id G) (etaMap k M) continuous_of_discreteTopology
    (fun g m => etaMap_smul k M g m)

/-- The cochain map `N_* : C^•(G, Ind_U^G M) → C^•(G, M)`. -/
abbrev normCochains : contCochains k G (IndMod U k (ResMod (subgroupIncl U) M)) ⟶ contCochains k G M :=
  contCochainsMap (ContinuousMonoidHom.id G) (normMap R k M) continuous_of_discreteTopology
    (fun g f => normMap_smul R k M g f)

/-- `η_*` explicitly: `(η_* c)(g)(y) = y • c(g)`. -/
theorem etaCochains_apply (n : ℕ) (c : (contCochains k G M).X n) (g : Fin n → G) (y : G) :
    (show M from asFun k G (IndMod U k (ResMod (subgroupIncl U) M))
      ((contSubCx k G (IndMod U k (ResMod (subgroupIncl U) M))).el
        (((etaCochains (U := U) k M).f n).hom c) :
          contCochain k G (IndMod U k (ResMod (subgroupIncl U) M)) n) g y) =
      y • asFun k G M ((contSubCx k G M).el c : contCochain k G M n) g :=
  rfl

/-- `N_*` explicitly: `(N_* c)(g) = Σ_{t∈T} t⁻¹ • c(g)(t)`. -/
theorem normCochains_apply (n : ℕ)
    (c : (contCochains k G (IndMod U k (ResMod (subgroupIncl U) M))).X n) (g : Fin n → G) :
    asFun k G M ((contSubCx k G M).el (((normCochains R k M).f n).hom c) :
      contCochain k G M n) g =
      ∑ t ∈ R.T, t⁻¹ • (show M from asFun k G (IndMod U k (ResMod (subgroupIncl U) M))
        ((contSubCx k G (IndMod U k (ResMod (subgroupIncl U) M))).el c :
          contCochain k G (IndMod U k (ResMod (subgroupIncl U) M)) n) g t) :=
  rfl

/-- **Corestriction is the norm after the inverse Shapiro map**, on the nose:
`cor = N_* ∘ shapiroInv` for the same transversal (Nekovář 8.1.1, 8.1.4: Shapiro followed by
the equivariant norm). PROVED. -/
theorem corCochains_eq_shapiroInv_comp_norm :
    R.corCochains hU = shapiroInv R hU k (ResMod (subgroupIncl U) M) ≫ normCochains R k M := by
  ext n c
  apply Subtype.ext
  funext g
  change R.corFun (M := M) (asFun k U (ResMod (subgroupIncl U) M)
      ((contSubCx k U (ResMod (subgroupIncl U) M)).el c :
        contCochain k U (ResMod (subgroupIncl U) M) n)) g =
    asFun k G M ((contSubCx k G M).el (((normCochains R k M).f n).hom
      (((shapiroInv R hU k (ResMod (subgroupIncl U) M)).f n).hom c)) : contCochain k G M n) g
  rw [normCochains_apply]
  unfold RightTransversal.corFun
  refine Finset.sum_congr rfl fun t ht => ?_
  congr 1
  have key := shapiroInv_apply R hU k (ResMod (subgroupIncl U) M) n c g t
  rw [Fin.partialProd_zero, mul_one, R.uPart_of_mem_T ht, one_smul] at key
  exact key.symm

/-- **Restriction is the Shapiro map after the unit map**, on the nose:
`res = shapiro ∘ η_*` (Nekovář 8.1.1). PROVED. -/
theorem resCochains_eq_eta_comp_shapiro :
    resCochains (k := k) (M := M) (subgroupIncl U) =
      etaCochains k M ≫ shapiro k (ResMod (subgroupIncl U) M) := by
  ext n c
  apply Subtype.ext
  funext u
  have key := shapiro_apply k (ResMod (subgroupIncl U) M) n
    (((etaCochains (U := U) k M).f n).hom c) u
  refine Eq.trans ?_ key.symm
  have h2 := etaCochains_apply (U := U) k M n c (fun i => (u i : G)) 1
  rw [one_smul] at h2
  exact h2.symm

/-- `η_* ≫ N_* = [G : U]`. -/
theorem etaCochains_comp_normCochains :
    etaCochains (U := U) k M ≫ normCochains R k M = (U.index : k) • 𝟙 _ := by
  ext n c
  apply Subtype.ext
  funext g
  exact normMap_etaMap R k M _

/-- **`cor ∘ res ≃ [G : U]` at cochain level** (Neukirch–Schmidt–Wingberg I §5; Nekovář 8.1): the
explicit homotopy is `N_* ∘ (Shapiro homotopy) ∘ η_*`, the Shapiro homotopy being the prism
homotopy between `ι ∘ ρ` and `id` on homogeneous cochains. PROVED. -/
def corResHomotopy :
    Homotopy (resCochains (k := k) (M := M) (subgroupIncl U) ≫ R.corCochains hU)
      ((U.index : k) • 𝟙 _) :=
  (Homotopy.ofEq (by
    rw [resCochains_eq_eta_comp_shapiro, corCochains_eq_shapiroInv_comp_norm R hU k M]
    simp only [Category.assoc])).trans
    ((((shapiroHomotopy R hU k (ResMod (subgroupIncl U) M)).compRight
      (normCochains R k M)).compLeft (etaCochains k M)).trans
      (Homotopy.ofEq (by
        rw [Category.id_comp]
        exact etaCochains_comp_normCochains R k M)))

omit [IsTopologicalGroup G] [U.FiniteIndex] [ContinuousSMul G M] in
/-- **The norm map does not depend on the transversal**: for `t' = t̂'` in another transversal,
`t'⁻¹ • f(t') = t⁻¹ • f(t)` since `f(u t) = u • f(t)`. -/
theorem normMap_indep (R' : RightTransversal U) : normMap R k M = normMap R' k M := by
  ext f
  rw [normMap_apply, normMap_apply]
  refine Finset.sum_nbij' (fun t => R'.hat t) (fun t => R.hat t) (fun t _ => R'.hat_mem t)
    (fun t _ => R.hat_mem t) ?_ ?_ ?_
  · intro t ht
    rw [← R.hat_self t ht]
    exact R.hat_eq t _ (by
      have h := R'.hat_mul_inv_mem t
      rw [R.hat_self t ht]
      exact h)
  · intro t ht
    rw [← R'.hat_self t ht]
    exact R'.hat_eq t _ (by
      have h := R.hat_mul_inv_mem t
      rw [R'.hat_self t ht]
      exact h)
  · intro t _
    have hu : R'.hat t * t⁻¹ ∈ U := R'.hat_mul_inv_mem t
    have e : R'.hat t = ((⟨R'.hat t * t⁻¹, hu⟩ : U) : G) * t := by simp
    change t⁻¹ • (show M from f t) = (R'.hat t)⁻¹ • (show M from f (R'.hat t))
    conv_rhs => rw [e, IndMod.map_mul_left]
    change _ = (((⟨R'.hat t * t⁻¹, hu⟩ : U) : G) * t)⁻¹ •
      ((⟨R'.hat t * t⁻¹, hu⟩ : U) : G) • (show M from f t)
    rw [smul_smul, mul_inv_rev, inv_mul_cancel_right]

/-- `N_*` does not depend on the transversal. -/
theorem normCochains_indep (R' : RightTransversal U) :
    normCochains R' k M = normCochains R k M := by
  ext n c
  apply Subtype.ext
  funext g
  exact LinearMap.congr_fun (normMap_indep R' k M R) _

/-- **Corestriction does not depend on the transversal, up to an explicit homotopy**: for two
transversals `R, R'` of an open subgroup `U`, `cor_{R'} ≃ cor_R` by the prism homotopy between the
retractions `ρ_{R'}, ρ_R : G → U`, transported through `homIso`, `indIso` and the norm map. -/
def corIndepHomotopy (R' : RightTransversal U) :
    Homotopy (R'.corCochains (k := k) (M := M) hU) (R.corCochains hU) :=
  (Homotopy.ofEq (by
    rw [corCochains_eq_shapiroInv_comp_norm R' hU k M, normCochains_indep R k M R']
    simp only [shapiroInv, Category.assoc])).trans
    ((((homPrism (k := k) (M := ResMod (subgroupIncl U) M) R.uPart R'.uPart
        (R.continuous_uPart hU) R.uPart_smul (R'.continuous_uPart hU) R'.uPart_smul).compRight
        ((indIso U k (ResMod (subgroupIncl U) M)).inv ≫ normCochains R k M)).compLeft
        (homIso k U (ResMod (subgroupIncl U) M)).hom).trans
      (Homotopy.ofEq (by
        rw [corCochains_eq_shapiroInv_comp_norm R hU k M]
        simp only [shapiroInv, Category.assoc])))

end Transfer

/-! ### Non-vacuity -/

section NonVacuity

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (k : Type u) [CommRing k]

omit [IsTopologicalGroup G] in
/-- The whole group is open. -/
theorem isOpen_top : IsOpen ((⊤ : Subgroup G) : Set G) := by
  rw [Subgroup.coe_top]
  exact isOpen_univ

/-- **Non-vacuity of Shapiro's lemma**: for `U = G` (with the normalized transversal) and any
discrete `G`-module, `C^•(G, Ind_G^G M) ≃ C^•(G, M)` as a homotopy equivalence. -/
example (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction (⊤ : Subgroup G) M]
    [SMulCommClass (⊤ : Subgroup G) k M] [TopologicalSpace M] [DiscreteTopology M]
    [ContinuousSMul (⊤ : Subgroup G) M] :
    HomotopyEquiv (contCochains k G (IndMod (⊤ : Subgroup G) k M))
      (contCochains k (⊤ : Subgroup G) M) :=
  shapiroEquiv (RightTransversal.ofFiniteIndex ⊤).normalize isOpen_top k M
    (RightTransversal.normalize_hat_one _)

/-- **Non-vacuity of `cor ∘ res ≃ [G : U]`**: the homotopy exists for `U = G` (index one). -/
example (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] :
    Homotopy (resCochains (k := k) (M := M) (subgroupIncl (⊤ : Subgroup G)) ≫
      (RightTransversal.ofFiniteIndex (⊤ : Subgroup G)).corCochains isOpen_top)
      (((⊤ : Subgroup G).index : k) • 𝟙 _) :=
  corResHomotopy (RightTransversal.ofFiniteIndex ⊤) isOpen_top k M

end NonVacuity

/-! ### On cohomology -/

section Cohomology

variable {k : Type u} [CommRing k]

/-- A scalar multiple of the identity induces the same scalar multiple on homology. -/
theorem homologyMap_smul_id (K : CochainComplex (ModuleCat.{u} k) ℕ) (c : k) (n : ℕ) :
    HomologicalComplex.homologyMap (c • 𝟙 K) n = c • 𝟙 _ := by
  have h : (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) n).map
      (c • 𝟙 K) = c • 𝟙 _ := by
    ext <;> rfl
  change ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) n).map
      (c • 𝟙 K)) = _
  rw [h, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {U : Subgroup G}
  [U.FiniteIndex] (R : RightTransversal U) (hU : IsOpen (U : Set G))
  (M : Type u) [AddCommGroup M] [Module k M] [DistribMulAction G M]
  [SMulCommClass G k M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

/-- **`cor ∘ res = [G : U]` on `Hⁿ_cont(G, M)` in every degree** (Neukirch–Schmidt–Wingberg
I §5, Prop. 1.5.7). PROVED. -/
theorem cor_res_cohomology (n : ℕ) (x : contCohomology k G M n) :
    (R.corCohomology (k := k) (M := M) hU n).hom
      ((HomologicalComplex.homologyMap (resCochains (k := k) (M := M) (subgroupIncl U)) n).hom x) =
      (U.index : k) • x := by
  have h := (corResHomotopy R hU k M).homologyMap_eq n
  rw [HomologicalComplex.homologyMap_comp, homologyMap_smul_id] at h
  have := congrArg (fun f => ModuleCat.Hom.hom f x) h
  simpa using this

end Cohomology

end ZInQ.Manuscript.RC.SelmerComplex
