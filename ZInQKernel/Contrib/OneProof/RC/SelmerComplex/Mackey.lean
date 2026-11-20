import Mathlib
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Corestriction

/-!
# Lane RC26: the double coset (Mackey) formula at cochain level

Manuscript `diophantine_zq.tex`, (K7), tex 6971–6979: for a finite extension `L/K` with absolute
Galois groups `H ⊂ G_K`, a class `z ∈ H¹(H, M)` and an inertia subgroup `I ⊂ G_K`,
```
res^{G_K}_I cor^{G_K}_H z = ∑_{g ∈ I\G_K/H} cor^I_{I ∩ gHg⁻¹} res^{gHg⁻¹}_{I ∩ gHg⁻¹} (g z).   (K7)
```
(Brown, *Cohomology of Groups*, III.9–10; Neukirch–Schmidt–Wingberg, *Cohomology of Number
Fields*, I §5.)

This file proves the double coset formula **on the nose at the level of continuous inhomogeneous
cochains**, in all degrees, for a topological group `G`, an open subgroup `U` (of finite index,
through a finite right transversal) and an arbitrary subgroup `V` (e.g. an inertia group), for a
*compatible system of transversals* (`MackeyData`).

Main results:

* `conjInter U V s`: the subgroup `V ∩ s U s⁻¹`, as a subgroup of `V`; it is open in `V` when `U`
  is open (`isOpen_conjInter`).
* `conjHom U V s : V ∩ s U s⁻¹ →ₜ* U`, `w ↦ s⁻¹ w s`, and `conjSMul U V s : m ↦ s • m`; together a
  compatible pair (`conjSMul_compat`), whose cochain map is `res^{sUs⁻¹}_{V ∩ sUs⁻¹} ∘ (s ·)`.
* `MackeyData U V ι`: elements `s i`, a right transversal `RU` of `U` in `G` and right
  transversals `Rs i` of `V ∩ s_i U s_i⁻¹` in `V` such that `(i, r) ↦ s_i⁻¹ r` is a bijection
  onto the representatives of `RU`. Consequences: compatibility of the representative maps
  `RU.hat (s_i⁻¹ y) = s_i⁻¹ (Rs i).hat y` for `y ∈ V` (`MackeyData.hat_conj`), and the `s i`
  represent the double cosets `V\G/U` (`MackeyData.exists_eq_mul_s_mul`,
  `MackeyData.eq_of_s_eq_mul`). PROVED.
* `MackeyData.corCochains_comp_resCochains`: **the cochain-level double coset formula**
  `res^G_V ∘ cor^G_U = ∑_i cor^V_{V ∩ s_iUs_i⁻¹} ∘ res^{s_iUs_i⁻¹}_{V ∩ s_iUs_i⁻¹} ∘ (s_i ·)`,
  an equality of cochain maps (no homotopy). PROVED.
* `MackeyData.homologyMap_corCochains_comp_resCochains`: the induced identity on continuous
  cohomology `Hⁿ_cont`; `MackeyData.res_cor_eq_zero_of_forall`: if every summand vanishes on `z`,
  then `res^G_V cor^G_U z = 0` (the use of (K7) in the text). PROVED.
* Non-vacuity: `MackeyData.ofTopLeft` (`U = G`) and `MackeyData.ofTopRight` (`V = G`, one double
  coset, with an arbitrary transversal of `U`); in general, `MackeyData.ofFiniteIndex` and
  `MackeyData.exists_of_finiteIndex`: a compatible system exists for every `U` of finite index and
  every `V`, indexed by the finite double coset space `V\G/U` (`DoubleCosets`, whose relation is
  Mathlib's `DoubleCoset.setoid`, `dcSetoid_eq`). Hence `res_cor_eq_zero_of_forall_conj`: for `U`
  open of finite index, `res^{sUs⁻¹}_{V ∩ sUs⁻¹}(s z) = 0` for all `s ∈ G` implies
  `res^G_V cor^G_U z = 0` (corestriction computed with the transversal `MackeyData.dcRU U V`).
  PROVED.

Hypotheses: `G` is a topological group, `V` carries the subspace topology, and `M` satisfies the
standing hypotheses of `contCochains` (for a discrete `G`-module with continuous action they hold
automatically). The compatibility `RU.hat (s_i⁻¹ y) = s_i⁻¹ (Rs i).hat y` is derived from the
bijection condition, not assumed.

Kinds: all declarations are genuine definitions or PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory

universe u

/-! ### Conjugate intersections and the conjugation pair -/

section Conj

variable {G : Type u} [Group G]

/-- **The conjugate intersection** `V ∩ s U s⁻¹`, as a subgroup of `V`: the preimage in `V` of the
conjugate subgroup `s U s⁻¹`. These are the groups `I ∩ gHg⁻¹` of the double coset formula (K7),
tex 6971–6979 (Brown, *Cohomology of Groups*, III.9–10; Neukirch–Schmidt–Wingberg I §5). -/
def conjInter (U V : Subgroup G) (s : G) : Subgroup V :=
  (U.map (MulAut.conj s).toMonoidHom).comap V.subtype

/-- `w ∈ V ∩ s U s⁻¹` iff `s⁻¹ w s ∈ U`. -/
theorem mem_conjInter {U V : Subgroup G} {s : G} {w : V} :
    w ∈ conjInter U V s ↔ s⁻¹ * (w : G) * s ∈ U := by
  rw [conjInter, Subgroup.mem_comap, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rfl

/-- The trivial right transversal `{1}` of a subgroup containing every element (used for the
degenerate cases of the double coset formula, Brown III.9). -/
def RightTransversal.ofForallMem (H : Subgroup G) (h : ∀ x, x ∈ H) : RightTransversal H where
  T := {1}
  hat := fun _ => 1
  hat_mem := fun _ => Finset.mem_singleton_self 1
  hat_mul_inv_mem := fun _ => h _
  hat_eq := fun _ _ _ => rfl
  hat_self := fun _ ht => (Finset.mem_singleton.mp ht).symm

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The conjugation homomorphism** `V ∩ s U s⁻¹ → U`, `w ↦ s⁻¹ w s`, continuous for the subspace
topologies. Composed with the action `m ↦ s • m` it gives the map
`res^{sUs⁻¹}_{V ∩ sUs⁻¹}(s z)` of (K7), tex 6971–6979 (Brown III.9–10; NSW I §5). -/
def conjHom (U V : Subgroup G) (s : G) : conjInter U V s →ₜ* U where
  toFun w := ⟨s⁻¹ * ((w : V) : G) * s, mem_conjInter.mp w.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)).mul
      continuous_const

/-- The conjugation homomorphism sends `w` to `s⁻¹ w s`. -/
@[simp]
theorem coe_conjHom_apply (U V : Subgroup G) (s : G) (w : conjInter U V s) :
    ((conjHom U V s w : U) : G) = s⁻¹ * ((w : V) : G) * s :=
  rfl

/-- For an open subgroup `U`, the conjugate intersection `V ∩ s U s⁻¹` is open in `V` (it is the
preimage of `U` under the continuous map `w ↦ s⁻¹ w s`), so corestriction from it to `V` is
defined on continuous cochains (Brown III.9; NSW I §5). -/
theorem isOpen_conjInter {U : Subgroup G} (hU : IsOpen (U : Set G)) (V : Subgroup G) (s : G) :
    IsOpen ((conjInter U V s : Subgroup V) : Set V) := by
  have e : ((conjInter U V s : Subgroup V) : Set V) =
      (fun w : V => s⁻¹ * (w : G) * s) ⁻¹' (U : Set G) := by
    ext w
    exact mem_conjInter
  rw [e]
  exact hU.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)

variable {k : Type u} [CommRing k]
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]

/-- **The translation** `m ↦ s • m`, as a `k`-linear map from `M` with `U` acting (through
`U ≤ G`) to `M` with `V ∩ s U s⁻¹` acting (through `V ∩ sUs⁻¹ ≤ V ≤ G`): the map `z ↦ s z` of the
double coset formula (K7), tex 6971–6979 (Brown III.9–10; NSW I §5). -/
def conjSMul (U V : Subgroup G) (s : G) :
    ResMod (subgroupIncl U) M →ₗ[k]
      ResMod (subgroupIncl (conjInter U V s)) (ResMod (subgroupIncl V) M) where
  toFun m := (show M from s • (show M from m))
  map_add' a b := smul_add s (show M from a) (show M from b)
  map_smul' c m := smul_comm s c (show M from m)

omit [IsTopologicalGroup G] in
/-- The translation sends `m` to `s • m`. -/
theorem conjSMul_apply (U V : Subgroup G) (s : G) (m : ResMod (subgroupIncl U) M) :
    conjSMul (k := k) U V s m = (show M from s • (show M from m)) :=
  rfl

/-- **Compatibility** of the pair `(conjHom, conjSMul)`:
`s • ((s⁻¹ w s) • m) = w • (s • m)` (NSW I §5: the conjugation pair). -/
theorem conjSMul_compat (U V : Subgroup G) (s : G) (w : conjInter U V s)
    (m : ResMod (subgroupIncl U) M) :
    conjSMul (k := k) U V s (conjHom U V s w • m) = w • conjSMul (k := k) U V s m := by
  change s • ((s⁻¹ * ((w : V) : G) * s) • (show M from m)) =
    ((w : V) : G) • (s • (show M from m))
  rw [smul_smul, smul_smul]
  congr 1
  group

variable [TopologicalSpace M] [ContinuousSMul G M]

omit [IsTopologicalGroup G] in
/-- The translation `m ↦ s • m` is continuous. -/
theorem continuous_conjSMul (U V : Subgroup G) (s : G) :
    Continuous (conjSMul (k := k) (M := M) U V s) := by
  change Continuous (fun m : M => s • m)
  exact continuous_const_smul s

end Conj

/-! ### Compatible systems of transversals -/

section Data

variable {G : Type u} [Group G]

/-- **A compatible system of transversals for the double coset formula** (K7), tex 6971–6979
(Brown, *Cohomology of Groups*, III.9–10; Neukirch–Schmidt–Wingberg I §5): elements `s i`
(`i ∈ ι`), a finite right transversal `RU` of `U` in `G` and finite right transversals `Rs i` of
`V ∩ s_i U s_i⁻¹` in `V`, such that `(i, r) ↦ s_i⁻¹ r` is a bijection from `∐_i T(Rs i)` onto the
representatives `T(RU)`. Then `G = ∐_i V s_i U` (the `s i` represent `V\G/U`) and the
representative maps are compatible (`MackeyData.hat_conj`). -/
structure MackeyData (U V : Subgroup G) (ι : Type*) [Fintype ι] where
  /-- Representatives `s_i` of the double cosets `V s_i U`. -/
  s : ι → G
  /-- A finite right transversal of `U` in `G`. -/
  RU : RightTransversal U
  /-- Finite right transversals of `V ∩ s_i U s_i⁻¹` in `V`. -/
  Rs : ∀ i, RightTransversal (conjInter U V (s i))
  /-- `(i, r) ↦ s_i⁻¹ r` is a bijection from `∐_i T(Rs i)` onto `T(RU)`. -/
  bij : Set.BijOn (fun p : (Σ _ : ι, V) => (s p.1)⁻¹ * (p.2 : G))
    ((Finset.univ.sigma fun i => (Rs i).T : Finset (Σ _ : ι, V)) : Set (Σ _ : ι, V))
    (RU.T : Set G)

variable {U V : Subgroup G} {ι : Type*} [Fintype ι]

namespace MackeyData

variable (D : MackeyData U V ι)

/-- `s_i⁻¹ r` is a representative of `RU` for `r` a representative of `Rs i`. -/
theorem inv_mul_mem_T (i : ι) {r : V} (hr : r ∈ (D.Rs i).T) : (D.s i)⁻¹ * (r : G) ∈ D.RU.T :=
  D.bij.mapsTo (x := ⟨i, r⟩) (Finset.mem_coe.mpr (Finset.mem_sigma.mpr ⟨Finset.mem_univ i, hr⟩))

/-- **Compatibility of the representative maps**: for `y ∈ V`, the representative of the right
coset `U s_i⁻¹ y` is `s_i⁻¹ ŷ`, where `ŷ` is the representative of `(V ∩ s_iUs_i⁻¹) y`
(Brown III.9–10). -/
theorem hat_conj (i : ι) (y : V) :
    D.RU.hat ((D.s i)⁻¹ * (y : G)) = (D.s i)⁻¹ * ((D.Rs i).hat y : G) := by
  refine (D.RU.hat_eq _ _ ?_).trans (D.RU.hat_self _ (D.inv_mul_mem_T i ((D.Rs i).hat_mem y)))
  have h := U.inv_mem (mem_conjInter.mp ((D.Rs i).hat_mul_inv_mem y))
  have e : (D.s i)⁻¹ * (y : G) * ((D.s i)⁻¹ * ((D.Rs i).hat y : G))⁻¹ =
      ((D.s i)⁻¹ * (((D.Rs i).hat y * y⁻¹ : V) : G) * D.s i)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact h

/-- **The `s_i` cover `V\G/U`**: every `g ∈ G` lies in some double coset `V s_i U`
(Brown III.9–10). -/
theorem exists_eq_mul_s_mul (g : G) : ∃ i, ∃ v ∈ V, ∃ u ∈ U, g = v * D.s i * u := by
  obtain ⟨⟨i, r⟩, -, ht⟩ := D.bij.surjOn (Finset.mem_coe.mpr (D.RU.hat_mem g⁻¹))
  have ht' : (D.s i)⁻¹ * (r : G) = D.RU.hat g⁻¹ := ht
  refine ⟨i, (r : G)⁻¹, V.inv_mem r.2, (D.s i)⁻¹ * (r : G) * g, ?_, by group⟩
  have hu := D.RU.hat_mul_inv_mem g⁻¹
  rw [inv_inv, ← ht'] at hu
  exact hu

/-- **The double cosets `V s_i U` are distinct**: if `s_j ∈ V s_i U` then `i = j`
(Brown III.9–10). Together with `exists_eq_mul_s_mul`: the `s_i` represent `V\G/U`. -/
theorem eq_of_s_eq_mul {i j : ι} {v u : G} (hv : v ∈ V) (hu : u ∈ U)
    (h : D.s j = v * D.s i * u) : i = j := by
  have hrj := (D.Rs j).hat_mem 1
  let y : V := ⟨v⁻¹, V.inv_mem hv⟩ * (D.Rs j).hat 1
  have hri := (D.Rs i).hat_mem y
  have hw := mem_conjInter.mp ((D.Rs i).hat_mul_inv_mem y)
  have hti := D.inv_mul_mem_T i hri
  have htj := D.inv_mul_mem_T j hrj
  have key : ∀ (si sj hi hj : G), sj = v * si * u →
      si⁻¹ * hi * (sj⁻¹ * hj)⁻¹ = (si⁻¹ * (hi * (v⁻¹ * hj)⁻¹) * si) * u := by
    intro si sj hi hj hs
    rw [hs]
    group
  have hsame : (D.s i)⁻¹ * ((D.Rs i).hat y : G) * ((D.s j)⁻¹ * ((D.Rs j).hat 1 : G))⁻¹ ∈ U := by
    rw [key (D.s i) (D.s j) _ _ h]
    exact U.mul_mem hw hu
  have heq : (D.s i)⁻¹ * ((D.Rs i).hat y : G) = (D.s j)⁻¹ * ((D.Rs j).hat 1 : G) := by
    rw [← D.RU.hat_self _ hti, ← D.RU.hat_self _ htj]
    exact D.RU.hat_eq _ _ hsame
  have hp : (⟨i, (D.Rs i).hat y⟩ : Σ _ : ι, V) = ⟨j, (D.Rs j).hat 1⟩ :=
    D.bij.injOn (Finset.mem_coe.mpr (Finset.mem_sigma.mpr ⟨Finset.mem_univ i, hri⟩))
      (Finset.mem_coe.mpr (Finset.mem_sigma.mpr ⟨Finset.mem_univ j, hrj⟩)) heq
  exact congrArg Sigma.fst hp

end MackeyData

/-- Partial products commute with the inclusion of a subgroup. -/
theorem coe_partialProd (H : Subgroup G) {n : ℕ} (v : Fin n → H) (j : Fin (n + 1)) :
    ((Fin.partialProd v j : H) : G) = Fin.partialProd (fun i => (v i : G)) j := by
  induction j using Fin.induction with
  | zero => simp only [Fin.partialProd_zero, Subgroup.coe_one]
  | succ j ih => rw [Fin.partialProd_succ, Fin.partialProd_succ, Subgroup.coe_mul, ih]

end Data

/-! ### The double coset formula on cochains -/

section Formula

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U V : Subgroup G} {ι : Type*} [Fintype ι]

namespace MackeyData

variable (D : MackeyData U V ι)

/-- **The arguments of corestriction under the double coset decomposition**: for `r ∈ V` and
`v ∈ Vⁿ`, the arguments of `cor^G_U` at the representative `s_i⁻¹ r` and `v` are the conjugates
`s_i⁻¹ (·) s_i` of the arguments of `cor^V_{V ∩ s_iUs_i⁻¹}` at `r` and `v` (Brown III.9–10). -/
theorem corArg_conj (i : ι) {n : ℕ} (r : V) (v : Fin n → V) :
    D.RU.corArg ((D.s i)⁻¹ * (r : G)) (fun j => (v j : G)) =
      fun j => conjHom U V (D.s i) ((D.Rs i).corArg r v j) := by
  funext j
  apply Subtype.ext
  rw [RightTransversal.coe_corArg, coe_conjHom_apply, RightTransversal.coe_corArg]
  have e : ∀ m : Fin (n + 1), (D.s i)⁻¹ * (r : G) * Fin.partialProd (fun j => (v j : G)) m =
      (D.s i)⁻¹ * ((r * Fin.partialProd v m : V) : G) := by
    intro m
    rw [Subgroup.coe_mul, coe_partialProd, mul_assoc]
  rw [e, e, D.hat_conj, D.hat_conj]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

variable {k : Type u} [CommRing k]
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]

/-- **The double coset formula for the corestriction formula** (Brown III.9–10; NSW I §5): for a
function `c : Uⁿ → M` and `v ∈ Vⁿ`,
`(cor^G_U c)(v) = ∑_i ∑_{r ∈ T(Rs i)} r⁻¹ • s_i • c(s_i⁻¹ · corArg_r(v) · s_i)`, i.e.
`res^G_V cor^G_U c = ∑_i cor^V_{V ∩ s_iUs_i⁻¹}(s_i • c(s_i⁻¹ (·) s_i))`. PROVED. -/
theorem corFun_eq {n : ℕ} (c : (Fin n → U) → M) (v : Fin n → V) :
    D.RU.corFun c (fun j => (v j : G)) =
      ∑ i, ∑ r ∈ (D.Rs i).T,
        (r : G)⁻¹ • D.s i • c (fun j => conjHom U V (D.s i) ((D.Rs i).corArg r v j)) := by
  rw [RightTransversal.corFun_apply, Finset.sum_sigma']
  symm
  refine Finset.sum_nbij (fun p : (Σ _ : ι, V) => (D.s p.1)⁻¹ * (p.2 : G))
    (fun a ha => D.bij.mapsTo ha) D.bij.injOn D.bij.surjOn ?_
  rintro ⟨i, r⟩ _
  simp only
  rw [D.corArg_conj, mul_inv_rev, inv_inv, mul_smul]

end MackeyData

end Formula

/-! ### Evaluating cochain maps into continuous cochains -/

section Evaluation

variable {k : Type u} [CommRing k] {H : Type u} [Group H] [TopologicalSpace H] [ContinuousMul H]
  {N : Type u} [AddCommGroup N] [Module k N] [DistribMulAction H N] [SMulCommClass H k N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul k N] [ContinuousSMul H N]
  {X : CochainComplex (ModuleCat.{u} k) ℕ}

/-- Two cochain maps into `C^•_cont(H, N)` are equal once they agree, in every degree and on every
cochain, as functions `Hⁿ → N` (continuous cochains are functions; NSW I §2). -/
theorem contCochains_hom_ext {φ ψ : X ⟶ contCochains k H N}
    (h : ∀ (n : ℕ) (c : X.X n) (x : Fin n → H),
      asFun k H N (((contSubCx k H N).el ((φ.f n).hom c) : contCochain k H N n) :
          (groupCohomology.inhomogeneousCochains (rep k H N)).X n) x =
        asFun k H N (((contSubCx k H N).el ((ψ.f n).hom c) : contCochain k H N n) :
          (groupCohomology.inhomogeneousCochains (rep k H N)).X n) x) :
    φ = ψ := by
  ext n c
  apply Subtype.ext
  funext x
  exact h n c x

/-- A finite sum of cochain maps into `C^•_cont(H, N)` is evaluated termwise (the sum of cochain
maps is computed degreewise and pointwise). -/
theorem contCochains_sum_apply {ι : Type*} (s : Finset ι) (φ : ι → (X ⟶ contCochains k H N))
    (n : ℕ) (c : X.X n) (x : Fin n → H) :
    asFun k H N (((contSubCx k H N).el (((∑ i ∈ s, φ i).f n).hom c) : contCochain k H N n) :
        (groupCohomology.inhomogeneousCochains (rep k H N)).X n) x =
      ∑ i ∈ s, asFun k H N (((contSubCx k H N).el (((φ i).f n).hom c) : contCochain k H N n) :
        (groupCohomology.inhomogeneousCochains (rep k H N)).X n) x := by
  let F : (X ⟶ contCochains k H N) →+ N :=
    { toFun := fun φ => asFun k H N (((contSubCx k H N).el ((φ.f n).hom c) :
          contCochain k H N n) : (groupCohomology.inhomogeneousCochains (rep k H N)).X n) x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact map_sum F φ s

end Evaluation

/-- `homologyMap` commutes with finite sums of cochain maps (the homology functor is additive). -/
theorem homologyMap_finset_sum {k : Type u} [CommRing k] {K L : CochainComplex (ModuleCat.{u} k) ℕ}
    {ι : Type*} (s : Finset ι) (f : ι → (K ⟶ L)) (n : ℕ) :
    HomologicalComplex.homologyMap (∑ i ∈ s, f i) n =
      ∑ i ∈ s, HomologicalComplex.homologyMap (f i) n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) n).map_sum f s

/-! ### The cochain-level double coset formula -/

section MainFormula

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U V : Subgroup G} {ι : Type*} [Fintype ι]
  {k : Type u} [CommRing k]
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

namespace MackeyData

variable (D : MackeyData U V ι)

/-- **The double coset (Mackey) formula on continuous cochains** (K7), tex 6971–6979 (Brown,
*Cohomology of Groups*, III.9–10; Neukirch–Schmidt–Wingberg I §5): for an open subgroup `U` and a
compatible system of transversals `D`, the equality of cochain maps
`C^•_cont(U, M) → C^•_cont(V, M)`
```
res^G_V ∘ cor^G_U = ∑_i cor^V_{V ∩ s_iUs_i⁻¹} ∘ (res^{s_iUs_i⁻¹}_{V ∩ s_iUs_i⁻¹} ∘ (s_i ·)),
```
where the middle map is the cochain map of the compatible pair (`w ↦ s_i⁻¹ w s_i`, `m ↦ s_i • m`).
It holds on the nose (no homotopy). PROVED. -/
theorem corCochains_comp_resCochains (hU : IsOpen (U : Set G)) :
    D.RU.corCochains (k := k) (M := M) hU ≫ resCochains (subgroupIncl V) =
      ∑ i, contCochainsMap (conjHom U V (D.s i)) (conjSMul (k := k) (M := M) U V (D.s i))
          (continuous_conjSMul U V (D.s i)) (conjSMul_compat U V (D.s i)) ≫
        (D.Rs i).corCochains (isOpen_conjInter hU V (D.s i)) := by
  refine contCochains_hom_ext fun n c v => ?_
  rw [contCochains_sum_apply]
  refine (D.corFun_eq (M := M) (asFun k U (ResMod (subgroupIncl U) M)
    (((contSubCx k U (ResMod (subgroupIncl U) M)).el c :
      contCochain k U (ResMod (subgroupIncl U) M) n) :
        (groupCohomology.inhomogeneousCochains (rep k U (ResMod (subgroupIncl U) M))).X n))
          v).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rfl

/-- **The double coset (Mackey) formula on continuous cohomology** (K7), tex 6971–6979 (Brown
III.9–10; NSW I §5): on `Hⁿ_cont`,
`res^G_V ∘ cor^G_U = ∑_i cor^V_{V ∩ s_iUs_i⁻¹} ∘ res^{s_iUs_i⁻¹}_{V ∩ s_iUs_i⁻¹} ∘ (s_i ·)`.
PROVED (from the cochain-level identity). -/
theorem homologyMap_corCochains_comp_resCochains (hU : IsOpen (U : Set G)) (n : ℕ) :
    HomologicalComplex.homologyMap (D.RU.corCochains (k := k) (M := M) hU) n ≫
        HomologicalComplex.homologyMap (resCochains (k := k) (M := M) (subgroupIncl V)) n =
      ∑ i, HomologicalComplex.homologyMap (contCochainsMap (conjHom U V (D.s i))
          (conjSMul (k := k) (M := M) U V (D.s i)) (continuous_conjSMul U V (D.s i))
          (conjSMul_compat U V (D.s i))) n ≫
        HomologicalComplex.homologyMap ((D.Rs i).corCochains (isOpen_conjInter hU V (D.s i))) n := by
  rw [← HomologicalComplex.homologyMap_comp, D.corCochains_comp_resCochains hU,
    homologyMap_finset_sum]
  exact Finset.sum_congr rfl fun i _ => HomologicalComplex.homologyMap_comp _ _ _

/-- **Vanishing of the summands** (K7), tex 6971–6979: if for every double coset representative
`s_i` the class `res^{s_iUs_i⁻¹}_{V ∩ s_iUs_i⁻¹}(s_i z)` vanishes, then `res^G_V cor^G_U z = 0`
(the text's use: if all upper inertia restrictions vanish, every summand is zero). PROVED. -/
theorem res_cor_eq_zero_of_forall (hU : IsOpen (U : Set G)) (n : ℕ)
    (z : contCohomology k U (ResMod (subgroupIncl U) M) n)
    (hz : ∀ i, (HomologicalComplex.homologyMap (contCochainsMap (conjHom U V (D.s i))
      (conjSMul (k := k) (M := M) U V (D.s i)) (continuous_conjSMul U V (D.s i))
      (conjSMul_compat U V (D.s i))) n).hom z = 0) :
    (HomologicalComplex.homologyMap (resCochains (k := k) (M := M) (subgroupIncl V)) n).hom
      ((HomologicalComplex.homologyMap (D.RU.corCochains (k := k) (M := M) hU) n).hom z) = 0 := by
  have h := congrArg (fun φ => φ.hom z) (D.homologyMap_corCochains_comp_resCochains hU n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum, LinearMap.sum_apply,
    hz, map_zero, Finset.sum_const_zero] at h
  exact h

end MackeyData

end MainFormula

/-! ### Non-vacuity -/

section Examples

variable {G : Type u} [Group G]

/-- **The case `U = G`** of the double coset formula: one double coset, `s = 1`, and the trivial
transversals `{1}` of `G` in `G` and of `V ∩ G` in `V` (Brown III.9–10). -/
def MackeyData.ofTopLeft (V : Subgroup G) : MackeyData (⊤ : Subgroup G) V Unit where
  s := fun _ => 1
  RU := RightTransversal.ofForallMem ⊤ Subgroup.mem_top
  Rs := fun _ => RightTransversal.ofForallMem _ fun _ => mem_conjInter.mpr (Subgroup.mem_top _)
  bij := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨i, r⟩ hr
      have hr' : r = 1 := Finset.mem_singleton.mp (Finset.mem_sigma.mp (Finset.mem_coe.mp hr)).2
      subst hr'
      simp [RightTransversal.ofForallMem]
    · rintro ⟨i, r⟩ hr ⟨j, r'⟩ hr' _
      have e1 : r = 1 := Finset.mem_singleton.mp (Finset.mem_sigma.mp (Finset.mem_coe.mp hr)).2
      have e2 : r' = 1 := Finset.mem_singleton.mp (Finset.mem_sigma.mp (Finset.mem_coe.mp hr')).2
      subst e1
      subst e2
      rfl
    · intro t ht
      have e : t = 1 := Finset.mem_singleton.mp ht
      subst e
      exact ⟨⟨(), 1⟩, Finset.mem_coe.mpr (Finset.mem_sigma.mpr
        ⟨Finset.mem_univ _, Finset.mem_singleton_self _⟩), by simp⟩

/-- A right transversal of `U` in `G`, transported to a right transversal of `G ∩ U` in `G`
(viewed as the subgroup `⊤`). -/
def RightTransversal.toTop {U : Subgroup G} (R : RightTransversal U) :
    RightTransversal (conjInter U ⊤ 1) where
  T := R.T.map ⟨fun g => (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G)),
    fun _ _ h => congrArg Subtype.val h⟩
  hat := fun y => ⟨R.hat y, Subgroup.mem_top _⟩
  hat_mem := fun y => Finset.mem_map_of_mem _ (R.hat_mem y)
  hat_mul_inv_mem := fun y => mem_conjInter.mpr (by simpa using R.hat_mul_inv_mem y)
  hat_eq := fun x y h => Subtype.ext (R.hat_eq x y (by simpa using mem_conjInter.mp h))
  hat_self := fun t ht => by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp ht
    exact Subtype.ext (R.hat_self a ha)

/-- **The case `V = G`** of the double coset formula: one double coset, `s = 1`, an arbitrary
right transversal of `U` in `G`, and its transport to `G ∩ U ≤ G` (Brown III.9–10). -/
def MackeyData.ofTopRight {U : Subgroup G} (R : RightTransversal U) :
    MackeyData U (⊤ : Subgroup G) Unit where
  s := fun _ => 1
  RU := R
  Rs := fun _ => R.toTop
  bij := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨i, r⟩ hr
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp (Finset.mem_sigma.mp (Finset.mem_coe.mp hr)).2
      change (1 : G)⁻¹ * a ∈ R.T
      rwa [inv_one, one_mul]
    · rintro ⟨i, r⟩ _ ⟨j, r'⟩ _ h
      have h' : r = r' := Subtype.ext (by simpa using h)
      subst h'
      rfl
    · intro t ht
      refine ⟨⟨(), ⟨t, Subgroup.mem_top t⟩⟩, Finset.mem_coe.mpr (Finset.mem_sigma.mpr
        ⟨Finset.mem_univ _, Finset.mem_map_of_mem _ (Finset.mem_coe.mp ht)⟩), ?_⟩
      simp

end Examples

/-! ### Existence of compatible systems of transversals -/

section Existence

variable {G : Type u} [Group G]

/-- **The double coset relation** `a ~ b ⟺ b ∈ V a U` on `G` (Brown III.9–10; NSW I §5); its
quotient is the double coset space `V\G/U`. It equals Mathlib's `DoubleCoset.setoid`
(`dcSetoid_eq`). -/
def dcSetoid (V U : Subgroup G) : Setoid G where
  r a b := ∃ v ∈ V, ∃ u ∈ U, b = v * a * u
  iseqv :=
    { refl := fun _ => ⟨1, V.one_mem, 1, U.one_mem, by group⟩
      symm := fun {_ _} ⟨v, hv, u, hu, h⟩ =>
        ⟨v⁻¹, V.inv_mem hv, u⁻¹, U.inv_mem hu, by rw [h]; group⟩
      trans := fun {_ _ _} ⟨v, hv, u, hu, h⟩ ⟨v', hv', u', hu', h'⟩ =>
        ⟨v' * v, V.mul_mem hv' hv, u * u', U.mul_mem hu hu', by rw [h', h]; group⟩ }

/-- Unfolding the double coset relation. -/
theorem dcSetoid_r {V U : Subgroup G} {a b : G} :
    (dcSetoid V U).r a b ↔ ∃ v ∈ V, ∃ u ∈ U, b = v * a * u :=
  Iff.rfl

/-- The double coset relation is Mathlib's `DoubleCoset.setoid` (`DoubleCoset.rel_iff`). -/
theorem dcSetoid_eq (V U : Subgroup G) :
    dcSetoid V U = DoubleCoset.setoid (V : Set G) (U : Set G) := by
  ext a b
  exact DoubleCoset.rel_iff.symm

/-- **The double coset space** `V\G/U` (Brown III.9–10; NSW I §5). -/
abbrev DoubleCosets (V U : Subgroup G) : Type u := Quotient (dcSetoid V U)

/-- For `U` of finite index, `V\G/U` is finite (it is a quotient of `G/U`). -/
theorem finite_doubleCosets (V U : Subgroup G) [U.FiniteIndex] : Finite (DoubleCosets V U) := by
  refine Finite.of_surjective (fun q : G ⧸ U => Quotient.liftOn' q
    (fun g => (Quotient.mk (dcSetoid V U) g)) fun a b h => Quotient.sound
      (dcSetoid_r.mpr ⟨1, V.one_mem, a⁻¹ * b, QuotientGroup.leftRel_apply.mp h, by group⟩)) ?_
  intro d
  induction d using Quotient.inductionOn with
  | h g => exact ⟨(QuotientGroup.mk g : G ⧸ U), rfl⟩

/-- For `U` of finite index in `G`, `V ∩ s U s⁻¹` has finite index in `V` (Brown III.9). -/
instance finiteIndex_conjInter (U V : Subgroup G) [U.FiniteIndex] (s : G) :
    (conjInter U V s).FiniteIndex := by
  have : (U.map (MulAut.conj s).toMonoidHom).FiniteIndex :=
    Subgroup.FiniteIndex.map_of_surjective U (MulAut.conj s).surjective
  exact inferInstanceAs ((U.map (MulAut.conj s).toMonoidHom).comap V.subtype).FiniteIndex

namespace MackeyData

variable (U V : Subgroup G) [U.FiniteIndex]

/-- Chosen right transversals of `V ∩ s_i U s_i⁻¹` in `V`, for the chosen double coset
representatives `s_i` (Brown III.9–10). -/
def dcRs (i : DoubleCosets V U) : RightTransversal (conjInter U V i.out) :=
  RightTransversal.ofFiniteIndex _

/-- **Uniqueness**: if `s_i⁻¹ r` and `s_j⁻¹ r'` (with `r`, `r'` representatives of `dcRs i`,
`dcRs j`) lie in the same right coset of `U`, then `i = j` and `r = r'` (Brown III.9–10). -/
theorem dc_unique {i j : DoubleCosets V U} {r r' : V} (hr : r ∈ (dcRs U V i).T)
    (hr' : r' ∈ (dcRs U V j).T) (h : i.out⁻¹ * (r : G) * (j.out⁻¹ * (r' : G))⁻¹ ∈ U) :
    i = j ∧ r = r' := by
  have hij : i = j := by
    refine (Quotient.out_eq i).symm.trans ((Quotient.sound (dcSetoid_r.mpr
      ⟨(r' : G) * (r : G)⁻¹, V.mul_mem r'.2 (V.inv_mem r.2),
        i.out⁻¹ * (r : G) * (j.out⁻¹ * (r' : G))⁻¹, h, ?_⟩)).trans (Quotient.out_eq j))
    group
  subst hij
  refine ⟨rfl, ?_⟩
  have hw : r * r'⁻¹ ∈ conjInter U V i.out := by
    rw [mem_conjInter]
    have e : i.out⁻¹ * ((r * r'⁻¹ : V) : G) * i.out =
        i.out⁻¹ * (r : G) * (i.out⁻¹ * (r' : G))⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h
  rw [← (dcRs U V i).hat_self r hr, ← (dcRs U V i).hat_self r' hr']
  exact (dcRs U V i).hat_eq r' r hw

variable [Fintype (DoubleCosets V U)]

/-- **Covering**: every right coset `U x` contains some `s_i⁻¹ r` with `r` a representative of
`dcRs i` (Brown III.9–10). -/
theorem dc_cover (x : G) : ∃ p : (Σ _ : DoubleCosets V U, V),
    p ∈ (Finset.univ.sigma fun i => (dcRs U V i).T) ∧ (p.1.out)⁻¹ * (p.2 : G) * x⁻¹ ∈ U := by
  obtain ⟨i, hi⟩ : ∃ i : DoubleCosets V U,
      Quotient.mk (dcSetoid V U) i.out = Quotient.mk (dcSetoid V U) x⁻¹ :=
    ⟨_, Quotient.out_eq _⟩
  obtain ⟨v, hv, u, hu, hx⟩ := dcSetoid_r.mp (Quotient.exact hi)
  obtain ⟨y, hy⟩ : ∃ y : V, (y : G) = v⁻¹ := ⟨⟨v⁻¹, V.inv_mem hv⟩, rfl⟩
  refine ⟨⟨i, (dcRs U V i).hat y⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
    (dcRs U V i).hat_mem y⟩, ?_⟩
  have hw := mem_conjInter.mp ((dcRs U V i).hat_mul_inv_mem y)
  have e : (i.out)⁻¹ * ((dcRs U V i).hat y : G) * x⁻¹ =
      ((i.out)⁻¹ * (((dcRs U V i).hat y * y⁻¹ : V) : G) * i.out) * u := by
    rw [hx]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hy, inv_inv]
    group
  rw [e]
  exact U.mul_mem hw hu

open Classical in
/-- **The right transversal `{s_i⁻¹ r}` of `U` in `G`** built from the double coset
representatives and the transversals `dcRs i` (Brown III.9–10; NSW I §5): the representative of
`U x` is the unique `s_i⁻¹ r` in it. -/
def dcRU : RightTransversal U where
  T := (Finset.univ.sigma fun i => (dcRs U V i).T).image (fun p => (p.1.out)⁻¹ * (p.2 : G))
  hat x := ((Classical.choose (dc_cover U V x)).1.out)⁻¹ *
    ((Classical.choose (dc_cover U V x)).2 : G)
  hat_mem x := Finset.mem_image_of_mem _ (Classical.choose_spec (dc_cover U V x)).1
  hat_mul_inv_mem x := (Classical.choose_spec (dc_cover U V x)).2
  hat_eq x y h := by
    obtain ⟨hp, hpy⟩ := Classical.choose_spec (dc_cover U V y)
    obtain ⟨hq, hqx⟩ := Classical.choose_spec (dc_cover U V x)
    have key := dc_unique U V (Finset.mem_sigma.mp hp).2 (Finset.mem_sigma.mp hq).2 (by
      have := U.mul_mem (U.mul_mem hpy h) (U.inv_mem hqx)
      convert this using 1
      group)
    rw [key.1, key.2]
  hat_self t ht := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hq, hqx⟩ := Classical.choose_spec (dc_cover U V ((p.1.out)⁻¹ * (p.2 : G)))
    have key := dc_unique U V (Finset.mem_sigma.mp hq).2 (Finset.mem_sigma.mp hp).2 hqx
    rw [key.1, key.2]

/-- Membership in the transversal `dcRU`: the elements `s_i⁻¹ r`. -/
theorem mem_dcRU_T {t : G} : t ∈ (dcRU U V).T ↔
    ∃ p ∈ (Finset.univ.sigma fun i => (dcRs U V i).T), (p.1.out)⁻¹ * (p.2 : G) = t := by
  classical
  exact Finset.mem_image

/-- **Existence of compatible systems of transversals** (Brown III.9–10; NSW I §5): for `U` of
finite index and any `V`, the double coset representatives `s_i = out(i)` (`i ∈ V\G/U`), chosen
transversals of `V ∩ s_iUs_i⁻¹` in `V`, and the transversal `{s_i⁻¹ r}` of `U` form a
`MackeyData`. -/
def ofFiniteIndex : MackeyData U V (DoubleCosets V U) where
  s i := i.out
  RU := dcRU U V
  Rs := dcRs U V
  bij := by
    refine ⟨fun p hp => (mem_dcRU_T U V).mpr ⟨p, hp, rfl⟩, fun p hp q hq h => ?_, fun t ht => ?_⟩
    · have key := dc_unique U V (Finset.mem_sigma.mp hp).2 (Finset.mem_sigma.mp hq).2 (by
        have h' : p.1.out⁻¹ * (p.2 : G) = q.1.out⁻¹ * (q.2 : G) := h
        rw [h', mul_inv_cancel]
        exact U.one_mem)
      exact Sigma.ext key.1 (heq_of_eq key.2)
    · obtain ⟨p, hp, rfl⟩ := (mem_dcRU_T U V).mp ht
      exact ⟨p, hp, rfl⟩

end MackeyData

/-- **Compatible systems of transversals exist** for every subgroup `U` of finite index and every
subgroup `V` (index set: the finite double coset space `V\G/U`). With
`MackeyData.corCochains_comp_resCochains`, the cochain-level double coset formula (K7),
tex 6971–6979, holds for every open subgroup `U` of finite index and every `V`. PROVED. -/
theorem MackeyData.exists_of_finiteIndex (U V : Subgroup G) [U.FiniteIndex] :
    ∃ (ι : Type u) (_ : Fintype ι), Nonempty (MackeyData U V ι) := by
  have := finite_doubleCosets V U
  let _ : Fintype (DoubleCosets V U) := Fintype.ofFinite _
  exact ⟨DoubleCosets V U, inferInstance, ⟨MackeyData.ofFiniteIndex U V⟩⟩

/-- **The vanishing statement of (K7) without choices of representatives**, tex 6971–6979: for an
open subgroup `U` of finite index of a topological group `G`, any subgroup `V` and a class
`z ∈ Hⁿ_cont(U, M)` with `res^{sUs⁻¹}_{V ∩ sUs⁻¹}(s z) = 0` for **every** `s ∈ G`, the class
`res^G_V cor^G_U z` vanishes, corestriction being computed with the transversal
`MackeyData.dcRU U V` (Brown III.9–10; NSW I §5). PROVED. -/
theorem res_cor_eq_zero_of_forall_conj {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {U : Subgroup G} (V : Subgroup G) [U.FiniteIndex]
    [Fintype (DoubleCosets V U)] {k : Type u} [CommRing k]
    {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]
    (hU : IsOpen (U : Set G)) (n : ℕ) (z : contCohomology k U (ResMod (subgroupIncl U) M) n)
    (hz : ∀ s : G, (HomologicalComplex.homologyMap (contCochainsMap (conjHom U V s)
      (conjSMul (k := k) (M := M) U V s) (continuous_conjSMul U V s)
      (conjSMul_compat U V s)) n).hom z = 0) :
    (HomologicalComplex.homologyMap (resCochains (k := k) (M := M) (subgroupIncl V)) n).hom
      ((HomologicalComplex.homologyMap ((MackeyData.dcRU U V).corCochains (k := k) (M := M) hU)
        n).hom z) = 0 :=
  (MackeyData.ofFiniteIndex U V).res_cor_eq_zero_of_forall hU n z fun _ => hz _

end Existence

end ZInQ.Manuscript.RC.SelmerComplex
