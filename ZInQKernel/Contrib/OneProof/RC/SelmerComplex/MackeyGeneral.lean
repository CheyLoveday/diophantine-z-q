import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Shapiro
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Mackey

/-!
# Lane RC26 (round 3): the double coset formula for arbitrary transversals

Manuscript `diophantine_zq.tex`, (K7), tex 6971–6979; Brown, *Cohomology of Groups*, III.9–10;
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, I §5.

`Mackey.lean` proves the double coset formula on the nose for a compatible system of transversals
(`MackeyData`). With the transversal independence of corestriction up to explicit homotopy
(`corIndepHomotopy`, from the Shapiro machinery), this file gives:

* `MackeyData.mackeyHomotopy`: for **any** transversal `R` of `U\G`,
  `res^G_V ∘ cor_R ≃ Σ_i cor^V_{W_i} ∘ (res ∘ s_i)` with an explicit homotopy
  (`W_i = V ∩ s_i U s_i⁻¹`);
* `MackeyData.mackey_cohomology`: on `Hⁿ_cont`, for any transversal `R` of `U\G` and any
  transversals `R'_i` of `W_i\V`, `res^G_V ∘ cor^G_U = Σ_i cor^V_{W_i} ∘ res ∘ (s_i ·)` (the formula
  (K7) with no condition on the transversals);
* `res_cor_eq_zero_of_forall_conj'`: the text's vanishing statement for every transversal.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open CategoryTheory

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U V : Subgroup G} [U.FiniteIndex] {ι : Type*} [Fintype ι]
  {k : Type u} [CommRing k]
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

namespace MackeyData

variable (D : MackeyData U V ι)

/-- **The double coset formula up to an explicit homotopy, for any transversal of `U\G`** (K7),
tex 6971–6979: for an open subgroup `U` of finite index, any right transversal `R` of `U\G` and a
compatible system `D`, `res^G_V ∘ cor_R ≃ Σ_i cor^V_{W_i} ∘ res^{s_iUs_i⁻¹}_{W_i} ∘ (s_i ·)`. The
homotopy is the transversal-change homotopy `corIndepHomotopy` (prism homotopy between the
retractions `G → U`) followed by restriction to `V`. PROVED. -/
def mackeyHomotopy (hU : IsOpen (U : Set G)) (R : RightTransversal U) :
    Homotopy (R.corCochains (k := k) (M := M) hU ≫ resCochains (subgroupIncl V))
      (∑ i, contCochainsMap (conjHom U V (D.s i)) (conjSMul (k := k) (M := M) U V (D.s i))
          (continuous_conjSMul U V (D.s i)) (conjSMul_compat U V (D.s i)) ≫
        (D.Rs i).corCochains (isOpen_conjInter hU V (D.s i))) :=
  ((corIndepHomotopy D.RU hU k M R).compRight (resCochains (subgroupIncl V))).trans
    (Homotopy.ofEq (D.corCochains_comp_resCochains hU))

/-- **The double coset formula (K7) on continuous cohomology, for arbitrary transversals**
(tex 6971–6979; Brown III.9–10; NSW I §5): for an open subgroup `U` of finite index, any right
transversal `R` of `U\G`, double coset representatives `s_i` (from a compatible system `D`) and
**any** right transversals `R'_i` of `W_i = V ∩ s_iUs_i⁻¹` in `V`, on `Hⁿ_cont`,
`res^G_V ∘ cor^G_U = Σ_i cor^V_{W_i} ∘ res^{s_iUs_i⁻¹}_{W_i} ∘ (s_i ·)`. PROVED. -/
theorem mackey_cohomology (hU : IsOpen (U : Set G)) (R : RightTransversal U)
    (R' : ∀ i, RightTransversal (conjInter U V (D.s i))) (n : ℕ) :
    HomologicalComplex.homologyMap (R.corCochains (k := k) (M := M) hU) n ≫
        HomologicalComplex.homologyMap (resCochains (k := k) (M := M) (subgroupIncl V)) n =
      ∑ i, HomologicalComplex.homologyMap (contCochainsMap (conjHom U V (D.s i))
          (conjSMul (k := k) (M := M) U V (D.s i)) (continuous_conjSMul U V (D.s i))
          (conjSMul_compat U V (D.s i))) n ≫
        HomologicalComplex.homologyMap ((R' i).corCochains (isOpen_conjInter hU V (D.s i))) n := by
  rw [← HomologicalComplex.homologyMap_comp, (D.mackeyHomotopy hU R).homologyMap_eq n,
    homologyMap_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [HomologicalComplex.homologyMap_comp,
    (corIndepHomotopy (G := V) (U := conjInter U V (D.s i)) (D.Rs i)
      (isOpen_conjInter hU V (D.s i)) k (ResMod (subgroupIncl V) M) (R' i)).homologyMap_eq n]

end MackeyData

omit [DiscreteTopology M] in
/-- Corestriction on cohomology does not depend on the transversal. PROVED (from
`corIndepHomotopy`). -/
theorem corCohomology_indep [DiscreteTopology M] (hU : IsOpen (U : Set G))
    (R R' : RightTransversal U) (n : ℕ) :
    R'.corCohomology (k := k) (M := M) hU n = R.corCohomology hU n :=
  (corIndepHomotopy R hU k M R').homologyMap_eq n

/-- **The vanishing statement of (K7) for every transversal** (tex 6971–6979: "if all upper
inertia restrictions vanish, every summand is zero"): for an open subgroup `U` of finite index,
any subgroup `V`, any right transversal `R` of `U\G`, and `z ∈ Hⁿ_cont(U, M)` with
`res^{sUs⁻¹}_{V ∩ sUs⁻¹}(s z) = 0` for every `s ∈ G`, `res^G_V cor_R z = 0`. PROVED. -/
theorem res_cor_eq_zero_of_forall_conj' (V : Subgroup G) [Fintype (DoubleCosets V U)]
    (hU : IsOpen (U : Set G)) (R : RightTransversal U) (n : ℕ)
    (z : contCohomology k U (ResMod (subgroupIncl U) M) n)
    (hz : ∀ s : G, (HomologicalComplex.homologyMap (contCochainsMap (conjHom U V s)
      (conjSMul (k := k) (M := M) U V s) (continuous_conjSMul U V s)
      (conjSMul_compat U V s)) n).hom z = 0) :
    (HomologicalComplex.homologyMap (resCochains (k := k) (M := M) (subgroupIncl V)) n).hom
      ((HomologicalComplex.homologyMap (R.corCochains (k := k) (M := M) hU) n).hom z) = 0 := by
  have h := corCohomology_indep (k := k) (M := M) hU (MackeyData.dcRU U V) R n
  change (HomologicalComplex.homologyMap (resCochains (k := k) (M := M) (subgroupIncl V)) n).hom
      ((R.corCohomology (k := k) (M := M) hU n).hom z) = 0
  rw [h]
  exact res_cor_eq_zero_of_forall_conj V hU n z hz

end ZInQ.Manuscript.RC.SelmerComplex
