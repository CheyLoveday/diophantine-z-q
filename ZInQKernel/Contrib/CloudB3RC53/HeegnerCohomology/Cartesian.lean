import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Mackey.Basic

/-!
# HeegnerCohomology, part 10: restriction and corestriction in Cartesian squares

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:arith-finite-heegner`, paragraph 7,
tex 3281–3288: "For a new conductor prime the class-field squares obtained by retaining the
derivative factors are Cartesian, by (H5) and the same local-unit calculation at that prime.
Restriction and corestriction commute in these squares."

For a profinite group `G` (for `G_{H_f}`), an open subgroup `U` (for `G_{H_{fq}}`) and a subgroup
`V` (for `G_{M_I}`), the square of fields is Cartesian (linearly disjoint, `M_I ∩ H_{fq} = H_f`)
exactly when `G = V U`, i.e. there is a single double coset `V \ G / U`.  Then the Mackey formula
(Tau Ceti's `explicitCor1_mackey`) has a single term: `res^G_V ∘ cor^G_U` is the Mackey term at
`s = 1`, which is `cor^V_{V ⊓ U} ∘ res^U_{V ⊓ U}` (`res_cor_cartesian`, `PROVED`).  This is the
hypothesis `hsq` ("`res ∘ cor = cor ∘ res`") of RC10's `FiveTerm.descend_cor`.
-/

namespace ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

open TauCeti.ContCohomology

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type*) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (U V : Subgroup G) [U.FiniteIndex]

/-- **Restriction and corestriction commute in a Cartesian square** (tex 3283–3284), `PROVED`:
if `G = V U`, then `res^G_V (cor^G_U x)` is the single Mackey term at `s = 1`,
`cor^V_{V ⊓ U}(res^U_{V ⊓ U} x)`. -/
theorem res_cor_cartesian (hU : IsOpen (U : Set G))
    (hVU : ∀ g : G, ∃ v ∈ V, ∃ u ∈ U, g = v * u) (x : H1 U M) :
    explicitRes1 G M V (explicitCor1 G M U hU x) = explicitMackeyTerm1 G M U V hU 1 x := by
  have hr : ∀ D : DoubleCoset.Quotient (V : Set G) (U : Set G), DoubleCoset.mk V U 1 = D := by
    intro D
    rw [← DoubleCoset.out_eq' D, DoubleCoset.eq]
    obtain ⟨v, hv, u, hu, h⟩ := hVU D.out
    exact ⟨v, hv, u, hu, by rw [h, mul_one]⟩
  rw [explicitCor1_mackey G M U V (fun _ => 1) hr hU x]
  let _ := Fintype.ofFinite (DoubleCoset.Quotient (V : Set G) (U : Set G))
  rw [Finset.sum_eq_single (DoubleCoset.mk V U 1)]
  · intro b _ hb
    exact absurd (hr b).symm hb
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Node: Cartesian squares** (tex 3281–3284), `PROVED`: for every topological group `G`, open
subgroup `U` of finite index and subgroup `V` with `G = V U`, `res^G_V ∘ cor^G_U` equals the
Mackey term `cor^V_{V ⊓ U} ∘ (1)_* ∘ res^U_{V ⊓ U}` on continuous `H¹` with coefficients in any
topological `G`-module. -/
def CartesianNode : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M] (U V : Subgroup G) [U.FiniteIndex]
    (hU : IsOpen (U : Set G)), (∀ g : G, ∃ v ∈ V, ∃ u ∈ U, g = v * u) →
    ∀ x : H1 U M, explicitRes1 G M V (explicitCor1 G M U hU x) =
      explicitMackeyTerm1 G M U V hU 1 x

theorem cartesianNode_proof : CartesianNode := by
  intro G _ _ _ M _ _ _ _ _ U V _ hU hVU x
  exact res_cor_cartesian G M U V hU hVU x

end ZInQ.Contrib.CloudB3RC53.HeegnerCohomology
