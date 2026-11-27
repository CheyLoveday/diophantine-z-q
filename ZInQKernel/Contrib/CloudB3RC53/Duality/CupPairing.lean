import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree

/-!
# Duality area: the cup product `H¹ × H¹ → H²` of discrete modules through a pairing

The local dualities used in Lemma `ex:arith-local-kummer` (tex L3395–3468) and in
`ex:arith-conjugate-duality` (tex L2761–2830) are cup-product pairings
`H¹(F, M) × H¹(F, N) → H²(F, P)` attached to an equivariant pairing `e : M × N → P`
(for `M = N = E[2^a]`, `P = μ_{2^a}` and `e` the Weil pairing; Milne ADT I.2.3, I.3.2–3.5 as
cited at tex L3439–3441). The vendored library provides explicit continuous cochains in degrees
`≤ 2` (`TauCeti.ContCohomology`) but no cup product. This file defines it on explicit continuous
cohomology of a topological group `G` with discrete coefficient modules:
```
(f ∪ g)(σ, τ) = e(f(σ), σ g(τ)).
```
* `cupCocycle`: the cup of two continuous `1`-cocycles is a continuous `2`-cocycle;
* `cup_d0_left`, `cup_d0_right`: a coboundary cupped with a cocycle (either side) is the
  coboundary of a continuous cochain;
* `cupH`: the induced biadditive map `H¹(G, M) →+ H¹(G, N) →+ H²(G, P)`.

**Classification.** GLUE (the standard cup product in low degree), PROVED.
-/

set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.CloudB3RC53.Duality

open TauCeti.ContCohomology

section Cup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M N P : Type*}
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N] [IsTopologicalAddGroup N]
  [DistribMulAction G N] [ContinuousSMul G N]
  [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P] [IsTopologicalAddGroup P]
  [DistribMulAction G P] [ContinuousSMul G P]
  (e : M →+ N →+ P)

/-- The cup product of cochains, `(f ∪ g)(σ, τ) = e(f(σ), σ g(τ))`. -/
def cupFun (f : G → M) (g : G → N) : G × G → P := fun q => e (f q.1) (q.1 • g q.2)

theorem cupFun_add_left (f f' : G → M) (g : G → N) :
    cupFun e (f + f') g = cupFun e f g + cupFun e f' g := by
  funext q; simp [cupFun]

theorem cupFun_add_right (f : G → M) (g g' : G → N) :
    cupFun e f (g + g') = cupFun e f g + cupFun e f g' := by
  funext q; simp [cupFun, smul_add]

theorem continuous_uncurry_of_discrete {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [DiscreteTopology X] [DiscreteTopology Y] (h : X → Y → Z) :
    Continuous (fun p : X × Y => h p.1 p.2) :=
  continuous_of_discreteTopology

theorem continuous_cupFun {f : G → M} {g : G → N} (hf : Continuous f) (hg : Continuous g) :
    Continuous (cupFun e f g) := by
  have h1 : Continuous fun q : G × G => (f q.1, q.1 • g q.2) :=
    (hf.comp continuous_fst).prodMk (continuous_fst.smul (hg.comp continuous_snd))
  exact (continuous_uncurry_of_discrete (fun m n => e m n)).comp h1

variable {e}

/-- **The cup of two continuous `1`-cocycles is a continuous `2`-cocycle.** -/
theorem cupFun_mem_Z2 (he : ∀ (σ : G) m n, e (σ • m) (σ • n) = σ • e m n)
    {f : G → M} {g : G → N} (hf : f ∈ Z1 G M) (hg : g ∈ Z1 G N) : cupFun e f g ∈ Z2 G P := by
  rw [mem_Z1_iff] at hf hg
  rw [mem_Z2_iff]
  refine ⟨continuous_cupFun e hf.1 hg.1, fun σ τ ρ => ?_⟩
  simp only [cupFun]
  rw [hf.2 σ τ, hg.2 τ ρ, ← he σ, smul_add, smul_smul]
  simp only [map_add, AddMonoidHom.add_apply]
  abel

/-- A coboundary cupped with a cocycle: `(d⁰ a) ∪ g = d¹ (σ ↦ e(a, g σ))`. -/
theorem cup_d0_left (he : ∀ (σ : G) m n, e (σ • m) (σ • n) = σ • e m n)
    (a : M) {g : G → N} (hg : g ∈ Z1 G N) :
    cupFun e (d0 G M a) g = d1 G P (fun σ => e a (g σ)) := by
  rw [mem_Z1_iff] at hg
  funext q
  obtain ⟨σ, τ⟩ := q
  simp only [cupFun, d0_apply, d1_apply, hg.2 σ τ, ← he σ]
  simp only [map_sub, map_add, AddMonoidHom.sub_apply]
  abel

/-- A cocycle cupped with a coboundary: `f ∪ (d⁰ b) = d¹ (σ ↦ -e(f σ, σ b))`. -/
theorem cup_d0_right (he : ∀ (σ : G) m n, e (σ • m) (σ • n) = σ • e m n)
    {f : G → M} (hf : f ∈ Z1 G M) (b : N) :
    cupFun e f (d0 G N b) = d1 G P (fun σ => -e (f σ) (σ • b)) := by
  rw [mem_Z1_iff] at hf
  funext q
  obtain ⟨σ, τ⟩ := q
  simp only [cupFun, d0_apply, d1_apply, hf.2 σ τ, smul_neg, ← he σ, smul_sub, smul_smul]
  simp only [map_sub, map_add, AddMonoidHom.add_apply]
  abel

variable (e)

/-- The cup product on continuous `1`-cocycles. -/
def cupZ (he : ∀ (σ : G) m n, e (σ • m) (σ • n) = σ • e m n) :
    Z1 G M →+ Z1 G N →+ Z2 G P where
  toFun f :=
    { toFun := fun g => ⟨cupFun e f g, cupFun_mem_Z2 he f.2 g.2⟩
      map_zero' := by ext q; simp [cupFun]
      map_add' := fun g g' => Subtype.ext (by
        simp only [AddSubgroup.coe_add]; exact cupFun_add_right e (f : G → M) (g : G → N) (g' : G → N)) }
  map_zero' := by ext g q; simp [cupFun]
  map_add' f f' := by ext g q; simp [cupFun]

theorem coe_cupZ (he : ∀ (σ : G) m n, e (σ • m) (σ • n) = σ • e m n) (f : Z1 G M)
    (g : Z1 G N) : ((cupZ e he f g : Z2 G P) : G × G → P) = cupFun e f g :=
  rfl

theorem H2pi_eq_zero_of_mem_B2 {c : Z2 G P} (hc : (c : G × G → P) ∈ B2 G P) :
    H2pi G P c = 0 := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  exact hc

/-- The cup product with a fixed cocycle, on `H¹(G, N)`. -/
def cupH1 (he : ∀ (σ : G) m n, e (σ • m) (σ • n) = σ • e m n) (f : Z1 G M) :
    H1 G N →+ H2 G P :=
  QuotientAddGroup.lift _ ((H2pi G P).comp (cupZ e he f)) (by
    intro g hg
    rw [AddSubgroup.mem_addSubgroupOf] at hg
    obtain ⟨b, hb⟩ := hg
    refine H2pi_eq_zero_of_mem_B2 ?_
    rw [coe_cupZ]
    rw [← hb, cup_d0_right he f.2 b, mem_B2_iff]
    refine ⟨_, ?_, rfl⟩
    have hfc : Continuous (f : G → M) := ((mem_Z1_iff).1 f.2).1
    have h1 : Continuous fun σ : G => ((f : G → M) σ, σ • b) :=
      hfc.prodMk (continuous_id.smul continuous_const)
    exact ((continuous_uncurry_of_discrete (fun m n => e m n)).comp h1).neg)

/-- **The cup product** `H¹(G, M) →+ H¹(G, N) →+ H²(G, P)` through the equivariant pairing
`e`. -/
def cupH (he : ∀ (σ : G) m n, e (σ • m) (σ • n) = σ • e m n) :
    H1 G M →+ H1 G N →+ H2 G P :=
  QuotientAddGroup.lift _
    { toFun := cupH1 e he
      map_zero' := by
        ext g
        simp [cupH1, map_zero]
      map_add' := fun f f' => by
        ext g
        simp [cupH1, map_add] }
    (by
      intro f hf
      rw [AddSubgroup.mem_addSubgroupOf] at hf
      obtain ⟨a, ha⟩ := hf
      ext g
      refine H2pi_eq_zero_of_mem_B2 ?_
      rw [coe_cupZ]
      rw [← ha, cup_d0_left he a g.2, mem_B2_iff]
      refine ⟨_, ?_, rfl⟩
      exact (continuous_of_discreteTopology (f := fun n : N => e a n)).comp
        ((mem_Z1_iff).1 g.2).1)

/-- The cup product of two cocycle classes is the class of the cup cocycle. -/
theorem cupH_mk (he : ∀ (σ : G) m n, e (σ • m) (σ • n) = σ • e m n) (f : Z1 G M)
    (g : Z1 G N) :
    cupH e he (H1pi G M f) (H1pi G N g) = H2pi G P (cupZ e he f g) :=
  rfl

end Cup

end ZInQ.Contrib.CloudB3RC53.Duality
