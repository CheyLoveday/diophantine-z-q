import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.MackeyCor

/-!
# HeegnerCohomology, part 11b: the Mackey orbit term on `H¹`

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:arith-finite-heegner`, paragraph 7,
tex 3251–3256: "Localizing (H21) separates the cosets into decomposition-group orbits: this is the
local Mackey formula, a sum of the local corestrictions from the transported places."

`MackeyCor.lean` (`MackeyCorNode`) identifies each orbit term with the corestriction cochain of the
transported cochain `b_s(x) = R(s) b(s⁻¹ x s)` up to a coboundary. This file adds the packaging
into a literal equality of classes in `H¹` (all `PROVED`):

* `bTrans_isCocycle`: `b_s` is a `1`-cocycle of `D₀` (with values in `M(θ)`) when `b` is a
  `1`-cocycle of `H`;
* `orbitCochain_mem_Z1`: the orbit term, as a cochain `D → M(θ)`, is a `1`-cocycle;
* `orbitTerm_class_eq_cor`: its class is Tau Ceti's corestriction `explicitCor1Transversal` of the
  class of `b_s`: `[𝒯_O b] = cor_{D₀}^{D} [b_s]` in `H¹(D, M(θ))`;
* `MackeyH1Node` / `mackeyH1Node_proof`: the node.

Tau Ceti's `H¹` is the continuous cohomology of a topological group in a topological module; the
groups here carry no topology in the manuscript's finite setting, so `G` (hence `D`, `D₀`) and
`M(θ)` are given the discrete topology, for which `H¹` is the abstract `H¹` (every cochain is
continuous and every subgroup is open).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

namespace TwistedTransfer

open Finset TauCeti.ContCohomology

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
  {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ)

/-- `M(θ)` carries the discrete topology. -/
instance instTopologicalSpaceTwM : TopologicalSpace (TwM H ρ θ) := ⊥

instance instDiscreteTopologyTwM : DiscreteTopology (TwM H ρ θ) := ⟨rfl⟩

instance instIsTopologicalAddGroupTwM : IsTopologicalAddGroup (TwM H ρ θ) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

variable {D : Subgroup G} {δ₀ : G ⧸ H}

/-- **The transported cochain is a cocycle** (`PROVED`): if `b(xy) = b(x) + ρ(x) b(y)` on `H`, then
`b_s(x) = R(s) b(s⁻¹ x s)` is a `1`-cocycle of `D₀` with values in `M(θ)`, because
`R(s) ρ(s⁻¹ x s) = R(s) R(s⁻¹ x s) = R(x) R(s)` (`s⁻¹ x s ∈ H`). -/
theorem bTrans_isCocycle (s : G) (hs : ((s : G) : G ⧸ H) = δ₀) (b : H → M)
    (hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)) :
    groupCohomology.IsCocycle₁ (bTrans (D := D) H ρ θ s hs b) := by
  intro x y
  apply TwM.ext'
  simp only [bTrans, TwM.val_add]
  rw [show ((x • (⟨R H ρ θ s (b ⟨s⁻¹ * ((y : D) : G) * s, conj_mem_of_stab H s hs y⟩)⟩ :
      TwM H ρ θ)).val) = R H ρ θ ((x : D) : G)
        (R H ρ θ s (b ⟨s⁻¹ * ((y : D) : G) * s, conj_mem_of_stab H s hs y⟩)) from rfl]
  have hsplit : (⟨s⁻¹ * (((x * y : stab H D δ₀) : D) : G) * s, conj_mem_of_stab H s hs (x * y)⟩ :
      H) = ⟨s⁻¹ * ((x : D) : G) * s, conj_mem_of_stab H s hs x⟩ *
        ⟨s⁻¹ * ((y : D) : G) * s, conj_mem_of_stab H s hs y⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group
  rw [hsplit, hb, map_add, add_comm]
  congr 1
  change R H ρ θ s (ρ (s⁻¹ * ((x : D) : G) * s) _) = _
  rw [← R_of_mem H ρ θ (conj_mem_of_stab H s hs x), ← Module.End.mul_apply, ← R_mul,
    ← Module.End.mul_apply, ← R_mul]
  congr 2
  group

variable [TopologicalSpace G] [DiscreteTopology G]

/-- The transported cocycle as an element of `Z¹(D₀, M(θ))`. -/
def bTransZ1 (s : G) (hs : ((s : G) : G ⧸ H) = δ₀) (b : H → M)
    (hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)) : Z1 (stab H D δ₀) (TwM H ρ θ) :=
  ⟨bTrans H ρ θ s hs b, mem_Z1_iff.2 ⟨continuous_of_discreteTopology,
    bTrans_isCocycle H ρ θ s hs b hb⟩⟩

variable (r : G ⧸ H → G) (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ)
  [(stab H D δ₀).FiniteIndex] (t : D ⧸ stab H D δ₀ → D)
  (ht : ∀ u, (QuotientGroup.mk (t u) : D ⧸ stab H D δ₀) = u)

/-- The orbit term over `D δ₀` as a cochain `D → M(θ)`. -/
def orbitCochain [DecidableEq (G ⧸ H)] (b : H → M) : D → TwM H ρ θ :=
  fun d => ⟨orbitTerm H ρ θ r hr (univ.image (phi H t)) b d⟩

instance instContinuousSMulTwM : ContinuousSMul D (TwM H ρ θ) :=
  ⟨continuous_of_discreteTopology⟩

omit [TopologicalSpace G] [DiscreteTopology G] in
/-- The orbit cochain is the corestriction cochain of `b_s` plus a coboundary (a restatement of
`orbitTerm_eq_cor_add_coboundary` as an equality of cochains `D → M(θ)`). -/
theorem orbitCochain_eq [DecidableEq (G ⧸ H)] (s : G) (hs : ((s : G) : G ⧸ H) = δ₀) (b : H → M)
    (hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)) :
    ∃ w : TwM H ρ θ, orbitCochain H ρ θ r hr t b =
      cochainsCor1 D (TwM H ρ θ) (stab H D δ₀) t ht (bTrans H ρ θ s hs b) + d0 D (TwM H ρ θ) w := by
  obtain ⟨w, hw⟩ := orbitTerm_eq_cor_add_coboundary H ρ θ r hr t ht s hs b hb
  refine ⟨⟨w⟩, funext fun d => TwM.ext' ?_⟩
  rw [orbitCochain, hw d, Pi.add_apply, TwM.val_add, d0_apply, TwM.val_sub, Subgroup.smul_def,
    TwM.val_smul]

include ht in
/-- **The orbit cochain is a `1`-cocycle** (`PROVED`). -/
theorem orbitCochain_mem_Z1 [DecidableEq (G ⧸ H)] (s : G) (hs : ((s : G) : G ⧸ H) = δ₀)
    (b : H → M) (hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)) :
    orbitCochain H ρ θ r hr t b ∈ Z1 D (TwM H ρ θ) := by
  obtain ⟨w, hw⟩ := orbitCochain_eq H ρ θ r hr t ht s hs b hb
  rw [hw]
  refine add_mem (cochainsCor1_mem_Z1 D (TwM H ρ θ) (stab H D δ₀) t ht (isOpen_discrete _)
    (bTransZ1 H ρ θ s hs b hb).2) (B1_le_Z1 D (TwM H ρ θ) (d0_mem_B1 w))

/-- **On `H¹`, the orbit term is the corestriction of the transported class** (tex 3251–3256;
`PROVED`): `[𝒯_O b] = cor_{D₀}^{D} [b_s]` in `H¹(D, M(θ))`, with Tau Ceti's degree-one
corestriction `explicitCor1Transversal` along the transversal `t`. -/
theorem orbitTerm_class_eq_cor [DecidableEq (G ⧸ H)] (s : G) (hs : ((s : G) : G ⧸ H) = δ₀)
    (b : H → M) (hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)) :
    ((⟨orbitCochain H ρ θ r hr t b, orbitCochain_mem_Z1 H ρ θ r hr t ht s hs b hb⟩ :
        Z1 D (TwM H ρ θ)) : H1 D (TwM H ρ θ)) =
      explicitCor1Transversal D (TwM H ρ θ) (stab H D δ₀) t ht (isOpen_discrete _)
        ((bTransZ1 H ρ θ s hs b hb : Z1 (stab H D δ₀) (TwM H ρ θ)) :
          H1 (stab H D δ₀) (TwM H ρ θ)) := by
  rw [explicitCor1Transversal_mk, H1pi_eq_iff, coe_cocyclesCor1]
  obtain ⟨w, hw⟩ := orbitCochain_eq H ρ θ r hr t ht s hs b hb
  change orbitCochain H ρ θ r hr t b - _ ∈ _
  have e : ((bTransZ1 H ρ θ s hs b hb : Z1 (stab H D δ₀) (TwM H ρ θ)) :
      stab H D δ₀ → TwM H ρ θ) = bTrans H ρ θ s hs b := rfl
  rw [e, hw, add_sub_cancel_left]
  exact d0_mem_B1 w

end TwistedTransfer

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

open TauCeti.ContCohomology in
/-- **Node: the Mackey orbit terms are local corestrictions on `H¹`**, tex 3251–3256, `PROVED`: in
the setting of `MackeyCorNode` (with the discrete topologies of the finite setting), for a cocycle
`b` of `H`, the transported cochain `b_s` is a cocycle of `D₀`, the orbit term over `D δ₀` is a
cocycle of `D`, and its class in `H¹(D, M(θ))` is the corestriction of the class of `b_s`. -/
def MackeyH1Node : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G] (H : Subgroup G) [H.Normal]
    (r : G ⧸ H → G) (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ) (A M : Type) [CommRing A]
    [AddCommGroup M] [Module A M] (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) (D : Subgroup G)
    (δ₀ : G ⧸ H) [(TwistedTransfer.stab H D δ₀).FiniteIndex] [DecidableEq (G ⧸ H)]
    (t : D ⧸ TwistedTransfer.stab H D δ₀ → D)
    (ht : ∀ u, (QuotientGroup.mk (t u) : D ⧸ TwistedTransfer.stab H D δ₀) = u)
    (s : G) (hs : ((s : G) : G ⧸ H) = δ₀) (b : H → M)
    (hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)),
    groupCohomology.IsCocycle₁ (TwistedTransfer.bTrans (D := D) H ρ θ s hs b) ∧
    ∃ hZ : TwistedTransfer.orbitCochain H ρ θ r hr t b ∈ Z1 D (TwistedTransfer.TwM H ρ θ),
      ((⟨_, hZ⟩ : Z1 D (TwistedTransfer.TwM H ρ θ)) : H1 D (TwistedTransfer.TwM H ρ θ)) =
        explicitCor1Transversal D (TwistedTransfer.TwM H ρ θ) (TwistedTransfer.stab H D δ₀) t ht
          (isOpen_discrete _)
          ((TwistedTransfer.bTransZ1 H ρ θ s hs b hb :
              Z1 (TwistedTransfer.stab H D δ₀) (TwistedTransfer.TwM H ρ θ)) :
            H1 (TwistedTransfer.stab H D δ₀) (TwistedTransfer.TwM H ρ θ))

theorem mackeyH1Node_proof : MackeyH1Node := by
  intro G _ _ _ H _ r hr A M _ _ _ ρ θ D δ₀ _ _ t ht s hs b hb
  exact ⟨TwistedTransfer.bTrans_isCocycle H ρ θ s hs b hb,
    TwistedTransfer.orbitCochain_mem_Z1 H ρ θ r hr t ht s hs b hb,
    TwistedTransfer.orbitTerm_class_eq_cor H ρ θ r hr t ht s hs b hb⟩

end ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

end
