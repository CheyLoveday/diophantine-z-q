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

Tau Ceti's `H¹` is the continuous cohomology of a topological group in a topological module, and
it is used here with the genuine topologies: in the manuscript `G = G_K` and the decomposition
group `D` are profinite (only the coset quotient `G/H ≅ Gal(H_f/K)` is finite). So `G` is any
topological group, `D` and `D₀` carry the subspace topologies, `M(θ)` carries the topology of
`M` (`TwM.val` is a homeomorphism onto `M`), and the hypotheses are:

* `[ContinuousSMul G M(θ)]` — the twisted action `(g, m) ↦ θ(ḡ) ρ(g) m` is continuous
  (`continuousSMul_twM_of`, `PROVED`, derives it from `H` open, a continuous action `ρ` and
  continuous scalars);
* `Continuous b` — the cocycle of `H` is continuous;
* `IsOpen H` — `H` is open in `G` (`H = G_{H_f}`, of finite index); then `D₀ = D ∩ H` is open in
  `D` (`isOpen_stab`, `PROVED`), which is the openness used by `explicitCor1Transversal`.

The transported cochain `b_s = s • b(s⁻¹ · s)` is continuous (`continuous_bTrans`, `PROVED`), and
the orbit cochain is continuous because it is the corestriction cochain of `b_s` (a finite sum over
`D/D₀` of continuous maps, Tau Ceti's `continuous_cochainsCor1`) plus a coboundary.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

namespace TwistedTransfer

open Finset TauCeti.ContCohomology

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
  {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ)

section Topology

variable [TopologicalSpace M]

/-- `M(θ)` carries the topology of `M`. -/
instance instTopologicalSpaceTwM : TopologicalSpace (TwM H ρ θ) :=
  TopologicalSpace.induced TwM.val ‹_›

theorem continuous_val : Continuous (TwM.val : TwM H ρ θ → M) := continuous_induced_dom

theorem continuous_mk : Continuous (TwM.mk : M → TwM H ρ θ) :=
  continuous_induced_rng.2 continuous_id

instance instIsTopologicalAddGroupTwM [IsTopologicalAddGroup M] :
    IsTopologicalAddGroup (TwM H ρ θ) where
  continuous_add := continuous_induced_rng.2
    (((continuous_val H ρ θ).comp continuous_fst).add ((continuous_val H ρ θ).comp continuous_snd))
  continuous_neg := continuous_induced_rng.2 ((continuous_val H ρ θ).neg)

end Topology

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

/-- `D₀` is `D ∩ H`: `x δ₀ = δ₀` in `G/H` exactly when `x ∈ H`. -/
theorem mem_stab_iff (x : D) : x ∈ stab H D δ₀ ↔ (x : G) ∈ H := by
  change ((x : G) : G ⧸ H) * δ₀ = δ₀ ↔ _
  rw [mul_eq_right, QuotientGroup.eq_one_iff]

variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- **`D₀` is open in `D` when `H` is open in `G`** (`PROVED`). -/
theorem isOpen_stab (hH : IsOpen (H : Set G)) : IsOpen ((stab H D δ₀ : Subgroup D) : Set D) := by
  have : ((stab H D δ₀ : Subgroup D) : Set D) = Subtype.val ⁻¹' (H : Set G) := by
    ext x; exact mem_stab_iff H x
  rw [this]
  exact hH.preimage continuous_subtype_val

variable [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G (TwM H ρ θ)]

omit [IsTopologicalAddGroup M] [ContinuousSMul G (TwM H ρ θ)] in
/-- **The twisted action is continuous** (`PROVED`) when `H` is open (so `g ↦ θ(ḡ)` is locally
constant), the action `ρ` is jointly continuous, and scalars act continuously. -/
theorem continuousSMul_twM_of (hH : IsOpen (H : Set G))
    (hρ : Continuous fun p : G × M => ρ p.1 p.2) (hsc : ∀ a : A, Continuous fun m : M => a • m) :
    ContinuousSMul G (TwM H ρ θ) := by
  refine ⟨continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun p₀ => ?_)⟩
  have hcont : Continuous fun p : G × TwM H ρ θ =>
      ((θ ((p₀.1 : G) : G ⧸ H) : A)) • ρ p.1 p.2.val :=
    (hsc _).comp (hρ.comp (continuous_fst.prodMk ((continuous_val H ρ θ).comp continuous_snd)))
  have hopen : IsOpen {p : G × TwM H ρ θ | p₀.1⁻¹ * p.1 ∈ H} :=
    hH.preimage (continuous_const.mul continuous_fst)
  refine hcont.continuousAt.congr (Filter.eventuallyEq_of_mem (hopen.mem_nhds (by simp)) ?_)
  intro p hp
  have hq : ((p.1 : G) : G ⧸ H) = ((p₀.1 : G) : G ⧸ H) := (QuotientGroup.eq.2 hp).symm
  change _ = (R H ρ θ p.1) p.2.val
  rw [R, hq]
  rfl

omit [IsTopologicalAddGroup M] in
/-- **The transported cochain is continuous** (`PROVED`): `b_s(x) = s • b(s⁻¹ x s)`, a composition
of continuous maps when `b` is continuous on `H`. -/
theorem continuous_bTrans (s : G) (hs : ((s : G) : G ⧸ H) = δ₀) (b : H → M) (hbc : Continuous b) :
    Continuous (bTrans (D := D) H ρ θ s hs b) := by
  have hconj : Continuous fun x : stab H D δ₀ => s⁻¹ * ((x : D) : G) * s :=
    (continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)).mul
      continuous_const
  have hin : Continuous fun x : stab H D δ₀ =>
      (⟨s⁻¹ * ((x : D) : G) * s, conj_mem_of_stab H s hs x⟩ : H) :=
    hconj.subtype_mk _
  have h := (continuous_const_smul s).comp ((continuous_mk H ρ θ).comp (hbc.comp hin))
  exact h

/-- The transported cocycle as an element of `Z¹(D₀, M(θ))`. -/
def bTransZ1 (s : G) (hs : ((s : G) : G ⧸ H) = δ₀) (b : H → M) (hbc : Continuous b)
    (hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)) : Z1 (stab H D δ₀) (TwM H ρ θ) :=
  ⟨bTrans H ρ θ s hs b, mem_Z1_iff.2 ⟨continuous_bTrans H ρ θ s hs b hbc,
    bTrans_isCocycle H ρ θ s hs b hb⟩⟩

variable (r : G ⧸ H → G) (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ)
  [(stab H D δ₀).FiniteIndex] (t : D ⧸ stab H D δ₀ → D)
  (ht : ∀ u, (QuotientGroup.mk (t u) : D ⧸ stab H D δ₀) = u)

/-- The orbit term over `D δ₀` as a cochain `D → M(θ)`. -/
def orbitCochain [DecidableEq (G ⧸ H)] (b : H → M) : D → TwM H ρ θ :=
  fun d => ⟨orbitTerm H ρ θ r hr (univ.image (phi H t)) b d⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousSMul G (TwM H ρ θ)] in
/-- The orbit cochain is the corestriction cochain of `b_s` plus a coboundary (a restatement of
`orbitTerm_eq_cor_add_coboundary` as an equality of cochains `D → M(θ)`). -/
theorem orbitCochain_eq [DecidableEq (G ⧸ H)] (s : G) (hs : ((s : G) : G ⧸ H) = δ₀) (b : H → M)
    (hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)) :
    ∃ w : TwM H ρ θ, orbitCochain H ρ θ r hr t b =
      cochainsCor1 D (TwM H ρ θ) (stab H D δ₀) t ht (bTrans H ρ θ s hs b) + d0 D (TwM H ρ θ) w := by
  obtain ⟨w, -, hw⟩ := orbitTerm_eq_cor_add_coboundary H ρ θ r hr t ht s hs b hb
  refine ⟨⟨w⟩, funext fun d => TwM.ext' ?_⟩
  rw [orbitCochain, hw d, Pi.add_apply, TwM.val_add, d0_apply, TwM.val_sub, Subgroup.smul_def,
    TwM.val_smul]

include ht in
/-- **The orbit cochain is a continuous `1`-cocycle** (`PROVED`): the corestriction cochain of the
continuous cocycle `b_s` (continuous since `D₀` is open of finite index in `D`) plus a coboundary. -/
theorem orbitCochain_mem_Z1 [DecidableEq (G ⧸ H)] (hH : IsOpen (H : Set G)) (s : G)
    (hs : ((s : G) : G ⧸ H) = δ₀) (b : H → M) (hbc : Continuous b)
    (hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)) :
    orbitCochain H ρ θ r hr t b ∈ Z1 D (TwM H ρ θ) := by
  obtain ⟨w, hw⟩ := orbitCochain_eq H ρ θ r hr t ht s hs b hb
  rw [hw]
  exact add_mem (cochainsCor1_mem_Z1 D (TwM H ρ θ) (stab H D δ₀) t ht (isOpen_stab H hH)
    (bTransZ1 H ρ θ s hs b hbc hb).2) (B1_le_Z1 D (TwM H ρ θ) (d0_mem_B1 w))

/-- **On `H¹`, the orbit term is the corestriction of the transported class** (tex 3251–3256;
`PROVED`): `[𝒯_O b] = cor_{D₀}^{D} [b_s]` in the continuous `H¹(D, M(θ))`, with Tau Ceti's
degree-one corestriction `explicitCor1Transversal` along the transversal `t` (for the open
subgroup `D₀` of finite index). -/
theorem orbitTerm_class_eq_cor [DecidableEq (G ⧸ H)] (hH : IsOpen (H : Set G)) (s : G)
    (hs : ((s : G) : G ⧸ H) = δ₀) (b : H → M) (hbc : Continuous b)
    (hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)) :
    ((⟨orbitCochain H ρ θ r hr t b, orbitCochain_mem_Z1 H ρ θ r hr t ht hH s hs b hbc hb⟩ :
        Z1 D (TwM H ρ θ)) : H1 D (TwM H ρ θ)) =
      explicitCor1Transversal D (TwM H ρ θ) (stab H D δ₀) t ht (isOpen_stab H hH)
        ((bTransZ1 H ρ θ s hs b hbc hb : Z1 (stab H D δ₀) (TwM H ρ θ)) :
          H1 (stab H D δ₀) (TwM H ρ θ)) := by
  rw [explicitCor1Transversal_mk, H1pi_eq_iff, coe_cocyclesCor1]
  obtain ⟨w, hw⟩ := orbitCochain_eq H ρ θ r hr t ht s hs b hb
  change orbitCochain H ρ θ r hr t b - _ ∈ _
  have e : ((bTransZ1 H ρ θ s hs b hbc hb : Z1 (stab H D δ₀) (TwM H ρ θ)) :
      stab H D δ₀ → TwM H ρ θ) = bTrans H ρ θ s hs b := rfl
  rw [e, hw, add_sub_cancel_left]
  exact d0_mem_B1 w

end TwistedTransfer

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

open TauCeti.ContCohomology in
/-- **Node: the Mackey orbit terms are local corestrictions on the continuous `H¹`**, tex
3251–3256, `PROVED`: in the setting of `MackeyCorNode`, for a topological group `G` (profinite in
the manuscript) with `H` open, a topological module `M` with continuous twisted action, and a
continuous cocycle `b` of `H`, the transported cochain `b_s` is a continuous cocycle of `D₀`, the
orbit term over `D δ₀` is a continuous cocycle of `D`, and its class in `H¹(D, M(θ))` is the
corestriction of the class of `b_s`. -/
def MackeyH1Node : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) [H.Normal]
    (hH : IsOpen (H : Set G))
    (r : G ⧸ H → G) (hr : ∀ δ, ((r δ : G) : G ⧸ H) = δ) (A M : Type) [CommRing A]
    [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    (ρ : G →* Module.End A M) (θ : G ⧸ H →* Aˣ) [ContinuousSMul G (TwistedTransfer.TwM H ρ θ)]
    (D : Subgroup G)
    (δ₀ : G ⧸ H) [(TwistedTransfer.stab H D δ₀).FiniteIndex] [DecidableEq (G ⧸ H)]
    (t : D ⧸ TwistedTransfer.stab H D δ₀ → D)
    (ht : ∀ u, (QuotientGroup.mk (t u) : D ⧸ TwistedTransfer.stab H D δ₀) = u)
    (s : G) (hs : ((s : G) : G ⧸ H) = δ₀) (b : H → M) (hbc : Continuous b)
    (hb : ∀ x y : H, b (x * y) = b x + ρ x (b y)),
    TwistedTransfer.bTrans (D := D) H ρ θ s hs b ∈
        Z1 (TwistedTransfer.stab H D δ₀) (TwistedTransfer.TwM H ρ θ) ∧
    ∃ hZ : TwistedTransfer.orbitCochain H ρ θ r hr t b ∈ Z1 D (TwistedTransfer.TwM H ρ θ),
      ((⟨_, hZ⟩ : Z1 D (TwistedTransfer.TwM H ρ θ)) : H1 D (TwistedTransfer.TwM H ρ θ)) =
        explicitCor1Transversal D (TwistedTransfer.TwM H ρ θ) (TwistedTransfer.stab H D δ₀) t ht
          (TwistedTransfer.isOpen_stab H hH)
          ((TwistedTransfer.bTransZ1 H ρ θ s hs b hbc hb :
              Z1 (TwistedTransfer.stab H D δ₀) (TwistedTransfer.TwM H ρ θ)) :
            H1 (TwistedTransfer.stab H D δ₀) (TwistedTransfer.TwM H ρ θ))

theorem mackeyH1Node_proof : MackeyH1Node := by
  intro G _ _ _ H _ hH r hr A M _ _ _ _ _ ρ θ _ D δ₀ _ _ t ht s hs b hbc hb
  exact ⟨(TwistedTransfer.bTransZ1 H ρ θ s hs b hbc hb).2,
    TwistedTransfer.orbitCochain_mem_Z1 H ρ θ r hr t ht hH s hs b hbc hb,
    TwistedTransfer.orbitTerm_class_eq_cor H ρ θ r hr t ht hH s hs b hbc hb⟩

end ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

end
