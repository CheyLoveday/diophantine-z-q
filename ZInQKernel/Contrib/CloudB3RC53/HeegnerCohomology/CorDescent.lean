import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.Cartesian
import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.InfRes
import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.Conjugation.Basic

/-!
# HeegnerCohomology, part 12: the descent `d_a` commutes with corestriction (genuine squares)

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:arith-finite-heegner`, paragraph 7,
tex 3281–3288: "For a new conductor prime the class-field squares obtained by retaining the
derivative factors are Cartesian … Restriction and corestriction commute in these squares.  If `b`
lifts `2^e c` in (H9), its corestriction lifts `2^e` times the corresponding corestricted class;
uniqueness after the second multiplication by `2^e` proves the required compatibility of `d_a`."

RC10 proves the last sentence as `FiveTerm.descend_cor` from a hypothesis `hsq`
(`res ∘ cor = corM ∘ res`) on abstract data.  Here the data are constructed for genuine continuous
cohomology and `hsq` is proved (all `PROVED`):

* `G` profinite (for `G_{H_f}`), `U` open of finite index (for `G_{H_{fq}}`), `V` closed normal
  (for `G_{M_I}`) with `G = V U` (the square is Cartesian), `N_U = V ∩ U` inside `U` (for
  `G_{M_I H_{fq}}`), `K = V ∩ U` inside `V`;
* `cor = cor^G_U : H¹(U, M) → H¹(G, M)`;
* `corM : H¹(N_U, M)^{U/N_U} → H¹(V, M)^{G/V}`, the corestriction from `K` to `V` (after the
  identification `K = N_U`); it lands in the invariants because corestriction commutes with
  conjugation (`explicitConj1_explicitCor1`) and inner conjugation is trivial;
* `hsq_genuine`: `res^G_V ∘ cor^G_U = corM ∘ res^U_{N_U}` (single-term Mackey formula,
  `res_cor_cartesian`);
* `descend_cor_genuine`: RC10's `FiveTerm.descend_cor` for these data:
  `d_a(cor c) = cor(d_a c)`.
-/

namespace ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

open TauCeti TauCeti.ContCohomology

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-! ## Corestriction commutes with conjugation -/

section ConjCor

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (V : Subgroup G) [V.Normal] (K : Subgroup V) (u : G)
  (hu : ∀ k : V, k ∈ K ↔ Subgroup.inverseConjugationHom V u k ∈ K)

/-- Conjugation `k ↦ u⁻¹ k u` of `K`. -/
def conjK : K →ₜ* K where
  toFun k := ⟨Subgroup.inverseConjugationHom V u k, (hu k).mp k.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp; group
  continuous_toFun := continuous_induced_rng.2 ((Subgroup.inverseConjugationHom V u).continuous.comp
    continuous_subtype_val)

include hu in
@[simp] theorem conjK_apply (k : K) :
    (((conjK V K u hu k : K) : V) : G) = u⁻¹ * ((k : V) : G) * u := by
  simp [conjK]

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M] in
theorem conjK_smul (k : K) (m : M) :
    DistribSMul.toAddMonoidHom M u (conjK V K u hu k • m) = k • DistribSMul.toAddMonoidHom M u m := by
  simp only [DistribSMul.toAddMonoidHom_apply, Subgroup.smul_def, conjK_apply V K u hu, smul_smul]
  congr 1
  group

/-- The conjugation `(u)_*` on `H¹(K, M)`. -/
noncomputable def conjH1 : H1 K M →+ H1 K M :=
  explicitMap1 K M K M (conjK V K u hu) (DistribSMul.toAddMonoidHom M u)
    ((continuous_const_smul u).congr fun _ => rfl) (conjK_smul V K u hu)

/-- The induced map on cosets `w ↦ u⁻¹ w u`. -/
noncomputable def sigma (w : V ⧸ K) : V ⧸ K :=
  QuotientGroup.mk (Subgroup.inverseConjugationHom V u w.out)

include hu in
theorem sigma_mk (x : V) :
    sigma V K u (QuotientGroup.mk x) = QuotientGroup.mk (Subgroup.inverseConjugationHom V u x) := by
  unfold sigma
  rw [QuotientGroup.eq]
  have h : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk x : V ⧸ K)) : V ⧸ K) =
      QuotientGroup.mk x := Quotient.out_eq _
  rw [QuotientGroup.eq] at h
  rw [hu] at h
  convert h using 1
  apply Subtype.ext
  simp [mul_assoc]

include hu in
theorem sigma_smul (v : V) (w : V ⧸ K) :
    sigma V K u (v • w) = (Subgroup.inverseConjugationHom V u v) • sigma V K u w := by
  induction w using QuotientGroup.induction_on with
  | H x =>
    rw [MulAction.Quotient.smul_mk, sigma_mk V K u hu, sigma_mk V K u hu, MulAction.Quotient.smul_mk,
      smul_eq_mul, smul_eq_mul, map_mul]

include hu in
theorem hu_inv (k : V) : k ∈ K ↔ Subgroup.inverseConjugationHom V u⁻¹ k ∈ K := by
  have h := hu (Subgroup.inverseConjugationHom V u⁻¹ k)
  have e : Subgroup.inverseConjugationHom V u (Subgroup.inverseConjugationHom V u⁻¹ k) = k := by
    ext; simp; group
  rw [e] at h
  exact h.symm

/-- `σ` as a permutation of `V ⧸ K`. -/
noncomputable def sigmaEquiv : V ⧸ K ≃ V ⧸ K where
  toFun := sigma V K u
  invFun := sigma V K u⁻¹
  left_inv w := by
    induction w using QuotientGroup.induction_on with
    | H x =>
      rw [sigma_mk V K u hu, sigma_mk V K u⁻¹ (hu_inv V K u hu)]
      congr 1; ext; simp; group
  right_inv w := by
    induction w using QuotientGroup.induction_on with
    | H x =>
      rw [sigma_mk V K u⁻¹ (hu_inv V K u hu), sigma_mk V K u hu]
      congr 1; ext; simp; group

variable [K.FiniteIndex] (t : V ⧸ K → V) (ht : ∀ w, (QuotientGroup.mk (t w) : V ⧸ K) = w)

/-- The conjugated transversal `t'(w) = u t(σ w) u⁻¹`. -/
noncomputable def tConj (w : V ⧸ K) : V := Subgroup.inverseConjugationHom V u⁻¹ (t (sigma V K u w))

include hu ht in
theorem tConj_mk (w : V ⧸ K) : (QuotientGroup.mk (tConj V K u t w) : V ⧸ K) = w := by
  unfold tConj
  rw [← sigma_mk V K u⁻¹ (hu_inv V K u hu), ht]
  exact (sigmaEquiv V K u hu).left_inv w

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M] in
include ht in
/-- **The cochain identity**: `cor_{t'}((u)_* c) = (u)_* cor_t c`. -/
theorem cochainsCor1_conj (c : K → M) (v : V) :
    cochainsCor1 V M K (tConj V K u t) (tConj_mk V K u hu t ht)
        (fun k => u • c (conjK V K u hu k)) v =
      u • cochainsCor1 V M K t ht c (Subgroup.inverseConjugationHom V u v) := by
  simp only [cochainsCor1_apply]
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (sigmaEquiv V K u hu) _ _ (fun w => ?_)
  simp only [sigmaEquiv, Equiv.coe_fn_mk]
  have harg : conjK V K u hu ⟨lWord K (tConj V K u t) w v, lWord_mem K _ (tConj_mk V K u hu t ht) w v⟩
      = ⟨lWord K t (sigma V K u w) (Subgroup.inverseConjugationHom V u v),
          lWord_mem K t ht _ _⟩ := by
    apply Subtype.ext; apply Subtype.ext
    rw [conjK_apply V K u hu]
    simp only [lWord_def, tConj, sigma_smul V K u hu, map_inv, Subgroup.coe_mul,
      InvMemClass.coe_inv, Subgroup.inverseConjugationHom_apply]
    group
  rw [harg, Subgroup.smul_def, Subgroup.smul_def, smul_smul, smul_smul]
  congr 1
  simp only [tConj, Subgroup.inverseConjugationHom_apply]
  group

/-- **Corestriction commutes with conjugation** on `H¹`: `(u)_* ∘ cor^V_K = cor^V_K ∘ (u)_*`. -/
theorem explicitConj1_explicitCor1 (hK : IsOpen (K : Set V)) (y : H1 K M) :
    explicitConj1 V u (explicitCor1 V M K hK y) = explicitCor1 V M K hK (conjH1 V K u hu y) := by
  induction y using QuotientAddGroup.induction_on with
  | H c =>
    conv_lhs => rw [explicitCor1_eq_transversal V M K Quotient.out Quotient.out_eq hK,
      explicitCor1Transversal_mk]
    conv_rhs => rw [conjH1, explicitMap1_mk,
      explicitCor1_eq_transversal V M K (tConj V K u Quotient.out)
        (tConj_mk V K u hu Quotient.out Quotient.out_eq) hK, explicitCor1Transversal_mk]
    rw [explicitConj1_apply_eq_smul, smul_mk]
    congr 1
    apply Subtype.ext
    funext v
    rw [cocyclesMap1_apply, coe_cocyclesCor1, coe_cocyclesCor1]
    exact (cochainsCor1_conj V K u hu Quotient.out Quotient.out_eq (c : K → M) v).symm

end ConjCor

/-! ## The Cartesian square -/

section Square

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type*) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G)) (V : Subgroup G) [V.Normal]

/-- `K = V ∩ U` inside `V` (the Mackey subgroup at `s = 1`). -/
abbrev Kmk : Subgroup V := (mackeySubgroup 1 U V).subgroupOf V

/-- `N_U = V ∩ U` inside `U`. -/
abbrev NU : Subgroup U := V.subgroupOf U

theorem mem_Kmk (k : V) : k ∈ Kmk G U V ↔ (k : G) ∈ U := by
  simp [Kmk, Subgroup.mem_subgroupOf, mem_mackeySubgroup_iff]

/-- The identification `K → N_U` of the two copies of `V ∩ U`. -/
def phiKN : Kmk G U V →ₜ* NU G U V where
  toFun k := ⟨⟨((k : V) : G), (mem_Kmk G U V k).mp k.2⟩, Subgroup.mem_subgroupOf.mpr (k : V).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem phiKN_coe (k : Kmk G U V) : (((phiKN G U V k : NU G U V) : U) : G) = ((k : V) : G) :=
  rfl

theorem phiKN_smul (k : Kmk G U V) (m : M) :
    AddMonoidHom.id M (phiKN G U V k • m) = k • AddMonoidHom.id M m := by
  simp only [AddMonoidHom.id_apply, Subgroup.smul_def]
  rfl

/-- `corM₀ : H¹(N_U, M) → H¹(V, M)`: identify `N_U = K` and corestrict from `K` to `V`. -/
noncomputable def corMbase : H1 (NU G U V) M →+ H1 V M :=
  (explicitCor1 V M (Kmk G U V) (U.isOpen_mackeySubgroup_subgroupOf V hU 1)).comp
    (explicitMap1 (NU G U V) M (Kmk G U V) M (phiKN G U V) (AddMonoidHom.id M) continuous_id
      (phiKN_smul G M U V))

/-- **`res^G_V ∘ cor^G_U = corM₀ ∘ res^U_{N_U}`** in a Cartesian square (tex 3283–3284),
`PROVED`. -/
theorem hsq_base (hVU : ∀ g : G, ∃ v ∈ V, ∃ u ∈ U, g = v * u) (b : H1 U M) :
    explicitRes1 G M V (explicitCor1 G M U hU b) =
      corMbase G M U hU V (explicitRes1 U M (NU G U V) b) := by
  rw [res_cor_cartesian G M U V hU hVU b, explicitMackeyTerm1, corMbase, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, explicitRes1_eq_explicitMap1]
  congr 1
  refine (DFunLike.congr_fun (explicitMap1_congr_of_eq U M (Kmk G U V) M
    (U.continuousMackeyToH V 1)
    ((ContinuousMonoidHom.subgroupSubtype (NU G U V)).comp (phiKN G U V))
    (DistribSMul.toAddMonoidHom M 1)
    ((AddMonoidHom.id M).comp (AddMonoidHom.id M)) (hq := continuous_id.comp continuous_id)
    (hψ := ContinuousMonoidHom.comp_map_smul _ _ _ _
      (ContinuousMonoidHom.id_subgroupSubtype_smul M (NU G U V)) (phiKN_smul G M U V))
    (by ext k; simp [coe_mackeyToH_apply, phiKN_coe]) (by ext m; simp)) b).trans ?_
  exact DFunLike.congr_fun (explicitMap1_comp U M (NU G U V) M _ (AddMonoidHom.id M) continuous_id
    (ContinuousMonoidHom.id_subgroupSubtype_smul M (NU G U V)) (Kmk G U V) M (phiKN G U V)
    (AddMonoidHom.id M) continuous_id (phiKN_smul G M U V)) b

/-- `u ∈ U` normalizes `K = V ∩ U`. -/
theorem hu_K (u : G) (hu : u ∈ U) (k : V) :
    k ∈ Kmk G U V ↔ Subgroup.inverseConjugationHom V u k ∈ Kmk G U V := by
  rw [mem_Kmk, mem_Kmk, Subgroup.inverseConjugationHom_apply]
  constructor
  · intro hk; exact U.mul_mem (U.mul_mem (U.inv_mem hu) hk) hu
  · intro hk
    have := U.mul_mem (U.mul_mem hu hk) (U.inv_mem hu)
    simpa [mul_assoc] using this

variable [CompactSpace G] [TotallyDisconnectedSpace G] [DiscreteTopology M]

/-- **`corM₀` lands in the invariants** (`G/V`-invariant classes) when applied to `U/N_U`-invariant
classes, `PROVED`: write `g = v u`; `v ∈ V` acts trivially (inner), and `u ∈ U` commutes with the
corestriction (`explicitConj1_explicitCor1`) and with the identification `N_U = K`. -/
theorem corMbase_mem (hVU : ∀ g : G, ∃ v ∈ V, ∃ u ∈ U, g = v * u)
    (x : H1ConjInvariants U M (NU G U V)) :
    corMbase G M U hU V x ∈ H1ConjInvariants G M V := by
  intro g
  obtain ⟨v, hv, w, hw, rfl⟩ := hVU g
  rw [explicitConj1_mul, AddMonoidHom.comp_apply]
  have hw' : explicitConj1 V w (corMbase G M U hU V x) = corMbase G M U hU V x := by
    rw [corMbase, AddMonoidHom.comp_apply,
      explicitConj1_explicitCor1 V (Kmk G U V) w (hu_K G U V w hw)]
    congr 1
    have hx := x.2 ⟨w, hw⟩
    rw [conjH1]
    rw [explicitMap1_explicitMap1_of_comp_eq (NU G U V) M (Kmk G U V) M (phiKN G U V)
      (AddMonoidHom.id M) continuous_id (phiKN_smul G M U V) (Kmk G U V) M
      (conjK V (Kmk G U V) w (hu_K G U V w hw)) (DistribSMul.toAddMonoidHom M w)
      ((continuous_const_smul w).congr fun _ => rfl) (conjK_smul V (Kmk G U V) w _)
      (Subgroup.inverseConjugationHom (NU G U V) ⟨w, hw⟩)
      (DistribSMul.toAddMonoidHom M (⟨w, hw⟩ : U))
      ((continuous_const_smul (⟨w, hw⟩ : U)).congr fun _ => rfl)
      (Subgroup.inverseConjugationHom_smul (NU G U V) ⟨w, hw⟩)
      (phiKN G U V) (AddMonoidHom.id M) continuous_id (phiKN_smul G M U V)
      (by
        ext k
        show ((phiKN G U V (conjK V (Kmk G U V) w (hu_K G U V w hw) k) : U) : G) =
          ((Subgroup.inverseConjugationHom (NU G U V) ⟨w, hw⟩ (phiKN G U V k) : U) : G)
        rw [phiKN_coe, conjK_apply, Subgroup.inverseConjugationHom_apply]
        rfl)
      (by ext m; rfl)]
    rw [show explicitMap1 (NU G U V) M (NU G U V) M
        (Subgroup.inverseConjugationHom (NU G U V) ⟨w, hw⟩)
        (DistribSMul.toAddMonoidHom M (⟨w, hw⟩ : U)) _ _ x = explicitConj1 (NU G U V) ⟨w, hw⟩ x
      from rfl, hx]
  rw [hw', explicitConj1_eq_id_of_mem V ⟨v, hv⟩]
  rfl

/-- `corM : H¹(N_U, M)^{U/N_U} → H¹(V, M)^{G/V}`. -/
noncomputable def corM (hVU : ∀ g : G, ∃ v ∈ V, ∃ u ∈ U, g = v * u) :
    H1ConjInvariants U M (NU G U V) →+ H1ConjInvariants G M V :=
  AddMonoidHom.codRestrict ((corMbase G M U hU V).comp (H1ConjInvariants U M (NU G U V)).subtype)
    (H1ConjInvariants G M V) (corMbase_mem G M U hU V hVU)

/-- **The hypothesis `hsq` of RC10's `FiveTerm.descend_cor`, genuine** (tex 3281–3288), `PROVED`:
for the five-term sequences of `(U, N_U)` and `(G, V)`, `res ∘ cor^G_U = corM ∘ res`. -/
theorem hsq_genuine (hVU : ∀ g : G, ∃ v ∈ V, ∃ u ∈ U, g = v * u) (b : H1 U M) :
    explicitResConj1 G M V (explicitCor1 G M U hU b) =
      corM G M U hU V hVU (explicitResConj1 U M (NU G U V) b) := by
  apply Subtype.ext
  rw [coe_explicitResConj1, hsq_base G M U hU V hVU b]
  rfl

include hU in
/-- An open subgroup of a compact group is compact (so `U` is profinite with `G`). -/
theorem compactSpace_of_isOpen : CompactSpace U :=
  isCompact_iff_compactSpace.mp (U.isClosed_of_isOpen hU).isCompact

/-- `N_U` is closed in `U` when `V` is closed in `G`. -/
theorem isClosed_NU (hV : IsClosed (V : Set G)) : IsClosed ((NU G U V : Subgroup U) : Set U) :=
  hV.preimage continuous_subtype_val

/-- **The compatibility of `d_a` with corestriction, genuine** (tex 3281–3288), `PROVED`: RC10's
`FiveTerm.descend_cor` applied to the genuine five-term sequences of `(U, N_U)` and `(G, V)`, with
`cor = cor^G_U` and `corM` the corestriction on invariants, the hypothesis `hsq` being
`hsq_genuine`.  For `c ∈ H¹(N_U, M)^{U/N_U}`: `d_a(corM c) = cor^G_U(d_a c)`, where `d_a` is
(H9) with the vanishing `2^e M^{N_U} = 0`, `2^e M^V = 0` from (H2). -/
theorem descend_cor_genuine [CompactSpace U] (hV : IsClosed (V : Set G))
    (hVU : ∀ g : G, ∃ v ∈ V, ∃ u ∈ U, g = v * u) (e : ℕ)
    (hH2U : ∀ m : M, (∀ n : NU G U V, n • m = m) → ((2 : ℤ) ^ e) • m = 0)
    (hH2G : ∀ m : M, (∀ n : V, n • m = m) → ((2 : ℤ) ^ e) • m = 0)
    (c : H1ConjInvariants U M (NU G U V)) :
    (fiveTermGenuine G M V hV).descend e (infResInputGenuine G M V hV e hH2G).killD
        (corM G M U hU V hVU c) =
      explicitCor1 G M U hU ((fiveTermGenuine U M (NU G U V) (isClosed_NU G U V hV)).descend e
        (infResInputGenuine U M (NU G U V) (isClosed_NU G U V hV) e hH2U).killD c) :=
  ZInQ.Manuscript.RC.HeegnerAlgebra.FiveTerm.descend_cor
    (fiveTermGenuine U M (NU G U V) (isClosed_NU G U V hV)) e (fiveTermGenuine G M V hV)
    (infResInputGenuine G M V hV e hH2G).killA
    (infResInputGenuine U M (NU G U V) (isClosed_NU G U V hV) e hH2U).killD
    (infResInputGenuine G M V hV e hH2G).killD
    (explicitCor1 G M U hU) (corM G M U hU V hVU) (hsq_genuine G M U hU V hVU) c

end Square

end ZInQ.Contrib.CloudB3RC53.HeegnerCohomology
