import ZInQKernel.Contrib.OneProof.RC.Wiring.KummerCompArith

/-!
# Theorem 5.3, Lane RC37: non-vacuity of the Kummer comparison inputs

Non-vacuity instances for the hypothesis structures of the lane (manuscript tex 4005–4014).

* `KcLevelData`: inhabited by the arithmetic datum `kcArithLevelData` (PROVED from the bridge
  for every `k`, `S`, `E` with full two-power torsion over `K_S`).
* `KcSelmerSupport D L`: for **every** level datum `D` it holds for the subgroup
  `kcImage D` of classes of inflations of locally trivial level cocycles
  (`kcSelmerSupport_image`, PROVED; the levels are raised along `kcRaise` to add classes). So the
  construction `kcPhi` gives, with no input at all, a quasi-isomorphism
  `τ_{≤1}(C_K ⊗ ℚ₂/ℤ₂) → C_disc(kcImage D)` (`kcPhi_quasiIso_image`); the GLUE
  `KcArithSelmerLevel` is exactly what identifies `kcImage` with the Selmer group.
* `KcArithSelmerLevel` (GLUE): its premises are inhabited (the zero cocycle is a locally
  trivial cocycle, `kcLocTriv_zero`), and both fields hold at level `2^0`, unconditionally
  (`kcArithSelmerLevel_sel_zero`, `kcArithSelmerLevel_loc_zero`, PROVED: `E[1] = 0`).

Kinds: definitions and PROVED.
-/

noncomputable section

set_option maxHeartbeats 1600000

namespace ZInQ.Manuscript.RC

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ZInQ.Manuscript.RC53Assist.CentralUniversal ZInQ.Manuscript.RC53Assist.QuadraticDescent
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.LambdaCoef ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Contrib.RC53Assist.DiskOrders.Limit ZInQ.Contrib.RC53Assist.Finiteness
open TauCeti TauCeti.ContCohomology

attribute [local instance] levTop continuousSMul_lev

/-! ### Raising levels -/

section Raise

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K}

/-- The inclusion `E(K_S)[2^m] ⊂ E(K_S)[2^M]`, `m ≤ M`. Kind: definition. -/
def kcLevIncl (m M : ℕ) (h : m ≤ M) : Lev K S W m →+ Lev K S W M where
  toFun P := ⟨P, (mem_lev_iff _).2 (by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [pow_add, mul_comm, mul_smul, two_pow_nsmul_lev P, smul_zero])⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coe_kcLevIncl (m M : ℕ) (h : m ≤ M) (P : Lev K S W m) :
    ((kcLevIncl m M h P : Lev K S W M) : Pt K S W) = P :=
  rfl

/-- The inclusion is equivariant. Kind: PROVED. -/
theorem kcLevIncl_smul (m M : ℕ) (h : m ≤ M) (g : GKS K S) (P : Lev K S W m) :
    kcLevIncl m M h (g • P) = g • kcLevIncl m M h P :=
  Subtype.ext (by rw [coe_kcLevIncl, smul_lev_coe, smul_lev_coe, coe_kcLevIncl])

/-- **Raising the level of cochains** along `E(K_S)[2^m] ⊂ E(K_S)[2^M]`. Kind: definition. -/
def kcRaise (m M : ℕ) (h : m ≤ M) :
    contCochains ℤ (GKS K S) (Lev K S W m) ⟶ contCochains ℤ (GKS K S) (Lev K S W M) :=
  contCochainsMap (ContinuousMonoidHom.id (GKS K S)) (kcLevIncl m M h).toIntLinearMap
    continuous_of_discreteTopology (fun g P => kcLevIncl_smul m M h g P)

/-- Raising preserves cocycles. Kind: PROVED. -/
theorem kcRaise_d (m M : ℕ) (h : m ≤ M) (f : (contCochains ℤ (GKS K S) (Lev K S W m)).X 1)
    (hf : ((contCochains ℤ (GKS K S) (Lev K S W m)).d 1 2).hom f = 0) :
    ((contCochains ℤ (GKS K S) (Lev K S W M)).d 1 2).hom (((kcRaise m M h).f 1).hom f) = 0 := by
  have e := congrArg (fun g => g.hom f) ((kcRaise (S := S) (W := W) m M h).comm 1 2)
  change ((contCochains ℤ (GKS K S) (Lev K S W M)).d 1 2).hom (((kcRaise m M h).f 1).hom f) =
    ((kcRaise m M h).f 2).hom (((contCochains ℤ (GKS K S) (Lev K S W m)).d 1 2).hom f) at e
  rw [e, hf, map_zero]

/-- Raising preserves local triviality. Kind: PROVED. -/
theorem kcRaise_locTriv (m M : ℕ) (h : m ≤ M) {f : (contCochains ℤ (GKS K S) (Lev K S W m)).X 1}
    (hl : KcLocTriv W f) : KcLocTriv W (((kcRaise m M h).f 1).hom f) := by
  intro v
  obtain ⟨R, hR⟩ := hl v
  exact ⟨R, fun σ => hR σ⟩

variable {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  {M' : Type} [AddCommGroup M'] [DistribMulAction G' M'] [TopologicalSpace M']
  [DiscreteTopology M'] [ContinuousSMul G' M']
  (D : KcLevelData S W G' M')

/-- Raising does not change the inflation. Kind: PROVED. -/
theorem kcInflate_raise (m M : ℕ) (h : m ≤ M) (f : (contCochains ℤ (GKS K S) (Lev K S W m)).X 1) :
    ((kcInflate D M).f 1).hom (((kcRaise m M h).f 1).hom f) = ((kcInflate D m).f 1).hom f := by
  apply cochain_ext
  intro x
  exact D.J_compat M m _ _ rfl

/-- Equal cocycles have equal classes. Kind: PROVED. -/
theorem kc_kerToH1_congr {x y : (contCochains ℤ G' M').X 1}
    (hx : x ∈ LinearMap.ker ((contCochains ℤ G' M').d 1 2).hom)
    (hy : y ∈ LinearMap.ker ((contCochains ℤ G' M').d 1 2).hom) (h : x = y) :
    kerToH1 (k := ℤ) ⟨x, hx⟩ = kerToH1 (k := ℤ) ⟨y, hy⟩ := by
  subst h
  rfl

end Raise

/-! ### `KcSelmerSupport` for the image of inflation -/

section Image

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K}
  {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  {M' : Type} [AddCommGroup M'] [DistribMulAction G' M'] [TopologicalSpace M']
  [DiscreteTopology M'] [ContinuousSMul G' M']
  (D : KcLevelData S W G' M')

/-- The zero cochain is locally trivial (the premises of the inputs are inhabited).
Kind: PROVED. -/
theorem kcLocTriv_zero (m : ℕ) :
    KcLocTriv W (0 : (contCochains ℤ (GKS K S) (Lev K S W m)).X 1) := by
  intro v
  refine ⟨0, fun σ => ?_⟩
  rw [smul_zero, sub_zero]
  exact map_zero (compPt W v.1)

/-- **The classes of inflations of locally trivial level cocycles**, a subgroup of
`H¹(G', M')`. Kind: definition. -/
def kcImage : AddSubgroup (H1 G' M') where
  carrier := {s | ∃ (m : ℕ) (f : (contCochains ℤ (GKS K S) (Lev K S W m)).X 1)
    (hf : ((contCochains ℤ (GKS K S) (Lev K S W m)).d 1 2).hom f = 0), KcLocTriv W f ∧
      kerToH1 (k := ℤ) ⟨((kcInflate D m).f 1).hom f, kcInflate_mem_ker D hf⟩ = s}
  zero_mem' := by
    refine ⟨0, 0, map_zero _, kcLocTriv_zero 0, ?_⟩
    rw [← map_zero (kerToH1 (k := ℤ) (G := G') (M := M'))]
    congr 1
    exact Subtype.ext (map_zero _)
  add_mem' := by
    rintro _ _ ⟨m₁, f₁, hf₁, hl₁, rfl⟩ ⟨m₂, f₂, hf₂, hl₂, rfl⟩
    let F₁ := ((kcRaise m₁ (m₁ + m₂) (Nat.le_add_right _ _)).f 1).hom f₁
    let F₂ := ((kcRaise m₂ (m₁ + m₂) (Nat.le_add_left _ _)).f 1).hom f₂
    have hF₁ := kcRaise_d m₁ (m₁ + m₂) (Nat.le_add_right _ _) f₁ hf₁
    have hF₂ := kcRaise_d m₂ (m₁ + m₂) (Nat.le_add_left _ _) f₂ hf₂
    refine ⟨m₁ + m₂, F₁ + F₂, by rw [map_add, hF₁, hF₂, add_zero], ?_, ?_⟩
    · intro v
      obtain ⟨R₁, hR₁⟩ := kcRaise_locTriv m₁ (m₁ + m₂) (Nat.le_add_right _ _) hl₁ v
      obtain ⟨R₂, hR₂⟩ := kcRaise_locTriv m₂ (m₁ + m₂) (Nat.le_add_left _ _) hl₂ v
      refine ⟨R₁ + R₂, fun σ => ?_⟩
      change compPt W v.1 (((cochainFun F₁ (fun _ => locMap K S v.1 σ) : Lev K S W (m₁ + m₂)) :
        Pt K S W) + ((cochainFun F₂ (fun _ => locMap K S v.1 σ) : Lev K S W (m₁ + m₂)) :
          Pt K S W)) = _
      rw [map_add, hR₁, hR₂, smul_add]
      abel
    · have e1 := kc_kerToH1_congr (kcInflate_mem_ker D hF₁) (kcInflate_mem_ker D hf₁)
        (kcInflate_raise D m₁ (m₁ + m₂) _ f₁)
      have e2 := kc_kerToH1_congr (kcInflate_mem_ker D hF₂) (kcInflate_mem_ker D hf₂)
        (kcInflate_raise D m₂ (m₁ + m₂) _ f₂)
      refine (kc_kerToH1_congr _
        (⟨_, kcInflate_mem_ker D hF₁⟩ + ⟨_, kcInflate_mem_ker D hF₂⟩ :
          LinearMap.ker ((contCochains ℤ G' M').d 1 2).hom).2 (map_add _ _ _)).trans ?_
      change kerToH1 (k := ℤ) (⟨_, kcInflate_mem_ker D hF₁⟩ + ⟨_, kcInflate_mem_ker D hF₂⟩) = _
      rw [map_add, e1, e2]
  neg_mem' := by
    rintro _ ⟨m, f, hf, hl, rfl⟩
    refine ⟨m, -f, by rw [map_neg, hf, neg_zero], ?_, ?_⟩
    · intro v
      obtain ⟨R, hR⟩ := hl v
      refine ⟨-R, fun σ => ?_⟩
      change compPt W v.1 (-((cochainFun f (fun _ => locMap K S v.1 σ) : Lev K S W m) :
        Pt K S W)) = _
      rw [map_neg, hR, smul_neg]
      abel
    · refine (kc_kerToH1_congr _
        (-⟨_, kcInflate_mem_ker D hf⟩ : LinearMap.ker ((contCochains ℤ G' M').d 1 2).hom).2
          (map_neg _ _)).trans ?_
      change kerToH1 (k := ℤ) (-⟨_, kcInflate_mem_ker D hf⟩) = _
      rw [map_neg]

/-- **Non-vacuity of `KcSelmerSupport`**: it holds for every level datum and the image of
inflation. Kind: PROVED. -/
theorem kcSelmerSupport_image : KcSelmerSupport D (kcImage D) where
  sel_of_loc m f hf hl := ⟨m, f, hf, hl, rfl⟩
  loc_of_sel _ hs := hs

/-- **The construction without any input**: `kcPhi` for `kcImage D` is a quasi-isomorphism.
Kind: PROVED. -/
theorem kcPhi_quasiIso_image [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n)) :
    QuasiIso (kcPhi hFull D (kcImage D) (kcSelmerSupport_image D)) :=
  kcPhi_quasiIso hFull D (kcImage D) (kcSelmerSupport_image D)

end Image

/-! ### `KcArithSelmerLevel` at level `2^0` -/

section LevelZero

variable (k : ℤ) (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k))))
  (E : WeierstrassCurve ℚ)

/-- `E[2^0] = 0`. Kind: PROVED. -/
theorem kc_torsionCoeff_one_subsingleton : Subsingleton (E.TorsionCoeff (2 ^ 0)) := by
  constructor
  intro P Q
  have hP : (P : E.PointCoeff) = 0 := by
    have := AddSubgroup.torsionBy.nsmul P
    simpa using this
  have hQ : (Q : E.PointCoeff) = 0 := by
    have := AddSubgroup.torsionBy.nsmul Q
    simpa using this
  exact Subtype.ext (hP.trans hQ.symm)

/-- `H¹(G_K, E[2^0]) = 0`. Kind: PROVED. -/
theorem kc_H1_level_zero (c : H1 (galK (sqrtK k)) (E.TorsionCoeff (2 ^ 0))) : c = 0 := by
  have := kc_torsionCoeff_one_subsingleton E
  induction c using QuotientAddGroup.induction_on with
  | H z =>
    have hz : z = 0 := Subtype.ext (funext fun _ => Subsingleton.elim _ _)
    rw [hz]
    rfl

/-- **`KcArithSelmerLevel.sel_of_loc` holds at level `2^0`**, unconditionally. Kind: PROVED. -/
theorem kcArithSelmerLevel_sel_zero
    (f : (contCochains ℤ (GKS (QuadraticField k) S)
      (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) 0)).X 1)
    (hf : ((contCochains ℤ (GKS (QuadraticField k) S)
      (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) 0)).d 1 2).hom f = 0) :
    kerToH1 (k := ℤ) ⟨((kcInfl k S E 0).f 1).hom f, kcInfl_mem_ker k S E hf⟩ ∈
      selmerLevelK (sqrtK k) E 0 := by
  rw [kc_H1_level_zero k E (kerToH1 (k := ℤ) _)]
  exact zero_mem _

/-- **`KcArithSelmerLevel.loc_of_sel` holds at level `2^0`**, unconditionally, with the zero
cocycle. Kind: PROVED. -/
theorem kcArithSelmerLevel_loc_zero (c : H1 (galK (sqrtK k)) (E.TorsionCoeff (2 ^ 0))) :
    ∃ (f : (contCochains ℤ (GKS (QuadraticField k) S)
        (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) 0)).X 1)
      (hf : ((contCochains ℤ (GKS (QuadraticField k) S)
        (Lev (QuadraticField k) S (E.baseChange (QuadraticField k)) 0)).d 1 2).hom f = 0),
      KcLocTriv (E.baseChange (QuadraticField k)) f ∧
        kerToH1 (k := ℤ) ⟨((kcInfl k S E 0).f 1).hom f, kcInfl_mem_ker k S E hf⟩ = c :=
  ⟨0, map_zero _, kcLocTriv_zero 0, (kc_H1_level_zero k E _).trans (kc_H1_level_zero k E c).symm⟩

end LevelZero

end ZInQ.Manuscript.RC
