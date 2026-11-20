import ZInQKernel.Contrib.OneProof.RC.Wiring.KummerCompCore
import ZInQKernel.Contrib.OneProof.RC.Wiring.KummerCompLocal
import ZInQKernel.Contrib.CloudB3RC53.TameModel.QIsoCriterion

/-!
# Theorem 5.3, Lane RC37: the lift to the discrete Selmer complex

Manuscript `diophantine_zq.tex`, tex 4005–4014: the RC53 group's coefficient comparison
`KummerCoefficientComparison` is a quasi-isomorphism `τ_{≤1}(C_K ⊗ ℚ₂/ℤ₂) → C_disc(Sel)` to the
cocycle complex of the Selmer group. This file builds the morphism for a level datum `D`
(`KummerCompCore.lean`) and a target subgroup `L ⊆ H¹(G', M')`, under the named arithmetic input
`KcSelmerSupport D L` (GLUE, the description of the Selmer group through `G_{K,S}` and the places
of `S`, stated at each finite level `2^m`):

* `kcLift`: lifting a morphism of complexes through a degreewise injective one;
* `kc_mem_disc_of_class`: a continuous cocycle whose class lies in `L` lies in the degree-one
  term of the cocycle complex of `L`;
* `kc_psi_mem_disc` (the local part (c) of the comparison): the image under `ψ` of every
  degree-one cocycle of `C_K ⊗ ℚ₂/ℤ₂` is a Selmer cocycle — its level-`m` reduction is locally
  trivial at every place of `S` by the local Kummer lemma `kcLattice_coboundary`, and the input
  `KcSelmerSupport.sel_of_loc` turns this into membership in `L`;
* **`kcPhi`**: the morphism `τ_{≤1}(C_K ⊗ ℚ₂/ℤ₂) → C_disc(L)` with `kcPhi ≫ ι = ι_{≤1} ≫ ψ`
  (`kcPhi_comp`).

Kinds: definitions, PROVED, and one named input (`KcSelmerSupport`, GLUE).
-/

noncomputable section

set_option maxHeartbeats 1600000

namespace ZInQ.Manuscript.RC

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ZInQ.Manuscript.RC53Assist.CentralUniversal ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.LambdaCoef ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.Finiteness ZInQ.Contrib.RC53Assist.CalibrationShape
open TauCeti TauCeti.ContCohomology
open scoped TensorProduct

attribute [local instance] levTop continuousSMul_lev

/-! ### Lifting through a degreewise injective morphism -/

section Lift

variable {A D X : CochainComplex (ModuleCat.{0} ℤ) ℤ} (f : A ⟶ X) (ι : D ⟶ X)
  (hι : ∀ n, Function.Injective (ι.f n).hom)
  (h : ∀ (n : ℤ) (a : A.X n), ∃ b : D.X n, (ι.f n).hom b = (f.f n).hom a)

/-- The chosen preimage. Kind: definition. -/
def kcLiftFun (n : ℤ) (a : A.X n) : D.X n := Classical.choose (h n a)

theorem kcLiftFun_spec (n : ℤ) (a : A.X n) :
    (ι.f n).hom (kcLiftFun f ι h n a) = (f.f n).hom a :=
  Classical.choose_spec (h n a)

/-- **The lift** of `f` through the degreewise injective `ι`. Kind: definition. -/
def kcLift : A ⟶ D where
  f n := ModuleCat.ofHom
    { toFun := kcLiftFun f ι h n
      map_add' := fun a b => hι n (by
        rw [map_add, kcLiftFun_spec, kcLiftFun_spec, kcLiftFun_spec, map_add])
      map_smul' := fun c a => hι n (by
        rw [(ι.f n).hom.map_smul, kcLiftFun_spec, kcLiftFun_spec, (f.f n).hom.map_smul]
        rfl) }
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply hι j
    change (ι.f j).hom ((D.d i j).hom (kcLiftFun f ι h i a)) =
      (ι.f j).hom (kcLiftFun f ι h j ((A.d i j).hom a))
    have e1 : (ι.f j).hom ((D.d i j).hom (kcLiftFun f ι h i a)) =
        (X.d i j).hom ((ι.f i).hom (kcLiftFun f ι h i a)) :=
      (congrArg (fun g => g.hom (kcLiftFun f ι h i a)) (ι.comm i j)).symm
    have e2 : (X.d i j).hom ((f.f i).hom a) = (f.f j).hom ((A.d i j).hom a) :=
      congrArg (fun g => g.hom a) (f.comm i j)
    rw [e1, kcLiftFun_spec, e2, kcLiftFun_spec]

/-- **The lift factors `f`.** Kind: PROVED. -/
theorem kcLift_comp : kcLift f ι hι h ≫ ι = f := by
  ext n a
  exact kcLiftFun_spec f ι h n a

end Lift

/-! ### Homology maps from cocycles -/

section Homology

variable {R : Type} [Ring R]

/-- An elementwise criterion for injectivity of a homology map. Kind: PROVED. -/
theorem kc_homologyMap_injective {K L : CochainComplex (ModuleCat.{0} R) ℤ} (φ : K ⟶ L)
    (i j k : ℤ) (hi : (ComplexShape.up ℤ).prev j = i) (hk : (ComplexShape.up ℤ).next j = k)
    (hinj : ∀ x, (K.d j k).hom x = 0 → ∀ z, (φ.f j).hom x = (L.d i j).hom z →
      ∃ w, (K.d i j).hom w = x) :
    Function.Injective (HomologicalComplex.homologyMap φ j).hom := by
  subst hi hk
  let ψ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} R) (ComplexShape.up ℤ) j).map φ
  change Function.Injective (ShortComplex.homologyMap ψ).hom
  have hnat : ∀ c, (ShortComplex.homologyMap ψ).hom ((K.sc j).homologyπ.hom c) =
      (L.sc j).homologyπ.hom ((ShortComplex.cyclesMap ψ).hom c) := fun c =>
    congrArg (fun f => f.hom c) (ShortComplex.homologyπ_naturality ψ)
  have hci : ∀ c, (L.sc j).iCycles.hom ((ShortComplex.cyclesMap ψ).hom c) =
      ψ.τ₂.hom ((K.sc j).iCycles.hom c) := fun c =>
    congrArg (fun f => f.hom c) (ShortComplex.cyclesMap_i ψ)
  have hgi : ∀ c, (K.sc j).g.hom ((K.sc j).iCycles.hom c) = 0 :=
    fun c => congrArg (fun f => f.hom c) (K.sc j).iCycles_g
  rw [injective_iff_map_eq_zero]
  intro h hh
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (K.sc j).homologyπ).1 inferInstance h
  rw [hnat, ZInQ.Contrib.CloudB3RC53.TameModel.homologyπ_eq_zero_iff_moduleCat, hci] at hh
  obtain ⟨z, hz⟩ := hh
  obtain ⟨w, hw⟩ := hinj _ (hgi c) z hz.symm
  exact (ZInQ.Contrib.CloudB3RC53.TameModel.homologyπ_eq_zero_iff_moduleCat (K.sc j) c).2 ⟨w, hw⟩

/-- An elementwise criterion for the image of one homology map to contain that of another.
Kind: PROVED. -/
theorem kc_homologyMap_range {K L D : CochainComplex (ModuleCat.{0} R) ℤ} (ψ : K ⟶ L)
    (ι : D ⟶ L) (i j k : ℤ) (hi : (ComplexShape.up ℤ).prev j = i)
    (hk : (ComplexShape.up ℤ).next j = k)
    (h : ∀ y, (D.d j k).hom y = 0 → ∃ x, (K.d j k).hom x = 0 ∧
      ∃ z, (ψ.f j).hom x = (ι.f j).hom y + (L.d i j).hom z) (c : D.homology j) :
    ∃ c', (HomologicalComplex.homologyMap ψ j).hom c' =
      (HomologicalComplex.homologyMap ι j).hom c := by
  subst hi hk
  let ψ' := (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} R) (ComplexShape.up ℤ) j).map ψ
  let ι' := (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} R) (ComplexShape.up ℤ) j).map ι
  change ∃ c', (ShortComplex.homologyMap ψ').hom c' = (ShortComplex.homologyMap ι').hom c
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (D.sc j).homologyπ).1 inferInstance c
  have hgi : (D.sc j).g.hom ((D.sc j).iCycles.hom c) = 0 :=
    congrArg (fun f => f.hom c) (D.sc j).iCycles_g
  obtain ⟨x, hx, z, hxz⟩ := h _ hgi
  obtain ⟨c₁, hc₁⟩ := ZInQ.Contrib.CloudB3RC53.TameModel.exists_cycle_moduleCat (K.sc j) x hx
  refine ⟨(K.sc j).homologyπ.hom c₁, ?_⟩
  have hnatψ : (ShortComplex.homologyMap ψ').hom ((K.sc j).homologyπ.hom c₁) =
      (L.sc j).homologyπ.hom ((ShortComplex.cyclesMap ψ').hom c₁) :=
    congrArg (fun f => f.hom c₁) (ShortComplex.homologyπ_naturality ψ')
  have hnatι : (ShortComplex.homologyMap ι').hom ((D.sc j).homologyπ.hom c) =
      (L.sc j).homologyπ.hom ((ShortComplex.cyclesMap ι').hom c) :=
    congrArg (fun f => f.hom c) (ShortComplex.homologyπ_naturality ι')
  rw [hnatψ, hnatι, ← sub_eq_zero, ← map_sub,
    ZInQ.Contrib.CloudB3RC53.TameModel.homologyπ_eq_zero_iff_moduleCat, map_sub]
  have h1 : (L.sc j).iCycles.hom ((ShortComplex.cyclesMap ψ').hom c₁) =
      ψ'.τ₂.hom ((K.sc j).iCycles.hom c₁) :=
    congrArg (fun f => f.hom c₁) (ShortComplex.cyclesMap_i ψ')
  have h2 : (L.sc j).iCycles.hom ((ShortComplex.cyclesMap ι').hom c) =
      ι'.τ₂.hom ((D.sc j).iCycles.hom c) :=
    congrArg (fun f => f.hom c) (ShortComplex.cyclesMap_i ι')
  rw [h1, h2, hc₁]
  refine ⟨z, ?_⟩
  change (L.d _ j).hom z = (ψ.f j).hom x - (ι.f j).hom ((D.sc j).iCycles.hom c)
  rw [hxz]
  abel

/-- **Degree-wise quasi-isomorphism from a commutative square.** If `φ ≫ ι = α ≫ ψ` with `α` a
quasi-isomorphism at `n`, `ι` injective on `Hⁿ`, `ψ` injective on `Hⁿ`, and the image of `ι` in
`Hⁿ` contained in that of `ψ`, then `φ` is a quasi-isomorphism at `n`. Kind: PROVED. -/
theorem kc_quasiIsoAt_of_square {A B P X : CochainComplex (ModuleCat.{0} R) ℤ} (φ : A ⟶ B)
    (ι : B ⟶ X) (α : A ⟶ P) (ψ : P ⟶ X) (hsq : φ ≫ ι = α ≫ ψ) (n : ℤ) [QuasiIsoAt α n]
    (hψ : Function.Injective (HomologicalComplex.homologyMap ψ n).hom)
    (hι : Function.Injective (HomologicalComplex.homologyMap ι n).hom)
    (hrange : ∀ c, ∃ c', (HomologicalComplex.homologyMap ψ n).hom c' =
      (HomologicalComplex.homologyMap ι n).hom c) :
    QuasiIsoAt φ n := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hα : IsIso (HomologicalComplex.homologyMap α n) :=
    (quasiIsoAt_iff_isIso_homologyMap α n).1 inferInstance
  have hcomm : ∀ a, (HomologicalComplex.homologyMap ι n).hom
      ((HomologicalComplex.homologyMap φ n).hom a) =
      (HomologicalComplex.homologyMap ψ n).hom ((HomologicalComplex.homologyMap α n).hom a) := by
    intro a
    have e := congrArg (fun g => HomologicalComplex.homologyMap g n) hsq
    simp only [HomologicalComplex.homologyMap_comp] at e
    exact congrArg (fun g => g.hom a) e
  have hαb := (ConcreteCategory.isIso_iff_bijective (HomologicalComplex.homologyMap α n)).1 hα
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a b hab => ?_, fun b => ?_⟩
  · apply hαb.1
    apply hψ
    rw [← hcomm, ← hcomm, hab]
  · obtain ⟨c', hc'⟩ := hrange b
    obtain ⟨a, rfl⟩ := hαb.2 c'
    refine ⟨a, hι ?_⟩
    rw [hcomm, hc']

end Homology

/-! ### The named arithmetic input -/

section Input

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K)
  {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  {M' : Type} [AddCommGroup M'] [DistribMulAction G' M'] [TopologicalSpace M']
  [DiscreteTopology M'] [ContinuousSMul G' M']

/-- **Local triviality at the places of `S`** of a level-`m` cochain of `G_{K,S}`: at every
`v ∈ S` its restriction to `G_{K_v}`, read in `E(K̄_v)`, is a Galois coboundary `σ ↦ σ R − R`;
equivalently (`kcLocalKummer_iff`) its class lies in the image of the local Kummer map
`E(K_v)/2^m → H¹(K_v, E[2^m])`, i.e. dies in `H¹(K_v, E)`. Kind: definition. -/
def KcLocTriv {m : ℕ} (f : (contCochains ℤ (GKS K S) (Lev K S W m)).X 1) : Prop :=
  ∀ v : Places K S, ∃ R : PtAlg (v.1.adicCompletion K) (W.baseChange (v.1.adicCompletion K)),
    ∀ σ : Gloc K v.1, compPt W v.1 ((cochainFun f (fun _ => locMap K S v.1 σ) : Lev K S W m) :
      Pt K S W) = σ • R - R

variable {W} (D : KcLevelData S W G' M')

/-- Inflation commutes with the degree-one differential. Kind: PROVED. -/
theorem kcInflate_d (m : ℕ) (f : (contCochains ℤ (GKS K S) (Lev K S W m)).X 1) :
    ((contCochains ℤ G' M').d 1 2).hom (((kcInflate D m).f 1).hom f) =
      ((kcInflate D m).f 2).hom (((contCochains ℤ (GKS K S) (Lev K S W m)).d 1 2).hom f) :=
  congrArg (fun g => g.hom f) ((kcInflate D m).comm 1 2)

/-- An inflated cocycle is a cocycle. Kind: PROVED. -/
theorem kcInflate_mem_ker {m : ℕ} {f : (contCochains ℤ (GKS K S) (Lev K S W m)).X 1}
    (hf : ((contCochains ℤ (GKS K S) (Lev K S W m)).d 1 2).hom f = 0) :
    ((kcInflate D m).f 1).hom f ∈ LinearMap.ker ((contCochains ℤ G' M').d 1 2).hom := by
  rw [LinearMap.mem_ker, kcInflate_d, hf, map_zero]

/-- **The named arithmetic input (GLUE): the Selmer group through `G_{K,S}` and the places of
`S`**, at every finite level `2^m`. For a continuous cocycle `f : G_{K,S} → E(K_S)[2^m]`:
* `sel_of_loc`: if `f` is locally trivial at every place of `S` (`KcLocTriv`), the class of its
  inflation lies in `L`;
* `loc_of_sel`: every class of `L` is the class of the inflation of such a locally trivial
  cocycle at some level.
For the arithmetic instance (`G' = G_K`, `M' = E[2^∞]`, `L = Sel_{2^∞}(E/K)`) this is the classical
description `Sel_{2^m}(E/K) = ker(H¹(G_{K,S}, E[2^m]) → ∏_{v ∈ S} H¹(K_v, E))` (for `K` totally
complex, `S ⊇ {v ∣ 2}` finite and `E[2^∞] ⊂ E(K_S)`), passed to the limit; see
`KummerCompArith.lean`. Kind: definition (input). -/
structure KcSelmerSupport (L : AddSubgroup (H1 G' M')) : Prop where
  sel_of_loc : ∀ (m : ℕ) (f : (contCochains ℤ (GKS K S) (Lev K S W m)).X 1)
    (hf : ((contCochains ℤ (GKS K S) (Lev K S W m)).d 1 2).hom f = 0), KcLocTriv W f →
      kerToH1 (k := ℤ) ⟨((kcInflate D m).f 1).hom f, kcInflate_mem_ker D hf⟩ ∈ L
  loc_of_sel : ∀ s ∈ L, ∃ (m : ℕ) (f : (contCochains ℤ (GKS K S) (Lev K S W m)).X 1)
    (hf : ((contCochains ℤ (GKS K S) (Lev K S W m)).d 1 2).hom f = 0), KcLocTriv W f ∧
      kerToH1 (k := ℤ) ⟨((kcInflate D m).f 1).hom f, kcInflate_mem_ker D hf⟩ = s

end Input

/-! ### Selmer cocycles -/

section Disc

variable {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  {M' : Type} [AddCommGroup M'] [DistribMulAction G' M'] [TopologicalSpace M']
  [DiscreteTopology M'] [ContinuousSMul G' M'] (L : AddSubgroup (H1 G' M'))

/-- **A continuous cocycle whose class lies in `L` is a degree-one cochain of the cocycle
complex of `L`.** Kind: PROVED. -/
theorem kc_mem_disc_of_class (z : contCochain ℤ G' M' 1) (hz : contD ℤ G' M' 1 z = 0)
    (h : kerToH1 (k := ℤ) ⟨z, hz⟩ ∈ L) : z ∈ subgroupCocycleSub L ⊔ contB1 ℤ G' M' := by
  apply Submodule.mem_sup_left
  apply Submodule.subset_span
  refine ⟨⟨fun g => contFun (k := ℤ) z (fun _ => g), mem_Z1_of_d_eq_zero z hz⟩, h, ?_⟩
  apply Subtype.ext
  funext v
  change contFun (k := ℤ) z (fun _ => v 0) = contFun (k := ℤ) z v
  congr 1
  funext i
  rw [Subsingleton.elim i 0]

/-- The inclusion of the cocycle complex of `L` is injective in every degree. Kind: PROVED. -/
theorem kc_iotaD_injective (n : ℤ) :
    Function.Injective ((GHom.toCC (cocycleConditionι (subgroupCocycleSub L)
      (subgroupCocycleSub_d_zero L))).f n).hom :=
  cocycleConditionι_injective _ _ n

end Disc

end ZInQ.Manuscript.RC
