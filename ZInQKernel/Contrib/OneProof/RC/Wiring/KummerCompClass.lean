import ZInQKernel.Contrib.OneProof.RC.Wiring.KummerCompQuot
import ZInQKernel.Contrib.CloudB3RC53.TameModel.QIsoCriterion

/-!
# Theorem 5.3, Lane RC37: homology classes for the Kummer compatibility

Homology-class chasing for the coefficient comparison of the compact Kummer complex (manuscript
`diophantine_zq.tex`, the universal-coefficient step `C_K ⊗ ℚ₂/ℤ₂` and the identification of
its first cohomology with the Selmer group, tex 4005–4014). Classes are followed through the
canonical isomorphisms on representing cycles.

* `kc_mapHomologyIso_homologyπ`: for a functor `F` between module categories that preserves the
  left homology of a short complex `S`, the canonical isomorphism `H(S.map F) ≅ F(H S)` sends the
  class of a cycle to `F` of the class map on any element with the same underlying element.
* `kc_coefficientTensorHomologyEquiv_cycle`: the flat base-change identification
  `H¹(C ⊗ ℚ₂) ≅ ℚ₂ ⊗ H¹(C)` sends the class of the cycle `q ⊗ c` to `q ⊗ [c]`.
* `kc_rationalToDivisible_cycle` (C1): universal coefficients on a cycle: the image of
  `q ⊗ [c]` in `H¹(C ⊗ ℚ₂/ℤ₂)` is the class of the cycle with underlying element `π(q ⊗ c)`.
* `kcSelmerEquivOf φ`: the Selmer identification `H¹(Q) ≃ L` induced by a comparison `φ` of
  the degree-one truncation of `Q` (read as a complex of abelian groups) with the cocycle complex
  of a subgroup `L ⊆ H¹(G, M)`, built exactly as `KummerCoefficientComparison.selmerEquiv`;
  `kcSelmerEquivOf_eq`: for a `KummerCoefficientComparison` it is `selmerEquiv`.
* `kc_integerHomologyEquiv_cycle`, `kc_subgroupCocycleHomologyEquiv_homologyπ`: restriction of
  scalars and the cocycle-class identification on classes of cycles.
* `kc_selmerEquiv_cycle` (C2): if `φ` agrees after the inclusions with a cochain map
  `ψ : Q → C^•_cont(G, M)`, then for a cycle `c` of `Q` the cochain `ψ(c)` is a continuous
  cocycle and `kcSelmerEquivOf φ [c]` is its cohomology class (`kerToH1`);
  `kc_comparison_selmerEquiv_cycle`: the same statement for `I.selmerEquiv`.

Kinds: definitions and PROVED.
-/

noncomputable section

set_option autoImplicit false

namespace ZInQ.Manuscript.RC

open CategoryTheory CategoryTheory.Limits
open ZInQ.Manuscript.RC53Assist.CentralUniversal
open scoped TensorProduct

section MapHomology

variable {R R' : Type} [Ring R] [Ring R']

/-- For a functor between module categories preserving the left homology of `S`, the canonical
isomorphism `H(S.map F) ≅ F(H S)` sends the class of a cycle `c'` of `S.map F` to the image under
`F` of the class map applied to any `u ∈ F(cycles S)` with the same underlying element.
Kind: PROVED. -/
theorem kc_mapHomologyIso_homologyπ (S : ShortComplex (ModuleCat.{0} R))
    (F : ModuleCat.{0} R ⥤ ModuleCat.{0} R') [F.PreservesZeroMorphisms]
    [F.PreservesLeftHomologyOf S] (c' : (S.map F).cycles) (u : F.obj S.cycles)
    (hu : (F.map S.iCycles).hom u = (S.map F).iCycles.hom c') :
    (S.mapHomologyIso F).hom.hom ((S.map F).homologyπ.hom c') = (F.map S.homologyπ).hom u := by
  have hinj : Function.Injective (F.map S.homologyData.left.i).hom := by
    rw [← ModuleCat.mono_iff_injective]
    exact (inferInstance : Mono (S.homologyData.left.map F).i)
  have hk : (S.homologyData.left.map F).cyclesIso.hom.hom c' =
      (F.map S.homologyData.left.cyclesIso.hom).hom u := by
    apply hinj
    have e1 := congrArg (fun f => f.hom c') (S.homologyData.left.map F).cyclesIso_hom_comp_i
    have e2 := congrArg (fun f => (F.map f).hom u) S.homologyData.left.cyclesIso_hom_comp_i
    simp only [F.map_comp] at e2
    exact e1.trans (hu.symm.trans e2.symm)
  have hπ := congrArg (fun f => f.hom c')
    (S.homologyData.left.map F).homologyπ_comp_homologyIso_hom
  have hid : S.homologyData.left.homologyIso.hom = 𝟙 _ := by
    change S.leftHomologyIso.inv ≫ S.leftHomologyIso.hom = 𝟙 _
    exact Iso.inv_hom_id _
  have h3 : S.homologyData.left.cyclesIso.hom ≫ S.homologyData.left.π = S.homologyπ := by
    refine (S.homologyData.left.homologyπ_comp_homologyIso_hom).symm.trans ?_
    refine (congrArg (fun f => S.homologyπ ≫ f) hid).trans ?_
    exact Category.comp_id _
  have e4 := congrArg (fun f => (F.map f).hom u) h3
  simp only [F.map_comp] at e4
  refine hπ.trans (Eq.trans ?_ e4)
  exact congrArg (fun z => (F.map S.homologyData.left.π).hom z) hk

end MapHomology

section RationalCycle

variable (C : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ)

/-- The class of a rational cycle with underlying element `q ⊗ x`, `x` the underlying element
of an integral cycle `c`, is `q ⊗ [c]` under the flat base-change identification
`coefficientTensorHomologyEquiv`. Kind: PROVED. -/
theorem kc_coefficientTensorHomologyEquiv_cycle (q : ℚ_[2]) (c : C.cycles 1)
    (c₁ : (rationalCoefficientComplex C).cycles 1)
    (hc₁ : ((rationalCoefficientComplex C).iCycles 1).hom c₁ =
      kcTmul C q ((C.iCycles 1).hom c)) :
    coefficientTensorHomologyEquiv C 1 (((rationalCoefficientComplex C).homologyπ 1).hom c₁) =
      q ⊗ₜ[ℤ_[2]] ((C.homologyπ 1).hom c) :=
  kc_mapHomologyIso_homologyπ (C.sc 1) rationalFunctor c₁
    (show rationalFunctor.obj (C.sc 1).cycles from
      (q ⊗ₜ[ℤ_[2]] c : ℚ_[2] ⊗[ℤ_[2]] C.cycles 1)) hc₁.symm

/-- **(C1) Universal coefficients on a cycle.** For a cycle `c` of `C` in degree one and
`q ∈ ℚ₂`, the class `rationalToDivisible (q ⊗ [c])` in `H¹(C ⊗ ℚ₂/ℤ₂)` is the class of the
cycle `[q ⊗ c]` with underlying element `π(q ⊗ c)`. Kind: PROVED. -/
theorem kc_rationalToDivisible_cycle [∀ n, Module.IsTorsionFree ℤ_[2] (C.X n)] (q : ℚ_[2])
    (c : C.cycles 1) :
    ∃ c' : (coefficientQuotientComplex C).cycles 1,
      ((coefficientQuotientComplex C).iCycles 1).hom c' =
        kcPi C 1 (kcTmul C q ((C.iCycles 1).hom c)) ∧
      rationalToDivisible C (q ⊗ₜ[ℤ_[2]] ((C.homologyπ 1).hom c)) =
        ((coefficientQuotientComplex C).homologyπ 1).hom c' := by
  have hd : ((rationalCoefficientComplex C).sc 1).g.hom
      (kcTmul C q ((C.iCycles 1).hom c)) = 0 := by
    have h := congrArg (fun f => f.hom c) (C.iCycles_d 1 ((ComplexShape.up ℤ).next 1))
    change kcTmul C q ((C.d 1 ((ComplexShape.up ℤ).next 1)).hom ((C.iCycles 1).hom c)) = 0
    rw [show (C.d 1 ((ComplexShape.up ℤ).next 1)).hom ((C.iCycles 1).hom c) = 0 from h]
    exact TensorProduct.tmul_zero _ _
  obtain ⟨c₁, hc₁⟩ := ZInQ.Contrib.CloudB3RC53.TameModel.exists_cycle_moduleCat
    ((rationalCoefficientComplex C).sc 1) (kcTmul C q ((C.iCycles 1).hom c)) hd
  refine ⟨(HomologicalComplex.cyclesMap (cokernel.π (coefficientMap C)) 1).hom c₁, ?_, ?_⟩
  · have h := congrArg (fun f => f.hom c₁)
      (HomologicalComplex.cyclesMap_i (cokernel.π (coefficientMap C)) 1)
    exact h.trans (congrArg (kcPi C 1) hc₁)
  · have hT := kc_coefficientTensorHomologyEquiv_cycle C q c c₁ hc₁
    have hsymm : (coefficientTensorHomologyEquiv C 1).symm
        (q ⊗ₜ[ℤ_[2]] ((C.homologyπ 1).hom c)) =
          ((rationalCoefficientComplex C).homologyπ 1).hom c₁ := by
      rw [← hT, LinearEquiv.symm_apply_apply]
    change coefficientProjection C ((coefficientTensorHomologyEquiv C 1).symm
      (q ⊗ₜ[ℤ_[2]] ((C.homologyπ 1).hom c))) = _
    rw [hsymm]
    exact congrArg (fun f => f.hom c₁)
      (HomologicalComplex.homologyπ_naturality (cokernel.π (coefficientMap C)) 1)

end RationalCycle

section SelmerCycle

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open TauCeti TauCeti.ContCohomology

variable {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [DistribMulAction G M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M] {L : AddSubgroup (H1 G M)}
  {Q : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ}

/-- The Selmer identification `H¹(Q) ≃ L` induced by a cochain comparison
`φ : τ_{≤1}(Q as abelian groups) → (cocycle complex of L)` that is a quasi-isomorphism in degree
one: restriction of scalars, the inverse of the truncation isomorphism in degree one, `φ` on
cohomology, and the cocycle-class identification. Kind: definition. -/
def kcSelmerEquivOf (φ : (integerCoefficientComplex Q).truncLE 1 ⟶ subgroupCocycleComplex L)
    [QuasiIsoAt φ 1] : Q.homology 1 ≃+ L :=
  (integerHomologyEquiv Q 1).symm.trans
    ((asIso (HomologicalComplex.homologyMap ((integerCoefficientComplex Q).ιTruncLE 1)
      1)).toLinearEquiv.toAddEquiv.symm.trans
      ((asIso (HomologicalComplex.homologyMap φ 1)).toLinearEquiv.toAddEquiv.trans
        (subgroupCocycleHomologyEquiv L)))

/-- Restriction of scalars on the class of a cycle: `integerHomologyEquiv` sends the class of
the cycle of `Q` read as a complex of abelian groups to the class of the cycle of `Q` with the
same underlying element. Kind: PROVED. -/
theorem kc_integerHomologyEquiv_cycle (c : Q.cycles 1)
    (c₁ : (integerCoefficientComplex Q).cycles 1)
    (hc₁ : ((integerCoefficientComplex Q).iCycles 1).hom c₁ = (Q.iCycles 1).hom c) :
    integerHomologyEquiv Q 1 (((integerCoefficientComplex Q).homologyπ 1).hom c₁) =
      (Q.homologyπ 1).hom c :=
  kc_mapHomologyIso_homologyπ (Q.sc 1) (ModuleCat.restrictScalars (Int.castRingHom ℤ_[2])) c₁
    (show (ModuleCat.restrictScalars (Int.castRingHom ℤ_[2])).obj (Q.sc 1).cycles from c)
    hc₁.symm

variable (L) in
/-- The cocycle-class identification `subgroupCocycleHomologyEquiv` on the class of a cycle of
the cocycle complex is the class map `subgroupClass` of its underlying element.
Kind: PROVED. -/
theorem kc_subgroupCocycleHomologyEquiv_homologyπ (d : (subgroupCocycleComplex L).cycles 1) :
    subgroupCocycleHomologyEquiv L (((subgroupCocycleComplex L).homologyπ 1).hom d) =
      subgroupClass L (((subgroupCocycleComplex L).iCycles 1).hom d) := by
  obtain ⟨c₃, hc₃, hc₃'⟩ := cocycleConditionH1Iso_inv_mk (subgroupCocycleSub L)
    (subgroupCocycleSub_d_zero L) (((subgroupCocycleComplex L).iCycles 1).hom d)
  have hc₃d : c₃ = d := (ModuleCat.mono_iff_injective _).1 inferInstance hc₃
  subst hc₃d
  rw [← hc₃']
  have hN : (condB1 (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L)).toAddSubgroup =
      (subgroupClass L).ker := by
    ext x
    change x ∈ condB1 (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L) ↔
      subgroupClass L x = 0
    exact (subgroupClass_zero_iff L x).symm
  have : (condB1 (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L)).toAddSubgroup.Normal :=
    ⟨fun n hn g => by
      convert hn using 1
      abel⟩
  exact congrArg (QuotientAddGroup.liftEquiv (nN := this) _ (subgroupClass_surjective L) hN)
    (congrArg (fun f => f.hom (Submodule.Quotient.mk
      (((subgroupCocycleComplex L).iCycles 1).hom c₃)))
      (cocycleConditionH1Iso (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L)).inv_hom_id)

/-- **(C2) The Selmer identification on a cycle.** Let `ψ : Q → C^•_cont(G, M)` be a cochain
map from `Q` read as a complex of abelian groups, and `φ` a comparison of the degree-one
truncation of `Q` with the cocycle complex of `L` that is a quasi-isomorphism in degree one and
agrees with `ψ` after the inclusions (`hφ`). For a cycle `c` of `Q` in degree one, the cochain
`ψ(c)` is a continuous cocycle, and the Selmer identification `kcSelmerEquivOf φ` sends the
class of `c` to the cohomology class of `ψ(c)`. Kind: PROVED. -/
theorem kc_selmerEquiv_cycle
    (ψ : integerCoefficientComplex Q ⟶ (natCx (contCochains ℤ G M)).toCC)
    (φ : (integerCoefficientComplex Q).truncLE 1 ⟶ subgroupCocycleComplex L)
    (hφ : φ ≫ GHom.toCC (cocycleConditionι (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L)) =
      (integerCoefficientComplex Q).ιTruncLE 1 ≫ ψ)
    [QuasiIsoAt φ 1] (c : Q.cycles 1) :
    ∃ hd : ((contCochains ℤ G M).d 1 2).hom ((ψ.f 1).hom ((Q.iCycles 1).hom c)) = 0,
      ((kcSelmerEquivOf φ ((Q.homologyπ 1).hom c)) : H1 G M) =
        kerToH1 (k := ℤ) ⟨(ψ.f 1).hom ((Q.iCycles 1).hom c), hd⟩ := by
  have hy2 : ∀ j, ((integerCoefficientComplex Q).d 1 j).hom ((Q.iCycles 1).hom c) = 0 :=
    fun j => congrArg (fun f => f.hom c) (Q.iCycles_d 1 j)
  have hd : ((contCochains ℤ G M).d 1 2).hom ((ψ.f 1).hom ((Q.iCycles 1).hom c)) = 0 := by
    have h1 := congrArg (fun f => f.hom ((Q.iCycles 1).hom c)) (ψ.comm 1 2)
    have h2 : ((natCx (contCochains ℤ G M)).toCC.d 1 2).hom
        ((ψ.f 1).hom ((Q.iCycles 1).hom c)) =
          ((contCochains ℤ G M).d 1 2).hom ((ψ.f 1).hom ((Q.iCycles 1).hom c)) :=
      GCx.toCC_d_hom _ 1 2 rfl _
    rw [← h2]
    refine h1.trans ?_
    change (ψ.f 2).hom (((integerCoefficientComplex Q).d 1 2).hom ((Q.iCycles 1).hom c)) = 0
    rw [hy2 2, map_zero]
  refine ⟨hd, ?_⟩
  -- the cycle of `Q` read as a complex of abelian groups
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : (integerCoefficientComplex Q).cycles 1,
      ((integerCoefficientComplex Q).iCycles 1).hom c₁ = (Q.iCycles 1).hom c :=
    ZInQ.Contrib.CloudB3RC53.TameModel.exists_cycle_moduleCat
      ((integerCoefficientComplex Q).sc 1) ((Q.iCycles 1).hom c) (hy2 _)
  have hI := kc_integerHomologyEquiv_cycle c c₁ hc₁
  have hIs : (integerHomologyEquiv Q 1).symm ((Q.homologyπ 1).hom c) =
      ((integerCoefficientComplex Q).homologyπ 1).hom c₁ := by
    rw [← hI, AddEquiv.symm_apply_apply]
  -- a cycle of the truncation with the same class
  have hsurj : Function.Surjective
      (((integerCoefficientComplex Q).truncLE 1).homologyπ 1).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨c₂, hc₂⟩ := hsurj ((asIso (HomologicalComplex.homologyMap
    ((integerCoefficientComplex Q).ιTruncLE 1) 1)).inv.hom
      (((integerCoefficientComplex Q).homologyπ 1).hom c₁))
  have hc₂' : (HomologicalComplex.homologyMap ((integerCoefficientComplex Q).ιTruncLE 1) 1).hom
      ((((integerCoefficientComplex Q).truncLE 1).homologyπ 1).hom c₂) =
        ((integerCoefficientComplex Q).homologyπ 1).hom c₁ := by
    rw [hc₂]
    exact congrArg (fun f => f.hom (((integerCoefficientComplex Q).homologyπ 1).hom c₁))
      (asIso (HomologicalComplex.homologyMap
        ((integerCoefficientComplex Q).ιTruncLE 1) 1)).inv_hom_id
  have hnatι := congrArg (fun f => f.hom c₂)
    (HomologicalComplex.homologyπ_naturality ((integerCoefficientComplex Q).ιTruncLE 1) 1)
  have hzero : ((integerCoefficientComplex Q).homologyπ 1).hom
      ((HomologicalComplex.cyclesMap ((integerCoefficientComplex Q).ιTruncLE 1) 1).hom c₂ -
        c₁) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hnatι.symm.trans hc₂'
  obtain ⟨w, hw⟩ := (ZInQ.Contrib.CloudB3RC53.TameModel.homologyπ_eq_zero_iff_moduleCat
    ((integerCoefficientComplex Q).sc 1) _).1 hzero
  have hp : (ComplexShape.up ℤ).prev 1 = 0 := by
    rw [CochainComplex.prev]
    norm_num
  obtain ⟨w', hw'⟩ : ∃ w' : (integerCoefficientComplex Q).X 0,
      ((integerCoefficientComplex Q).d 0 1).hom w' =
        ((integerCoefficientComplex Q).sc 1).f.hom w :=
    ⟨((integerCoefficientComplex Q).XIsoOfEq hp).hom.hom w,
      congrArg (fun f => f.hom w) ((integerCoefficientComplex Q).XIsoOfEq_hom_comp_d hp 1)⟩
  have hιt : (((integerCoefficientComplex Q).ιTruncLE 1).f 1).hom
      ((((integerCoefficientComplex Q).truncLE 1).iCycles 1).hom c₂) =
        ((integerCoefficientComplex Q).iCycles 1).hom c₁ +
          ((integerCoefficientComplex Q).d 0 1).hom w' := by
    have h1 := congrArg (fun f => f.hom c₂)
      (HomologicalComplex.cyclesMap_i ((integerCoefficientComplex Q).ιTruncLE 1) 1)
    have h2 : ((integerCoefficientComplex Q).iCycles 1).hom
        ((HomologicalComplex.cyclesMap ((integerCoefficientComplex Q).ιTruncLE 1) 1).hom c₂ -
          c₁) =
        (((integerCoefficientComplex Q).ιTruncLE 1).f 1).hom
          ((((integerCoefficientComplex Q).truncLE 1).iCycles 1).hom c₂) -
            ((integerCoefficientComplex Q).iCycles 1).hom c₁ := by
      rw [map_sub]
      exact congrArg₂ (· - ·) h1 rfl
    have h3 : ((integerCoefficientComplex Q).d 0 1).hom w' =
        ((integerCoefficientComplex Q).iCycles 1).hom
          ((HomologicalComplex.cyclesMap ((integerCoefficientComplex Q).ιTruncLE 1) 1).hom c₂ -
            c₁) :=
      hw'.trans hw
    rw [h3, h2]
    abel
  -- the class on the Selmer side
  have hx := congrArg (fun f => f.hom c₂) (HomologicalComplex.cyclesMap_i φ 1)
  have hmain : ((kcSelmerEquivOf φ ((Q.homologyπ 1).hom c)) : H1 G M) =
      subgroupAmbientClass L (((subgroupCocycleComplex L).iCycles 1).hom
        ((HomologicalComplex.cyclesMap φ 1).hom c₂)) := by
    have h5 : kcSelmerEquivOf φ ((Q.homologyπ 1).hom c) =
        subgroupCocycleHomologyEquiv L ((HomologicalComplex.homologyMap φ 1).hom
          ((asIso (HomologicalComplex.homologyMap
            ((integerCoefficientComplex Q).ιTruncLE 1) 1)).inv.hom
              ((integerHomologyEquiv Q 1).symm ((Q.homologyπ 1).hom c)))) := rfl
    have hnatφ : (HomologicalComplex.homologyMap φ 1).hom
        ((((integerCoefficientComplex Q).truncLE 1).homologyπ 1).hom c₂) =
          ((subgroupCocycleComplex L).homologyπ 1).hom
            ((HomologicalComplex.cyclesMap φ 1).hom c₂) :=
      congrArg (fun f => f.hom c₂) (HomologicalComplex.homologyπ_naturality φ 1)
    rw [h5, hIs, ← hc₂]
    refine (congrArg (fun z => ((subgroupCocycleHomologyEquiv L z : L) : H1 G M)) hnatφ).trans ?_
    rw [kc_subgroupCocycleHomologyEquiv_homologyπ]
    rfl
  rw [hmain]
  have key : ∀ (a b : LinearMap.ker ((contCochains ℤ G M).d 1 2).hom)
      (y : (contCochains ℤ G M).X 0),
      ((contCochains ℤ G M).d 0 1).hom y = (a : (contCochains ℤ G M).X 1) - b →
        kerToH1 (k := ℤ) a = kerToH1 (k := ℤ) b := by
    intro a b y hy
    rw [← sub_eq_zero, ← map_sub]
    exact (kerToH1_eq_zero_iff _).2 ⟨y, hy⟩
  refine key (subgroupCycle L (((subgroupCocycleComplex L).iCycles 1).hom
    ((HomologicalComplex.cyclesMap φ 1).hom c₂))) _ ((ψ.f 0).hom w') ?_
  have hφx : (condOne (subgroupCocycleSub L) (subgroupCocycleSub_d_zero L)
      (((subgroupCocycleComplex L).iCycles 1).hom ((HomologicalComplex.cyclesMap φ 1).hom c₂)) :
        contCochain ℤ G M 1) =
      (ψ.f 1).hom ((((integerCoefficientComplex Q).ιTruncLE 1).f 1).hom
        ((((integerCoefficientComplex Q).truncLE 1).iCycles 1).hom c₂)) := by
    have h := congrArg (fun f => (f.f 1).hom
      ((((integerCoefficientComplex Q).truncLE 1).iCycles 1).hom c₂)) hφ
    exact (congrArg (fun z => ((GHom.toCC (cocycleConditionι (subgroupCocycleSub L)
      (subgroupCocycleSub_d_zero L))).f 1).hom z) hx).trans h
  have hsum : (ψ.f 1).hom ((((integerCoefficientComplex Q).ιTruncLE 1).f 1).hom
      ((((integerCoefficientComplex Q).truncLE 1).iCycles 1).hom c₂)) =
        (ψ.f 1).hom ((Q.iCycles 1).hom c) +
          (ψ.f 1).hom (((integerCoefficientComplex Q).d 0 1).hom w') := by
    rw [hιt, map_add, hc₁]
  have hcomm := congrArg (fun f => f.hom w') (ψ.comm 0 1)
  have hX01 : ((natCx (contCochains ℤ G M)).toCC.d 0 1).hom ((ψ.f 0).hom w') =
      ((contCochains ℤ G M).d 0 1).hom ((ψ.f 0).hom w') :=
    GCx.toCC_d_hom _ 0 1 rfl _
  rw [eq_sub_iff_add_eq, add_comm]
  have hcomm' : (ψ.f 1).hom (((integerCoefficientComplex Q).d 0 1).hom w') =
      ((contCochains ℤ G M).d 0 1).hom ((ψ.f 0).hom w') :=
    hcomm.symm.trans hX01
  exact (hφx.trans (hsum.trans
    (congrArg (fun z => (ψ.f 1).hom ((Q.iCycles 1).hom c) + z) hcomm'))).symm

end SelmerCycle

section Agreement

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open TauCeti TauCeti.ContCohomology
open NumberField IsDedekindDomain ZInQ.Manuscript.RC53Assist.QuadraticDescent
  ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53

variable {ℓ : ℕ} {k : ℤ} [(Ecurve ℓ).IsElliptic]
  {S : Set (HeightOneSpectrum (𝓞 (QuadraticField k)))}
  {hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
    ((Ecurve ℓ).baseChange (QuadraticField k)) (2 ^ n)}

/-- For the comparison of a `KummerCoefficientComparison`, `kcSelmerEquivOf` is its Selmer
identification `selmerEquiv`. Kind: PROVED. -/
theorem kcSelmerEquivOf_eq (I : KummerCoefficientComparison ℓ k S hFull)
    [QuasiIsoAt I.comparison 1] :
    kcSelmerEquivOf I.comparison = I.selmerEquiv :=
  rfl

/-- **(C2) for a `KummerCoefficientComparison`**: if `ψ` agrees with the comparison after the
inclusions, the Selmer identification `I.selmerEquiv` sends the class of a cycle `c` of the
coefficient quotient to the cohomology class of the continuous cocycle `ψ(c)`. Kind: PROVED. -/
theorem kc_comparison_selmerEquiv_cycle (I : KummerCoefficientComparison ℓ k S hFull)
    (ψ : integerCoefficientComplex (arithmeticCoefficientComplex ℓ k S hFull) ⟶
      (natCx (contCochains ℤ (galK (sqrtK k)) (TwoPowerCoeff (Ecurve ℓ)))).toCC)
    (hφ : I.comparison ≫ GHom.toCC (cocycleConditionι (subgroupCocycleSub (SelK ℓ k))
        (subgroupCocycleSub_d_zero (SelK ℓ k))) =
      (integerCoefficientComplex (arithmeticCoefficientComplex ℓ k S hFull)).ιTruncLE 1 ≫ ψ)
    (c : (arithmeticCoefficientComplex ℓ k S hFull).cycles 1) :
    ∃ hd : ((contCochains ℤ (galK (sqrtK k)) (TwoPowerCoeff (Ecurve ℓ))).d 1 2).hom
        ((ψ.f 1).hom (((arithmeticCoefficientComplex ℓ k S hFull).iCycles 1).hom c)) = 0,
      ((I.selmerEquiv (((arithmeticCoefficientComplex ℓ k S hFull).homologyπ 1).hom c) :
          SelK ℓ k) : H1 (galK (sqrtK k)) (TwoPowerCoeff (Ecurve ℓ))) =
        kerToH1 (k := ℤ)
          ⟨(ψ.f 1).hom (((arithmeticCoefficientComplex ℓ k S hFull).iCycles 1).hom c), hd⟩ := by
  have : QuasiIso I.comparison := I.quasiIso
  rw [← kcSelmerEquivOf_eq I]
  exact kc_selmerEquiv_cycle ψ I.comparison hφ c

end Agreement

end ZInQ.Manuscript.RC
