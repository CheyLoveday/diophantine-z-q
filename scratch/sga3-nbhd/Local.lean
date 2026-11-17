import ZInQKernel.Contrib.OneProof.SGA3IdComp

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry Limits Topology TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj CToPrinted

namespace SGA3Nbhd

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

/-- In the fibre `G_t` (subspace topology) of a smooth group scheme, the component of `e(t)` is open. -/
theorem isOpen_cc_fibre [Smooth G.hom] (t : S) (he : (η[G] : 𝟙_ (Over S) ⟶ G).left t ∈ G.hom ⁻¹' {t}) :
    IsOpen (connectedComponent (⟨_, he⟩ : G.hom ⁻¹' {t})) := by
  let φ := G.hom.fiberHomeo t
  let φF := G.hom.fiberToSpecResidueField t
  have hsm : Smooth φF := show Smooth (pullback.snd G.hom (S.fromSpecResidueField t)) from inferInstance
  have hnb : ∀ y : G.hom ⁻¹' {t}, ∃ W : Set (G.hom ⁻¹' {t}), IsOpen W ∧ _root_.IsPreconnected W ∧ y ∈ W := by
    intro y
    obtain ⟨V, hVo, -, hVi, hyV⟩ := @SGA3IdComp.exists_irred_nbhd_of_smooth _ _ _ φF hsm (φ.symm y)
    refine ⟨φ '' V, φ.isOpenMap V hVo, hVi.isPreconnected.image _ φ.continuous.continuousOn, ?_⟩
    exact ⟨φ.symm y, hyV, φ.apply_symm_apply y⟩
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨W, hWo, hWc, hzW⟩ := hnb z
  refine ⟨W, ?_, hWo, hzW⟩
  rw [connectedComponent_eq hz]
  exact hWc.subset_connectedComponent hzW

/-- Over a closed point `t`, the points of `G_t` outside the identity component form a closed set of `G`. -/
theorem isClosed_fibre_diff [Smooth G.hom] (t : S) (ht : IsClosed ({t} : Set S)) :
    IsClosed (G.hom ⁻¹' {t} \ connectedComponentIn (G.hom ⁻¹' {t}) ((η[G] : 𝟙_ (Over S) ⟶ G).left t)) := by
  have he : (η[G] : 𝟙_ (Over S) ⟶ G).left t ∈ G.hom ⁻¹' {t} := SGA3IdComp.hom_e G t
  have hF : IsClosed (G.hom ⁻¹' {t}) := ht.preimage G.hom.continuous
  rw [connectedComponentIn_eq_image he]
  have : G.hom ⁻¹' {t} \ Subtype.val '' connectedComponent (⟨_, he⟩ : G.hom ⁻¹' {t}) =
      Subtype.val '' (connectedComponent (⟨_, he⟩ : G.hom ⁻¹' {t}))ᶜ := by
    ext x
    constructor
    · rintro ⟨hx, hx'⟩
      exact ⟨⟨x, hx⟩, fun h => hx' ⟨_, h, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      rintro ⟨y', hy', hyy'⟩
      exact hy (Subtype.ext hyy' ▸ hy')
  rw [this]
  exact hF.isClosedMap_subtype_val _ (isOpen_cc_fibre G t he).isClosed_compl

/-- **`G⁰` is open when the fibres off a finite set of closed points are preconnected.** -/
theorem isOpen_idCompSet_of_finite [Smooth G.hom] (T : Set S) (hT : T.Finite)
    (hTc : ∀ t ∈ T, IsClosed ({t} : Set S))
    (hpre : ∀ t ∉ T, _root_.IsPreconnected (G.hom ⁻¹' {t})) : IsOpen (idCompSet G) := by
  have hc : (idCompSet G)ᶜ = ⋃ t ∈ T,
      (G.hom ⁻¹' {t} \ connectedComponentIn (G.hom ⁻¹' {t}) ((η[G] : 𝟙_ (Over S) ⟶ G).left t)) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_diff, Set.mem_preimage,
      Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hx
      refine ⟨G.hom x, ?_, rfl, hx⟩
      by_contra hT'
      apply hx
      show x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G] : 𝟙_ (Over S) ⟶ G).left (G.hom x))
      exact (hpre _ hT').subset_connectedComponentIn (SGA3IdComp.hom_e G _) le_rfl rfl
    · rintro ⟨t, -, rfl, hx⟩
      exact hx
  rw [← isClosed_compl_iff, hc]
  exact hT.isClosed_biUnion fun t ht => isClosed_fibre_diff G t (hTc t ht)

end SGA3Nbhd
