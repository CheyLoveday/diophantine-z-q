import ZInQKernel.Contrib.OneProof.MumfordRigidity

set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.MumfordRigidity

open LeafQM.AV.R1UnivRigid PkgI3

/-- **LEAF (`𝒪_S ≅ p_*𝒪_X`).** -/
def PushforwardStructureSheaf : Prop :=
  ∀ (S X : Scheme.{0}) (p : X ⟶ S), IsLocallyNoetherian S → IsProper p → Smooth p →
    GeometricallyConnected p → ∀ U : S.Opens, Function.Bijective (p.app U)

theorem appLE_id_eq {T : Scheme.{0}} (g : T ⟶ T) (hg : g = 𝟙 T) (U : T.Opens)
    (e : U ≤ g ⁻¹ᵁ U) : g.appLE U U e = 𝟙 _ := by
  subst hg
  exact (Scheme.Hom.appLE_eq_app (𝟙 T)).trans (Scheme.Hom.id_app U)

/-- **Local rigidity** from `𝒪_S ≅ p_*𝒪_X`. -/
theorem eq_of_pushforward (hP : PushforwardStructureSheaf) {T X : Scheme.{0}}
    [IsLocallyNoetherian T] (p : X ⟶ T) [IsProper p] [Smooth p] [GeometricallyConnected p]
    (f' : X ⟶ X) (j : T ⟶ X) (hjp : j ≫ p = 𝟙 T)
    (hfib : ∀ t : T, ∃ y : X, ∀ x : X, p x = t → f' x = y) :
    f' = p ≫ j ≫ f' := by
  refine Scheme.hom_ext_of_forall f' (p ≫ j ≫ f') fun x => ?_
  obtain ⟨y, hy⟩ := hfib (p x)
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  have hZ : IsClosed (p '' ((f' ⁻¹ᵁ V : X.Opens) : Set X)ᶜ) :=
    p.isClosedMap _ (f' ⁻¹ᵁ V).isOpen.isClosed_compl
  have htZ : p x ∉ p '' ((f' ⁻¹ᵁ V : X.Opens) : Set X)ᶜ := by
    rintro ⟨x', hx', hpx'⟩
    exact hx' (show f' x' ∈ V by rw [hy x' hpx']; exact hyV)
  obtain ⟨U, hU, htU, hUZ⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨_, hZ.isOpen_compl⟩) (x := p x) htZ
  refine ⟨p ⁻¹ᵁ U, htU, ?_⟩
  have hW : p ⁻¹ᵁ U ≤ f' ⁻¹ᵁ V := fun x' hx' => by
    by_contra h
    exact hUZ hx' ⟨x', h, rfl⟩
  have hjU : U ≤ j ⁻¹ᵁ (p ⁻¹ᵁ U) := fun t ht => by
    change p (j t) ∈ U
    rw [← Scheme.Hom.comp_apply, hjp]
    exact ht
  have hWc : p ⁻¹ᵁ U ≤ (p ≫ j ≫ f') ⁻¹ᵁ V := fun x' hx' => hW (hjU hx')
  have : IsAffine V := hV
  rw [← Scheme.Hom.resLE_comp_ι f' hW, ← Scheme.Hom.resLE_comp_ι (p ≫ j ≫ f') hWc]
  congr 1
  apply ext_of_isAffine
  rw [Scheme.Hom.appTop, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Hom.resLE_app_top]
  congr 2
  have hbij := hP T X p inferInstance inferInstance inferInstance inferInstance U
  rw [Scheme.Hom.app_eq_appLE] at hbij
  have hiso : IsIso (p.appLE U (p ⁻¹ᵁ U) le_rfl) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hbij
  have h1 : p.appLE U (p ⁻¹ᵁ U) le_rfl ≫ j.appLE (p ⁻¹ᵁ U) U hjU = 𝟙 _ := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact appLE_id_eq _ hjp _ _
  have h2 : j.appLE (p ⁻¹ᵁ U) U hjU ≫ p.appLE U (p ⁻¹ᵁ U) le_rfl = 𝟙 _ := by
    rw [IsIso.eq_inv_of_hom_inv_id h1, IsIso.inv_hom_id]
  have e1 := Scheme.Hom.appLE_comp_appLE j f' V (p ⁻¹ᵁ U) U hW hjU
  have e2 := Scheme.Hom.appLE_comp_appLE p (j ≫ f') V U (p ⁻¹ᵁ U)
    (fun t ht => hW (hjU ht)) le_rfl
  rw [← e1] at e2
  rw [← e2, Category.assoc, h2, Category.comp_id]

end ZInQ.Contrib.MumfordRigidity
