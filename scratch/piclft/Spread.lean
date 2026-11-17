import ZInQKernel.Contrib.OneProof.PicDictionary
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Limits.Objects
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Limits.FiniteMaps
import ZInQKernel.Contrib.CloudW06PoincareRigidity.AdjoinFinset

/-! # piclft (III): spreading out invertible sheaves along directed inverse limits -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite
open Scheme.Modules

set_option linter.style.haveILetI false

namespace PicLFT

section Triv

variable {X Y : Scheme.{0}}

/-- `M` is trivial on the open `U`. -/
def Triv (M : X.Modules) (U : X.Opens) : Prop :=
  Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

lemma triv_of_iso {M N : X.Modules} (e : M ≅ N) {U : X.Opens} (h : Triv M U) : Triv N U :=
  ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ h.some⟩

lemma triv_mono {M : X.Modules} {U U' : X.Opens} (hle : U' ≤ U) (h : Triv M U) : Triv M U' :=
  ⟨(pullbackCompOfEq (X.homOfLE hle) U.ι U'.ι (X.homOfLE_ι hle) M).symm ≪≫
    (Scheme.Modules.pullback (X.homOfLE hle)).mapIso h.some ≪≫ pullbackObjUnitIso _⟩

lemma triv_pullback (f : Y ⟶ X) {M : X.Modules} {U : X.Opens} (h : Triv M U) :
    Triv ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) :=
  ⟨pullbackCompOfEq (f ⁻¹ᵁ U).ι f _ rfl M ≪≫
    (pullbackCompOfEq (f ∣_ U) U.ι ((f ⁻¹ᵁ U).ι ≫ f) (morphismRestrict_ι f U) M).symm ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso h.some ≪≫ pullbackObjUnitIso _⟩

end Triv

/-! ## (L2) triviality on one affine open descends to a finite stage -/

theorem triv_stage {I : Type} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{0}) [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : I) (W : (D.obj (op i)).Opens) (hW : IsAffineOpen W)
    (M : (D.obj (op i)).Modules) [M.IsFinitePresentation]
    (hT : Triv ((Scheme.Modules.pullback (c.π.app (op i))).obj M) (c.π.app (op i) ⁻¹ᵁ W)) :
    ∃ (j : I) (h : i ≤ j),
      Triv ((Scheme.Modules.pullback (D.map (homOfLE h).op)).obj M) (D.map (homOfLE h).op ⁻¹ᵁ W) := by
  sorry

/-! ## (L3) invertibility descends to a finite stage -/

theorem invAtStage {I : Type} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{0}) [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] (c : Cone D) (hc : IsLimit c) (i0 : I)
    (M0 : (D.obj (op i0)).Modules) [M0.IsFinitePresentation]
    (hL : ((Scheme.Modules.pullback (c.π.app (op i0))).obj M0).IsInvertible) :
    ∃ (j : I) (h : i0 ≤ j), ((Scheme.Modules.pullback (D.map (homOfLE h).op)).obj M0).IsInvertible := by
  classical
  let Mj : ∀ j : I, i0 ≤ j → (D.obj (op j)).Modules := fun j h => (Scheme.Modules.pullback (D.map (homOfLE h).op)).obj M0
  have hMcomp : ∀ (j k : I) (hj : i0 ≤ j) (hjk : j ≤ k),
      Nonempty ((Scheme.Modules.pullback (D.map (homOfLE hjk).op)).obj (Mj j hj) ≅ Mj k (hj.trans hjk)) :=
    fun j k hj hjk => ⟨pullbackCompOfEq _ _ _ (by rw [← D.map_comp]; rfl) M0⟩
  have hMlim : ∀ (j : I) (hj : i0 ≤ j),
      Nonempty ((Scheme.Modules.pullback (c.π.app (op j))).obj (Mj j hj) ≅ (Scheme.Modules.pullback (c.π.app (op i0))).obj M0) :=
    fun j hj => ⟨pullbackCompOfEq _ _ _ (c.w _) M0⟩
  have hgood : ∀ x : c.pt, ∃ (j : I) (hj : i0 ≤ j) (O : (D.obj (op j)).Opens),
      Triv (Mj j hj) O ∧ x ∈ c.π.app (op j) ⁻¹ᵁ O := by
    intro x
    obtain ⟨U, hxU, hU⟩ := (isInvertible_iff_forall_exists_pullback_unit _).1 hL x
    obtain ⟨_, ⟨i, V, hV, rfl⟩, hxV, hVU⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (isBasis_preimage_isAffineOpen D c hc)) hxU
    obtain ⟨k, hk0, hki⟩ := exists_ge_ge i0 i.unop
    let t := D.map (homOfLE hki).op
    have hpre : c.π.app (op k) ⁻¹ᵁ (t ⁻¹ᵁ V) = c.π.app i ⁻¹ᵁ V := by
      rw [← Scheme.Hom.comp_preimage]
      exact congrArg (· ⁻¹ᵁ V) (c.w (homOfLE hki).op)
    have hT : Triv ((Scheme.Modules.pullback (c.π.app (op k))).obj (Mj k hk0)) (c.π.app (op k) ⁻¹ᵁ (t ⁻¹ᵁ V)) := by
      rw [hpre]
      exact triv_of_iso (hMlim k hk0).some.symm (triv_mono hVU hU)
    obtain ⟨j, hkj, hTj⟩ := triv_stage D c hc k (t ⁻¹ᵁ V) (hV.preimage t) (Mj k hk0) hT
    refine ⟨j, hk0.trans hkj, D.map (homOfLE hkj).op ⁻¹ᵁ (t ⁻¹ᵁ V),
      triv_of_iso (hMcomp k j hk0 hkj).some hTj, ?_⟩
    have : c.π.app (op j) ⁻¹ᵁ (D.map (homOfLE hkj).op ⁻¹ᵁ (t ⁻¹ᵁ V)) = c.π.app (op k) ⁻¹ᵁ (t ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage]
      exact congrArg (· ⁻¹ᵁ (t ⁻¹ᵁ V)) (c.w (homOfLE hkj).op)
    rw [this, hpre]; exact hxV
  choose j hj O hOT hxO using hgood
  haveI : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((c.π.app (op (j x)) ⁻¹ᵁ O x : c.pt.Opens) : Set c.pt))
    (fun x => (show c.pt.Opens from c.π.app (op (j x)) ⁻¹ᵁ O x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxO x⟩)
  obtain ⟨m, hm⟩ := (insert i0 (F.image j)).exists_le
  have hm0 : i0 ≤ m := hm _ (Finset.mem_insert_self _ _)
  have hjm : ∀ x ∈ F, j x ≤ m := fun x hx => hm _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx))
  let O' : F → (D.obj (op m)).Opens := fun x => D.map (homOfLE (hjm x.1 x.2)).op ⁻¹ᵁ O x.1
  have hO'T : ∀ x : F, Triv (Mj m hm0) (O' x) := fun x =>
    triv_of_iso (hMcomp _ _ _ (hjm x.1 x.2)).some (triv_pullback _ (hOT x.1))
  have hcov : c.π.app (op m) ⁻¹ᵁ (⨆ x : F, O' x) = ⊤ := by
    rw [Scheme.Hom.preimage_iSup, eq_top_iff]
    intro y _
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ y))
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, ?_⟩
    have : c.π.app (op m) ⁻¹ᵁ O' ⟨x, hx⟩ = c.π.app (op (j x)) ⁻¹ᵁ O x := by
      rw [← Scheme.Hom.comp_preimage]
      exact congrArg (· ⁻¹ᵁ O x) (c.w (homOfLE (hjm x hx)).op)
    rw [this]; exact hyx
  obtain ⟨j', f, hf⟩ := exists_map_eq_top D c hc (i := op m) _ hcov
  have hmj : m ≤ j'.unop := leOfHom f.unop
  have hfeq : f = (homOfLE hmj).op := Subsingleton.elim _ _
  refine ⟨j'.unop, hm0.trans hmj, ?_⟩
  apply (isInvertible_iff_forall_exists_pullback_unit _).2
  intro y
  have hy : y ∈ D.map f ⁻¹ᵁ (⨆ x : F, O' x) := by rw [hf]; trivial
  rw [Scheme.Hom.preimage_iSup] at hy
  obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine ⟨D.map f ⁻¹ᵁ O' x, hx, ?_⟩
  have := triv_of_iso (hMcomp m j'.unop hm0 hmj).some (triv_pullback (D.map (homOfLE hmj).op) (hO'T x))
  rw [hfeq]
  exact this

end PicLFT
