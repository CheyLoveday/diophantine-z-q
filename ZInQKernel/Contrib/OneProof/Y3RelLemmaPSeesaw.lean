import ZInQKernel.Contrib.OneProof.Y3RelLemmaP
import ZInQKernel.Contrib.CloudR2Poincare.L1.ReducedGlobalSeesaw
import ZInQKernel.Contrib.CloudR2Poincare.L2.FpqcNormalizedDetection

/-!
# Fibre detection and the native reduced local seesaw

A geometric base fibre of the pair contains the geometric fibres of its
second projection. Faithfully flat descent then gives actual residue-fibre
triviality for the projection. On a reduced base the native seesaw turns
this into local triviality over the second factor.
-/

noncomputable section

namespace Y3LemmaP

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM Y3Fix
open ZInQ.Contrib.CloudR2Poincare
open ZInQ.Contrib.CloudR2Poincare.L1 (groupUnit_over)
open scoped CategoryTheory.Obj MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

/-- Every geometric field-base change of a smooth geometrically connected
morphism is integral. -/
theorem geometricallyIntegral_of_smooth_geometricallyConnected {X S : Scheme.{0}}
    (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] : GeometricallyIntegral f := by
  refine ⟨fun k _ s Y a b h => ?_⟩
  have hb : Smooth b := MorphismProperty.of_isPullback h inferInstance
  have hc : GeometricallyConnected b := MorphismProperty.of_isPullback h inferInstance
  have hd := SGRSplit.smoothGeomConnIntegral k Y b hb hc
  exact hd.geometrically_isIntegral (𝟙 _) (𝟙 _) b (IsPullback.id_horiz b)

/-- Over a field, triviality after extension to the algebraic closure
descends for the actual Picard class of a pointed proper geometrically
integral scheme. -/
theorem pic_eq_one_of_algClosure {k : Type} [Field k] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [GeometricallyIntegral f]
    (σ : Spec (CommRingCat.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (P : X.Pic)
    (h : Scheme.Pic.map (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) P = 1) :
    P = 1 := by
  let q := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let T : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 _)
  let U : Over (Spec (CommRingCat.of k)) := Over.mk q
  let d : U ⟶ T := Over.homMk q (by simp [T, U])
  haveI : Flat d.left := by
    change Flat q
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI : Surjective d.left :=
    ⟨fun z => ⟨IsLocalRing.closedPoint _, Subsingleton.elim (α := Spec (CommRingCat.of k)) _ _⟩⟩
  haveI : QuasiCompact d.left := by change QuasiCompact q; infer_instance
  let j := pullback.fst f T.hom
  haveI : IsIso j := by change IsIso (pullback.fst f (𝟙 _)); infer_instance
  apply L1.pic_map_injective_of_isIso j
  rw [Scheme.Pic.map_one]
  haveI : Subsingleton T.left.Pic :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)).Pic)
  apply (L2.normalizedPicard_eq_one_iff_fpqc_pullback f σ hσ d (Scheme.Pic.map j P)
    (Subsingleton.elim (α := T.left.Pic) _ _)).mp
  have hcomp : JacobianChallenge.baseChangeMap f d ≫ j = pullback.fst f q :=
    JacobianChallenge.baseChangeMap_fst f d
  rw [← Scheme.Pic.map_comp, hcomp]
  exact h

/-- Triviality on the geometric base fibres of the pair gives triviality on
each residue fibre of the projection to the second factor. -/
theorem residueFibre_eq_one_of_geometricPairClass {S : Scheme.{0}} (A : Over S) [MonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    (P : (A ⊗ A).left.Pic)
    (hP : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S),
      geometricPairClass A s P = 1)
    (a : A.left) :
    Scheme.Pic.map ((pullback.snd A.hom A.hom).fiberι a) P = 1 := by
  let p := pullback.snd A.hom A.hom
  let k := A.left.residueField a
  let r := A.left.fromSpecResidueField a
  let F := p.fiber a
  let f := p.fiberToSpecResidueField a
  let i := p.fiberι a
  let l := (lift (1 : A ⟶ A) (𝟙 A)).left
  have hl : l ≫ p = 𝟙 A.left := congrArg Over.Hom.left
    (lift_snd (1 : A ⟶ A) (𝟙 A))
  let σ : Spec k ⟶ F := pullback.lift (r ≫ l) (𝟙 _)
    (by rw [Category.assoc, hl, Category.comp_id, Category.id_comp])
  have hσ : σ ≫ f = 𝟙 _ := pullback.lift_snd _ _ _
  letI : GeometricallyIntegral A.hom := geometricallyIntegral_of_smooth_geometricallyConnected A.hom
  haveI : IsProper f := by change IsProper (pullback.snd p r); dsimp [p]; infer_instance
  haveI : GeometricallyIntegral f := by
    change GeometricallyIntegral (pullback.snd p r)
    dsimp [p]
    infer_instance
  apply pic_eq_one_of_algClosure f σ hσ
  let q := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let s := q ≫ r ≫ A.hom
  let A' := (Over.pullback s).obj A
  let v := pullback.fst f q ≫ i
  let t := pullback.snd f q
  have hv : v ≫ p = t ≫ q ≫ r := by
    dsimp only [v, t]
    rw [Category.assoc, Scheme.Hom.fiber_fac, ← Category.assoc, pullback.condition,
      Category.assoc]
  have hw₂ : (v ≫ p) ≫ A.hom = t ≫ s := by rw [hv]; simp only [s, Category.assoc]
  have hw₁ : (v ≫ pullback.fst A.hom A.hom) ≫ A.hom = t ≫ s := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact hw₂
  let a₁ : Over.mk t ⟶ A' := Over.homMk (pullback.lift _ _ hw₁) (pullback.lift_snd _ _ _)
  let a₂ : Over.mk t ⟶ A' := Over.homMk (pullback.lift _ _ hw₂) (pullback.lift_snd _ _ _)
  have hfac : (lift a₁ a₂).left ≫ pairMap (A := A') (B := A) (g := s)
      (pullback.fst A.hom s) pullback.condition = v := by
    apply pullback.hom_ext
    · have h₁ : (lift a₁ a₂).left ≫ pullback.fst A'.hom A'.hom = a₁.left :=
        congrArg Over.Hom.left (lift_fst a₁ a₂)
      rw [Category.assoc, pairMap_fst, ← Category.assoc, h₁]
      exact pullback.lift_fst _ _ _
    · have h₂ : (lift a₁ a₂).left ≫ pullback.snd A'.hom A'.hom = a₂.left :=
        congrArg Over.Hom.left (lift_snd a₁ a₂)
      rw [Category.assoc, pairMap_snd, ← Category.assoc, h₂]
      exact pullback.lift_fst _ _ _
  change Scheme.Pic.map (pullback.fst f q) (Scheme.Pic.map i P) = 1
  rw [← Scheme.Pic.map_comp, ← show (lift a₁ a₂).left ≫ _ = pullback.fst f q ≫ i from hfac,
    Scheme.Pic.map_comp]
  change Scheme.Pic.map (lift a₁ a₂).left (geometricPairClass A s P) = 1
  rw [hP (AlgebraicClosure k) s, Scheme.Pic.map_one]

/-- On a reduced locally noetherian base, fibre agreement gives actual
Zariski-local equality of the pairings over the second factor. -/
theorem exists_open_pairClass_eq_of_geometricPairClass_eq {S : Scheme.{0}}
    [IsLocallyNoetherian S] [AlgebraicGeometry.IsReduced S]
    (A : QMAbSchemeP S) (P Q : (A.F ⊗ A.F).left.Pic)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S),
      geometricPairClass A.F s P = geometricPairClass A.F s Q) (a : A.F.left) :
    ∃ U : A.F.left.Opens, a ∈ U ∧
      Scheme.Pic.map ((pullback.snd A.F.hom A.F.hom ⁻¹ᵁ U).ι) P =
        Scheme.Pic.map ((pullback.snd A.F.hom A.F.hom ⁻¹ᵁ U).ι) Q := by
  letI := A.grp
  letI := A.proper
  letI := A.geomConn
  haveI : Smooth A.F.hom := by letI := A.smooth; exact SmoothOfRelativeDimension.smooth 2 _
  letI : GeometricallyIntegral A.F.hom := geometricallyIntegral_of_smooth_geometricallyConnected A.F.hom
  haveI : IsLocallyNoetherian A.F.left := LocallyOfFiniteType.isLocallyNoetherian A.F.hom
  haveI : AlgebraicGeometry.IsReduced A.F.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian A.F.hom
  let p := pullback.snd A.F.hom A.F.hom
  obtain ⟨M, hM, hMP⟩ := Scheme.Pic.exists_mk_eq (P / Q)
  letI := hM
  have hr (b : A.F.left) : Scheme.Pic.map (p.fiberι b) (Scheme.Pic.mk M) = 1 := by
    rw [hMP]
    apply residueFibre_eq_one_of_geometricPairClass A.F
    intro k _ _ s
    change Scheme.Pic.mapHom _ (P / Q) = 1
    rw [map_div]
    exact div_eq_one.mpr (h k s)
  obtain ⟨U, ha, ⟨e⟩⟩ := L1.exists_open_iso_unit_of_trivial_residue_fibres p M hr a
  refine ⟨U, ha, div_eq_one.mp ?_⟩
  change Scheme.Pic.mapHom (p ⁻¹ᵁ U).ι P / Scheme.Pic.mapHom (p ⁻¹ᵁ U).ι Q = 1
  rw [← map_div]
  change Scheme.Pic.map (p ⁻¹ᵁ U).ι (P / Q) = 1
  rw [← hMP, Scheme.Pic.map_mk]
  exact ((Scheme.Pic.mk_eq_mk_iff _ _).mpr ⟨e⟩).trans Scheme.Pic.one_eq_mk_unit.symm

/-- Over a field the native normalized global seesaw detects equality of
normalized pairings from their geometric base restrictions. -/
theorem pairClass_eq_over_field_of_geometricPairClass_eq {k : Type} [Field k]
    (A : QMAbSchemeP (Spec (CommRingCat.of k))) (P Q : (A.F ⊗ A.F).left.Pic)
    (hP : letI := A.grp; IsZeroAxisNormalized P)
    (hQ : letI := A.grp; IsZeroAxisNormalized Q)
    (h : ∀ (L : Type) [Field L] [IsAlgClosed L] (s : Spec (CommRingCat.of L) ⟶ _),
      geometricPairClass A.F s P = geometricPairClass A.F s Q) : P = Q := by
  letI := A.grp
  haveI := A.proper
  haveI := A.geomConn
  haveI : Smooth A.F.hom := by haveI := A.smooth; exact SmoothOfRelativeDimension.smooth 2 _
  haveI : GeometricallyIntegral A.F.hom := geometricallyIntegral_of_smooth_geometricallyConnected A.F.hom
  haveI : IsLocallyNoetherian A.F.left := LocallyOfFiniteType.isLocallyNoetherian A.F.hom
  haveI : AlgebraicGeometry.IsReduced A.F.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian A.F.hom
  apply div_eq_one.mp
  have hu := groupUnit_over A.F
  apply L1.normalizedPicardClass_eq_one_of_residueFibres_reduced A.F.hom η[A.F].left hu A.F
  · have hs : sectionBaseChange A.F.hom η[A.F].left hu A.F =
        (lift (1 : A.F ⟶ A.F) (𝟙 A.F)).left := by
      apply pullback.hom_ext
      · rw [sectionBaseChange_fst]
        exact (show _ = (1 : A.F ⟶ A.F).left from rfl).trans
          (congrArg Over.Hom.left (lift_fst (1 : A.F ⟶ A.F) (𝟙 A.F))).symm
      · rw [sectionBaseChange_snd]
        exact (congrArg Over.Hom.left (lift_snd (1 : A.F ⟶ A.F) (𝟙 A.F))).symm
    rw [hs]
    exact ((IsZeroAxisNormalized.div hP hQ) A.F (𝟙 A.F)).1
  · intro a
    apply residueFibre_eq_one_of_geometricPairClass A.F
    intro L _ _ s
    change Scheme.Pic.mapHom _ (P / Q) = 1
    rw [map_div]
    exact div_eq_one.mpr (h L s)

end Y3LemmaP

#print axioms Y3LemmaP.geometricallyIntegral_of_smooth_geometricallyConnected
#print axioms Y3LemmaP.pic_eq_one_of_algClosure
#print axioms Y3LemmaP.residueFibre_eq_one_of_geometricPairClass
#print axioms Y3LemmaP.exists_open_pairClass_eq_of_geometricPairClass_eq
#print axioms Y3LemmaP.pairClass_eq_over_field_of_geometricPairClass_eq
