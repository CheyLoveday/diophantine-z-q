import ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.AbelianVariety.RationalCurves
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Birational.ValuativeExtension
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Dimension

/-! # chevalley-free, step R: morphisms from `𝔾_m` to an abelian variety are constant -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry.ProjectiveLine AlgebraicGeometry.ProjectiveSpace ZInQ.SemiAbDescend

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ZInQ.ChevFree

section Rig

variable (K : Type) [Field K]

/-- `Spec K`. -/
abbrev PK : Scheme := Spec (CommRingCat.of K)

/-- The overlap `𝔾_m ⊆ ℙ¹_K` of the two standard charts. -/
abbrev Ov : Scheme := (relativeOverlap (PK K)).toScheme

/-- An element of `K` as a global section of `Spec K`. -/
abbrev secK (s : K) : Γ(PK K, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv s

theorem mem_overlap (s : Kˣ) (x : PK K) :
    normalized (𝟙 (PK K)) ⟨1⟩ (secK K s) x ∈ relativeOverlap (PK K) := by
  have hc : ∀ c : ULift.{0} (Fin 2),
      normalized (𝟙 (PK K)) ⟨1⟩ (secK K s) x ∈ standardOpen (ULift.{0} (Fin 2)) (PK K) c := by
    intro c
    change x ∈ normalized (𝟙 (PK K)) ⟨1⟩ (secK K s) ⁻¹ᵁ standardOpen (ULift.{0} (Fin 2)) (PK K) c
    rw [normalized, homOfSections_preimage_standardOpen]
    have hu : IsUnit (normalizedSections (source := PK K) ⟨1⟩ (secK K s) c) := by
      unfold normalizedSections
      split_ifs
      · exact isUnit_one
      · exact (s.isUnit.map _)
    rw [Scheme.basicOpen_of_isUnit _ hu]
    trivial
  exact ⟨hc ⟨0⟩, hc ⟨1⟩⟩

/-- The `K`-point `[s : 1]` of the overlap. -/
def ovPt (s : Kˣ) : PK K ⟶ Ov K :=
  IsOpenImmersion.lift (relativeOverlap (PK K)).ι (normalized (𝟙 (PK K)) ⟨1⟩ (secK K s)) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact mem_overlap K s x)

@[reassoc (attr := simp)]
theorem ovPt_ι (s : Kˣ) : ovPt K s ≫ (relativeOverlap (PK K)).ι = normalized (𝟙 (PK K)) ⟨1⟩ (secK K s) :=
  IsOpenImmersion.lift_fac ..

theorem ovPt_over (s : Kˣ) : ovPt K s ≫ overlapToBase K = 𝟙 (PK K) := by
  rw [overlapToBase, ovPt_ι_assoc, normalized_over]

theorem ovPt_coordinate (s : Kˣ) : (ovPt K s).appTop (scalingCoordinate K ⟨1⟩) = secK K s := by
  have chartEquation : ovPt K s ≫ ((relativeLine (PK K))).homOfLE
      (relativeOverlap_le_standardOpen (PK K) ⟨1⟩) =
      relativeChartPoint (𝟙 (PK K)) ⟨1⟩ (secK K s) := by
    apply (cancel_mono (standardOpen (ULift.{0} (Fin 2)) (PK K) ⟨1⟩).ι).mp
    simp
  rw [scalingCoordinate, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    chartEquation, relativeChartPoint_coordinate]

/-- `ℙ¹_K` is smooth of relative dimension one. -/
instance line_smooth : SmoothOfRelativeDimension 1 (relativeLine (PK K) ↘ PK K) := by
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} 1) (relativeChartCover (PK K))
  intro (c : ULift.{0} (Fin 2))
  change SmoothOfRelativeDimension 1
    ((standardOpen (ULift.{0} (Fin 2)) (PK K) c).ι ≫ relativeLine (PK K) ↘ PK K)
  rw [← standardOpenIso_hom_over]
  have : Nat.card {o : ULift.{0} (Fin 2) // o ≠ c} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨⟨c.down.rev⟩, ?_⟩⟩⟩
    · rcases a with ⟨⟨a⟩, ha⟩; rcases b with ⟨⟨b⟩, hb⟩; rcases c with ⟨c⟩
      ext; simp only [ne_eq, ULift.ext_iff] at ha hb ⊢; omega
    · rcases c with ⟨c⟩; simp only [ne_eq, ULift.ext_iff]; fin_cases c <;> decide
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension.{0} 1)]
  exact AffineSpace.smoothOfRelativeDimension_of_card_eq (n := {o : ULift.{0} (Fin 2) // o ≠ c})
    (PK K) this


variable {K}

theorem genericPoint_mem_overlap : genericPoint (relativeLine (PK K)) ∈ relativeOverlap (PK K) := by
  rw [← SetLike.mem_coe,
    (genericPoint_spec (relativeLine (PK K))).mem_open_set_iff (relativeOverlap (PK K)).isOpen]
  simpa using (Scheme.Opens.nonempty_iff _).mp (inferInstance : Nonempty (Ov K))

/-- `Spec K(ℙ¹) → 𝔾_m`. -/
abbrev ξg : Spec (relativeLine (PK K)).functionField ⟶ Ov K :=
  (relativeOverlap (PK K)).fromSpecStalkOfMem _ (genericPoint_mem_overlap (K := K))

theorem ξg_ι : ξg (K := K) ≫ (relativeOverlap (PK K)).ι = (relativeLine (PK K)).fromSpecFunctionField :=
  Scheme.Opens.fromSpecStalkOfMem_ι _ _ _

instance : IsDominant (ξg (K := K)) := by
  constructor
  let p : Spec (relativeLine (PK K)).functionField :=
    IsLocalRing.closedPoint ((relativeLine (PK K)).functionField)
  let z := (ξg (K := K)) p
  have hz : (relativeOverlap (PK K)).ι z = genericPoint (relativeLine (PK K)) := by
    show (relativeOverlap (PK K)).ι ((ξg (K := K)) p) = _
    rw [← Scheme.Hom.comp_apply, ξg_ι]
    exact Scheme.fromSpecStalk_closedPoint
  have hd : Dense ({z} : Set (Ov K)) := by
    rw [dense_iff_closure_eq,
      (relativeOverlap (PK K)).ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      Set.image_singleton, hz, genericPoint_closure]
    rfl
  exact hd.mono (by rintro _ rfl; exact ⟨_, rfl⟩)

/-- Every morphism `ℙ¹_K → B` to an abelian variety takes the same value at all `K`-points
(vendored `RationalCurves.eq_zero_comp`, commutativity from Mathlib). -/
theorem line_const (B : PkgI3.AbVar K) (E : relativeLineOver K ⟶ B.X)
    (a b : 𝟙_ (Over (PK K)) ⟶ relativeLineOver K) : a ≫ E = b ≫ E := by
  letI := B.grp
  haveI := B.proper
  haveI := B.smooth
  haveI := B.geomInt
  haveI : IsCommMonObj B.X := isCommMonObj_of_isProper_of_geometricallyIntegral B.X
  let V : AlgebraicGeometry.AbelianVariety K := ⟨CommGrp.mk B.X⟩
  have hE := AlgebraicGeometry.AbelianVariety.RationalCurves.eq_zero_comp V E
  have ha : a ≫ E = ProjectiveLine.zeroPointOver K ≫ E := by
    conv_lhs => rw [hE]
    rw [← Category.assoc, ← Category.assoc, Subsingleton.elim (a ≫ toUnit _) (𝟙 _), Category.id_comp]
  have hb : b ≫ E = ProjectiveLine.zeroPointOver K ≫ E := by
    conv_lhs => rw [hE]
    rw [← Category.assoc, ← Category.assoc, Subsingleton.elim (b ≫ toUnit _) (𝟙 _), Category.id_comp]
  rw [ha, hb]

/-- **Rigidity for `𝔾_m`**: a morphism from the overlap `𝔾_m ⊆ ℙ¹_K` to an abelian variety over `K` takes
the same value at all the points `[s : 1]`. -/
theorem overlap_const (B : PkgI3.AbVar K) (h : Ov K ⟶ B.X.left) (hh : h ≫ B.X.hom = overlapToBase K)
    (s t : Kˣ) : ovPt K s ≫ h = ovPt K t ≫ h := by
  letI : (B.X.left).Over (PK K) := ⟨B.X.hom⟩
  haveI : IsProper (B.X.left ↘ PK K) := B.proper
  haveI : B.X.left.IsSeparated := ⟨by
    rw [← terminal.comp_from B.X.hom]
    haveI : IsSeparated B.X.hom := inferInstanceAs (IsSeparated (B.X.left ↘ PK K))
    infer_instance⟩
  have hval : ∀ x, ValuationRing ((relativeLine (PK K)).presheaf.stalk x) :=
    Scheme.valuationRing_stalk (relativeLine (PK K) ↘ PK K)
  obtain ⟨E, hEo, hE⟩ := Scheme.exists_hom_of_valuationRing_stalk (base := PK K) hval (ξg ≫ h) (by
    change ξg ≫ h ≫ B.X.hom = _
    rw [hh, overlapToBase, ← Category.assoc, ξg_ι])
  have hEo' : E ≫ B.X.hom = relativeLine (PK K) ↘ PK K := hEo.comp_over
  have hagree : (relativeOverlap (PK K)).ι ≫ E = h := by
    apply ext_of_isDominant_of_isSeparated B.X.hom ?_ (ξg (K := K)) ?_
    · rw [Category.assoc, hEo', hh, overlapToBase]
    · rw [← Category.assoc, ξg_ι, hE]
  let Em : relativeLineOver K ⟶ B.X := Over.homMk E hEo'
  let pt : Kˣ → (𝟙_ (Over (PK K)) ⟶ relativeLineOver K) := fun s =>
    Over.homMk (ovPt K s ≫ (relativeOverlap (PK K)).ι) (by
      change (ovPt K s ≫ (relativeOverlap (PK K)).ι) ≫ relativeLine (PK K) ↘ PK K = 𝟙 _
      rw [Category.assoc, ← overlapToBase, ovPt_over])
  have := congrArg CommaMorphism.left (line_const B Em (pt s) (pt t))
  simp only [Over.comp_left, Over.homMk_left, Em, pt] at this
  rw [← hagree, ← Category.assoc, ← Category.assoc]
  simpa only [Category.assoc] using this

end Rig

end ZInQ.ChevFree
