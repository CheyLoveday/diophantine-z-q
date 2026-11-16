import ZInQKernel.Contrib.OneProof.NeronExtLocal
import ZInQKernel.Contrib.OneProof.NeronExtAb
import ZInQKernel.Contrib.CloudW01Spread.StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion

/-! # neron-ext: spreading out a separated smooth scheme over `R_𝔭` -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry
open NumberField

namespace NeronExt

open GapBLR ZInQ.Contrib.SpreadOut

section Sep

/-- `X ×_Z T → T` is separated iff the base change of the diagonal of `X → Z` is a closed immersion. -/
theorem isSeparated_pb_iff {Z T : Scheme.{0}} (π : T ⟶ Z) (X : Over Z) :
    IsClosedImmersion ((Over.pullback π).map
      (Over.homMk (pullback.diagonal X.hom) (by simp) :
        Over.mk X.hom ⟶ Over.mk (pullback.snd X.hom X.hom ≫ X.hom))).left ↔
      IsSeparated ((Over.pullback π).obj (Over.mk X.hom)).hom := by
  have e1 : ((Over.pullback π).obj (Over.mk X.hom)).hom =
      (pullbackSymmetry X.hom π).hom ≫ pullback.fst π X.hom := by
    simp
  have hd := diagonal_pullback_fst π X.hom
  rw [e1, MorphismProperty.cancel_left_of_respectsIso (P := @IsSeparated)]
  constructor
  · intro h
    refine ⟨?_⟩
    rw [hd]
    infer_instance
  · intro h
    have h1 := h.isClosedImmersion_diagonal
    rw [hd] at h1
    have h2 : IsClosedImmersion (((Over.pullback π).map
      (Over.homMk (pullback.diagonal X.hom) (by simp) :
        Over.mk X.hom ⟶ Over.mk (pullback.snd X.hom X.hom ≫ X.hom))).left ≫
          (diagonalObjPullbackFstIso π X.hom).inv) :=
      (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) _ _).mp h1
    exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ _).mp h2

theorem isSeparated_of_iso {S : Scheme.{0}} {X Y : Over S} (e : X ≅ Y) [IsSeparated Y.hom] :
    IsSeparated X.hom := by
  rw [← Over.w e.hom]
  haveI : IsIso e.hom.left := ⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id]; rfl,
    by rw [← Over.comp_left, e.inv_hom_id]; rfl⟩
  infer_instance

end Sep

/-- Base change along equal maps. -/
noncomputable def pbCongr {A B : Scheme.{0}} {f g : A ⟶ B} (h : f = g) (X : Over B) :
    (Over.pullback f).obj X ≅ (Over.pullback g).obj X := by
  subst h; exact Iso.refl _

section SpreadSep

variable {R : Type} [CommRing R] {𝔭 : Ideal R} [𝔭.IsPrime] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭]
  [IsLocalization.AtPrime R𝔭 𝔭]

/-- **Spreading out a smooth separated quasi-compact `R_𝔭`-scheme** to some `R[1/s]`, `s ∉ 𝔭`
(EGA IV 8.8.2 (ii), 17.7.8 (ii) proved in `CloudW01Spread`, and the descent of closed immersions,
Stacks 01ZP, proved in `CloudW01Spread/StacksFrontier`, applied to the diagonal). -/
theorem exists_spread_sep (V : Over (Spec (CommRingCat.of R𝔭))) [Smooth V.hom] [IsSeparated V.hom]
    [QuasiCompact V.hom] :
    ∃ (a : (GapBLR.Idx 𝔭)ᵒᵖ) (W : Over ((specDiag 𝔭).obj a)), Smooth W.hom ∧ IsSeparated W.hom ∧
      QuasiCompact W.hom ∧ Nonempty ((Over.pullback ((specCone 𝔭 R𝔭).π.app a)).obj W ≅ V) := by
  let D := specDiag 𝔭
  let c := specCone 𝔭 R𝔭
  have hc : IsLimit c := specConeIsLimit 𝔭 R𝔭
  obtain ⟨i, Xi, hl, hq, hs, ⟨e⟩⟩ := EGAIV_8_8_2_ii_proof (GapBLR.Idx 𝔭) D c hc V inferInstance
    inferInstance inferInstance
  haveI := hl; haveI := hq; haveI := hs
  have hsm : Smooth ((Over.pullback (c.π.app i)).obj Xi).hom := smooth_of_iso e
  obtain ⟨j₁, a₁, hj₁⟩ := EGAIV_17_7_8_ii_proof (GapBLR.Idx 𝔭) D c hc i Xi hl hq hs hsm
  -- separatedness, via the diagonal
  haveI : CompactSpace Xi.left := QuasiCompact.compactSpace_of_compactSpace Xi.hom
  haveI : QuasiSeparatedSpace Xi.left := quasiSeparatedSpace_of_quasiSeparated Xi.hom
  let Y₀ : Over (D.obj i) := Over.mk (pullback.snd Xi.hom Xi.hom ≫ Xi.hom)
  haveI : QuasiCompact Y₀.hom := show QuasiCompact (pullback.snd Xi.hom Xi.hom ≫ Xi.hom) from inferInstance
  haveI : QuasiSeparated Y₀.hom :=
    show QuasiSeparated (pullback.snd Xi.hom Xi.hom ≫ Xi.hom) from inferInstance
  haveI : CompactSpace Y₀.left := QuasiCompact.compactSpace_of_compactSpace Y₀.hom
  haveI : QuasiSeparatedSpace Y₀.left := quasiSeparatedSpace_of_quasiSeparated Y₀.hom
  haveI : CompactSpace (Over.mk Xi.hom).left := ‹CompactSpace Xi.left›
  haveI : QuasiSeparatedSpace (Over.mk Xi.hom).left := ‹QuasiSeparatedSpace Xi.left›
  let f₀ : Over.mk Xi.hom ⟶ Y₀ := Over.homMk (pullback.diagonal Xi.hom) (by simp [Y₀])
  haveI : LocallyOfFiniteType f₀.left := by
    have : f₀.left ≫ pullback.fst Xi.hom Xi.hom = 𝟙 _ := by simp [f₀]
    haveI : LocallyOfFiniteType (f₀.left ≫ pullback.fst Xi.hom Xi.hom) := by
      rw [this]; infer_instance
    exact locallyOfFiniteType_of_comp f₀.left (pullback.fst Xi.hom Xi.hom)
  haveI : IsSeparated ((Over.pullback (c.π.app i)).obj (Over.mk Xi.hom)).hom :=
    isSeparated_of_iso e
  haveI : IsClosedImmersion ((Over.pullback (c.π.app i)).map f₀).left :=
    (isSeparated_pb_iff (c.π.app i) Xi).mpr inferInstance
  obtain ⟨j₂, a₂, hj₂⟩ := exists_isClosedImmersion_baseChange_of_isLimit D c hc i
    (Over.mk Xi.hom) Y₀ f₀
  have hsep₂ : IsSeparated ((Over.pullback (D.map a₂)).obj (Over.mk Xi.hom)).hom :=
    (isSeparated_pb_iff (D.map a₂) Xi).mp hj₂
  -- a common stage
  obtain ⟨k, b₁, b₂, -⟩ := IsCofiltered.cospan a₁ a₂
  let b : k ⟶ i := b₁ ≫ a₁
  have hb : b₂ ≫ a₂ = b := Subsingleton.elim _ _
  let W : Over (D.obj k) := (Over.pullback (D.map b)).obj Xi
  have eW₁ : W ≅ (Over.pullback (D.map b₁)).obj ((Over.pullback (D.map a₁)).obj Xi) :=
    eqToIso (by simp only [W, b, Functor.map_comp]) ≪≫ (Over.pullbackComp _ _).app Xi
  have eW₂ : W ≅ (Over.pullback (D.map b₂)).obj ((Over.pullback (D.map a₂)).obj (Over.mk Xi.hom)) :=
    eqToIso (by simp only [W, ← hb, Functor.map_comp]; rfl) ≪≫ (Over.pullbackComp _ _).app _
  refine ⟨k, W, ?_, ?_, ?_, ⟨?_⟩⟩
  · haveI : Smooth ((Over.pullback (D.map a₁)).obj Xi).hom := hj₁
    haveI : Smooth ((Over.pullback (D.map b₁)).obj ((Over.pullback (D.map a₁)).obj Xi)).hom :=
      show Smooth (pullback.snd _ _) from inferInstance
    exact smooth_of_iso eW₁
  · haveI := hsep₂
    haveI : IsSeparated ((Over.pullback (D.map b₂)).obj
        ((Over.pullback (D.map a₂)).obj (Over.mk Xi.hom))).hom :=
      show IsSeparated (pullback.snd _ _) from inferInstance
    exact isSeparated_of_iso eW₂
  · show QuasiCompact (pullback.snd _ _)
    infer_instance
  · exact (Over.pullbackComp (c.π.app k) (D.map b)).symm.app Xi ≪≫ pbCongr (c.w b) Xi ≪≫ e

end SpreadSep

end NeronExt
