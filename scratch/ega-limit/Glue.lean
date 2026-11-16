import ZInQKernel.Contrib.SpreadOut.Spread
import ZInQKernel.Contrib.CloudW01Spread.Smooth
import ZInQKernel.Contrib.CloudW01Spread.FinitePresentation
import ZInQKernel.Contrib.CloudW06PoincareRigidity.AdjoinFinset
import ZInQKernel.Contrib.OneProof.EGAProperLimit.StacksFrontier.AlgebraicGeometry.ProperLimitStage.Basic
import ZInQKernel.Contrib.OneProof.EGAProperLimit.StacksFrontier.AlgebraicGeometry.Limits.ChowLemmaNoetherian0200
import ZInQKernel.Contrib.OneProof.EGAProperLimit.StacksFrontier.AlgebraicGeometry.SegreProdIso.Main

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.EGAProperLimit

universe u

/-- Stacks 01WD in the form `HasSegreEmbeddings` (existence of a receiving projective space). -/
theorem hasSegreEmbeddings (S : Scheme.{u}) : HasSegreEmbeddings S := by
  intro n m
  obtain ⟨f, hf, hcomm⟩ := Stacks.AlgebraicGeometry.SegreProdIso.exists_segreEmbedding n m S
  exact ⟨n * m + n + m, f, hf, hcomm⟩


/-- A property respecting isomorphisms holds for the base change of `p` along `g` exactly when it
holds for the given second projection of a cartesian square. -/
theorem prop_pullbackSnd_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X Y Z W : Scheme.{u}} {fst : X ⟶ Y} {snd : X ⟶ W} {p : Y ⟶ Z} {g : W ⟶ Z}
    (h : IsPullback fst snd p g) : P (pullback.snd p g) ↔ P snd := by
  rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso (P := P)]

open ZInQ.Contrib.CloudW06PoincareRigidity in
/-- **Chow's lemma over an affine base, for morphisms of finite presentation** (glue).  The
conclusion of Stacks 0202 for a separated morphism of finite presentation `f : X ⟶ T` with `T`
affine: approximate `Γ(T, ⊤)` by its finitely generated `ℤ`-subalgebras, descend `f` to a stage
(Stacks 01ZM (1)), make it separated (Stacks 01ZQ), apply Chow's lemma over the Noetherian affine
stage (Stacks 0200) and base change back. -/
theorem hasChowModification_of_isAffine {X T : Scheme.{0}} (f : X ⟶ T) [IsAffine T]
    [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    HasChowModification f := by
  let D' := AdjoinFinset.specDiagram ℤ Γ(T, ⊤)
  let c' := AdjoinFinset.specCone ℤ Γ(T, ⊤)
  have hc' : IsLimit c' := AdjoinFinset.isLimitSpecCone ℤ Γ(T, ⊤)
  let e : T ≅ c'.pt := T.isoSpec
  let f' : X ⟶ c'.pt := f ≫ e.hom
  haveI : IsSeparated f' := by dsimp [f']; infer_instance
  have hf' : FinitePresentation f' := ⟨inferInstance, inferInstance, inferInstance⟩
  haveI hD1 : ∀ {i j : (Finset Γ(T, ⊤))ᵒᵖ} (g : i ⟶ j), IsAffineHom (D'.map g) := fun g => by
    dsimp [D', AdjoinFinset.specDiagram]; infer_instance
  haveI hD4 : ∀ i, IsAffine (D'.obj i) := fun i => by
    dsimp [D', AdjoinFinset.specDiagram]; infer_instance
  haveI hD2 : ∀ i, CompactSpace (D'.obj i) := fun i => by haveI := hD4 i; infer_instance
  haveI hD3 : ∀ i, QuasiSeparatedSpace (D'.obj i) := fun i => by haveI := hD4 i; infer_instance
  obtain ⟨i, Y, p, g, hp, hpb⟩ :=
    LimitDescent.exists_isPullback_of_finitePresentation_of_essentiallySmall D' c' hc' f' hf'
  haveI : LocallyOfFinitePresentation p := hp.1
  haveI : QuasiCompact p := hp.2.1
  haveI : QuasiSeparated p := hp.2.2
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  haveI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  -- Stacks 01ZQ: `p` becomes separated at a later stage.
  let τ : Over.mk p ⟶ Over.mk (𝟙 (D'.obj i)) := Over.homMk p
  haveI : CompactSpace (Over.mk (𝟙 (D'.obj i))).left := hD2 i
  haveI : QuasiSeparatedSpace (Over.mk (𝟙 (D'.obj i))).left := hD3 i
  haveI : CompactSpace (Over.mk p).left := inferInstanceAs (CompactSpace Y)
  haveI : QuasiSeparatedSpace (Over.mk p).left := inferInstanceAs (QuasiSeparatedSpace Y)
  haveI : IsSeparated ((Over.pullback (c'.π.app i)).map τ).left := by
    refine (CloudW01Spread.pullback_to_identity_iff (@IsSeparated) (c'.π.app i) (Over.mk p)).2 ?_
    exact (prop_pullbackSnd_iff (@IsSeparated) hpb).2 inferInstance
  obtain ⟨j, a, hsep⟩ :=
    exists_isSeparated_baseChange_of_isLimit D' c' i (Over.mk p) (Over.mk (𝟙 (D'.obj i))) τ hc'
  haveI : IsSeparated (pullback.snd p (D'.map a)) :=
    (CloudW01Spread.pullback_to_identity_iff (@IsSeparated) (D'.map a) (Over.mk p)).1 hsep
  -- Stacks 0200 over the Noetherian affine stage `Spec ℤ[s]`.
  haveI : IsNoetherianRing (Algebra.adjoin ℤ ((Opposite.unop j : Finset Γ(T, ⊤)) : Set Γ(T, ⊤))) :=
    Algebra.FiniteType.isNoetherianRing ℤ _
  haveI : IsNoetherian (D'.obj j) := by
    dsimp [D', AdjoinFinset.specDiagram, AdjoinFinset.diagram]; infer_instance
  have hchow : HasChowModification (pullback.snd p (D'.map a)) :=
    hasChowModification_of_hasSegreEmbeddings (hasSegreEmbeddings _) _
  -- Base change back to `Spec Γ(T, ⊤)`, then along `T ≅ Spec Γ(T, ⊤)`.
  have hw : c'.π.app j ≫ D'.map a = c'.π.app i := c'.w a
  have hsq : IsPullback (pullback.lift g (f' ≫ c'.π.app j)
      (by rw [Category.assoc, hw]; exact hpb.w)) f' (pullback.snd p (D'.map a)) (c'.π.app j) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p (D'.map a))
    rw [pullback.lift_fst, hw]
    exact hpb
  have hchow' : HasChowModification f' := HasChowModification.of_isPullback hsq hchow
  exact HasChowModification.of_isPullback
    (IsPullback.of_horiz_isIso (fst := 𝟙 X) (snd := f) (f := f') (g := e.hom)
      (CommSq.mk (by simp [f']))) hchow'

end ZInQ.Contrib.EGAProperLimit
