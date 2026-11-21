import ZInQKernel.OneProof.H.TailB

/-! Descent of local quasi-finiteness without a quasi-compactness assumption on
the entire fixed locus. The proof uses Jack's finite-fibre descent on each
affine member of the source cover. -/

namespace ZInQ.PazukiQuasiFiniteDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

/-- A locally finite type scheme over a quasi-separated base is locally
quasi-finite when its pullback to a surjective cover is locally quasi-finite.
The source can have infinitely many components. -/
theorem locallyQuasiFinite_of_surjective_baseChange
    {X Y S : Scheme} [QuasiSeparatedSpace S] (p : X ⟶ S) (g : Y ⟶ S)
    [Surjective g] [LocallyOfFiniteType p] [LocallyQuasiFinite (pullback.snd p g)] :
    LocallyQuasiFinite p := by
  apply (IsZariskiLocalAtSource.iff_of_openCover X.affineCover).mpr
  intro i
  let u := X.affineCover.f i
  haveI : IsOpenImmersion u := inferInstanceAs (IsOpenImmersion (X.affineCover.f i))
  haveI : QuasiCompact (u ≫ p) := inferInstance
  haveI : LocallyQuasiFinite (pullback.snd (u ≫ p) g) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd p g u]
    infer_instance
  exact FS1Descend.locallyQuasiFinite_of_isPullback (IsPullback.of_hasPullback (u ≫ p) g).flip

/-- Apply descent directly to the scheme equalizer used for the theta point.
Only local finite type of the ambient parameter scheme is needed downstairs.
The input upstairs concerns the scalar extension of this very equalizer. -/
theorem fixedLocus_quasiFiniteAt_of_field_extension
    {K F : Type} [Field K] [Field F] [Algebra K F] {P : Scheme}
    (p : P ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p] (a : P ⟶ P)
    (geom : LocallyQuasiFinite
      (pullback.snd (equalizer.ι a (𝟙 P) ≫ p)
        (Spec.map (CommRingCat.ofHom (algebraMap K F)))))
    (x : ↑(equalizer a (𝟙 P))) :
    (equalizer.ι a (𝟙 P) ≫ p).QuasiFiniteAt x := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap K F))
  let f := equalizer.ι a (𝟙 P) ≫ p
  haveI : Surjective g := (FS1Descend.specMap_flat_surjective K F).2
  haveI : LocallyQuasiFinite (pullback.snd f g) := geom
  haveI : LocallyOfFiniteType f := inferInstanceAs (LocallyOfFiniteType (equalizer.ι a (𝟙 P) ≫ p))
  haveI : LocallyQuasiFinite f := locallyQuasiFinite_of_surjective_baseChange f g
  exact f.quasiFiniteAt x

end ZInQ.PazukiQuasiFiniteDescent
