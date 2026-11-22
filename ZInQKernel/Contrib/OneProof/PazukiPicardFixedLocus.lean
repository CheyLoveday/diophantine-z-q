import ZInQKernel.Contrib.OneProof.PazukiPicardBaseChange
import ZInQKernel.Contrib.OneProof.PazukiFixedEqualizerBaseChange
import ZInQKernel.Contrib.OneProof.PazukiFixedLocusCover
import ZInQKernel.Contrib.OneProof.PazukiQuasiFiniteDescent
import ZInQKernel.Contrib.OneProof.PazukiSymmetricDescent

/-! The actual Picard fixed locus in characteristic zero, and recovery of the
given field-valued point over a finite extension. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace ZInQ.PazukiPicardFixedLocus

/-- Under DZQ's Picard representability and characteristic-zero identity-component
inputs, the fixed locus of pullback by inversion is locally quasi-finite over K. -/
theorem locallyQuasiFinite_fixedPicard
    {K : Type} [Field K] [CharZero K]
    (hrep : T09Pic.PicRepresentableAbVar) (hzero : PicZeroChar0.PicZeroAbVar0)
    (A : PkgI3.AbVar K) {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) :
    LocallyQuasiFinite
      (equalizer.ι (T09Pic.dualP rep (GrpObj.inv (X := A.X))).left (𝟙 P.left) ≫ P.hom) := by
  let D := T09Pic.dualP rep (GrpObj.inv (X := A.X))
  let g := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  let R := PazukiPicardBaseChange.fullPicardRepresentation
    (IsPullback.of_hasPullback A.X.hom g) rep
  have hgeom := PazukiFixedLocusCover.picard_fixed_locallyQuasiFinite hrep hzero
    (A.baseChange (AlgebraicClosure K)) R
  have hD : (Over.pullback g).map D =
      T09Pic.dualP (A := A.baseChange (AlgebraicClosure K)) R
        (GrpObj.inv (X := (A.baseChange (AlgebraicClosure K)).X)) :=
    PazukiPicardBaseChange.dualP_inv_baseChange (L := AlgebraicClosure K) A rep
  have hfixed : LocallyQuasiFinite
      (equalizer.ι ((Over.pullback g).map D).left (𝟙 ((Over.pullback g).obj P).left) ≫
        ((Over.pullback g).obj P).hom) := by
    rw [hD]
    exact hgeom
  haveI : LocallyOfFiniteType P.hom := PicLFT.picLocFinType_proof K A P rep
  haveI : Surjective g := (HDec.FS1Descend.specMap_flat_surjective K (AlgebraicClosure K)).2
  haveI : LocallyQuasiFinite (pullback.snd (equalizer.ι D.left (𝟙 P.left) ≫ P.hom) g) :=
    PazukiFixedEqualizerBaseChange.locallyQuasiFinite_fixed_pullback D g hfixed
  exact PazukiQuasiFiniteDescent.locallyQuasiFinite_of_surjective_baseChange
    (equalizer.ι D.left (𝟙 P.left) ≫ P.hom) g

/-- The original point, its field embedding and its fixedness all descend to a
single finite extension of the number field. The endomorphism is the actual
represented Picard pullback. Quasi-finiteness is furnished by the preceding theorem. -/
theorem fixedPicard_point_definedOver
    {K F : Type} [Field K] [NumberField K] [Field F]
    (hrep : T09Pic.PicRepresentableAbVar) (hzero : PicZeroChar0.PicZeroAbVar0)
    (A : PkgI3.AbVar K) {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P)
    (s : Spec (CommRingCat.of F) ⟶ P.left) (σ : K →+* F)
    (hs : s ≫ P.hom = Spec.map (CommRingCat.ofHom σ))
    (hfixed : s ≫ (T09Pic.dualP rep (GrpObj.inv (X := A.X))).left = s) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra K E) (_ : FiniteDimensional K E)
      (e : E →+* F) (t : Spec (CommRingCat.of E) ⟶ P.left),
      e.comp (algebraMap K E) = σ ∧
      t ≫ P.hom = Spec.map (CommRingCat.ofHom (algebraMap K E)) ∧
      t ≫ (T09Pic.dualP rep (GrpObj.inv (X := A.X))).left = t ∧
      s = Spec.map (CommRingCat.ofHom e) ≫ t := by
  let D := (T09Pic.dualP rep (GrpObj.inv (X := A.X))).left
  haveI : LocallyQuasiFinite (equalizer.ι D (𝟙 P.left) ≫ P.hom) :=
    locallyQuasiFinite_fixedPicard hrep hzero A rep
  have hf : s ≫ D = s ≫ 𝟙 P.left := by simpa only [Category.comp_id] using hfixed
  exact PazukiSymmetricDescent.fixedPoint_numberField_factor P.hom D s σ hs hf
    ((equalizer.ι D (𝟙 P.left) ≫ P.hom).quasiFiniteAt _)

end ZInQ.PazukiPicardFixedLocus
