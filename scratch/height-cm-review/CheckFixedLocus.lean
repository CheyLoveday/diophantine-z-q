import ZInQKernel.Contrib.OneProof.PazukiPicardFixedLocus
import Mathlib.Analysis.Complex.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

-- The geometric statement is tested over the ground field itself, for its
-- represented Picard pullback, without being given quasi-finiteness.
example {K : Type} [Field K] [NumberField K]
    (hrep : T09Pic.PicRepresentableAbVar) (hzero : PicZeroChar0.PicZeroAbVar0)
    (A : PkgI3.AbVar K) {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) :
    LocallyQuasiFinite (equalizer.ι (T09Pic.dualP rep (GrpObj.inv (X := A.X))).left
      (𝟙 P.left) ≫ P.hom) :=
  ZInQ.PazukiPicardFixedLocus.locallyQuasiFinite_fixedPicard hrep hzero A rep

-- Require the same complex point and a descended fixed point over a finite
-- extension, with the original field embedding recovered on the nose.
example {K : Type} [Field K] [NumberField K]
    (hrep : T09Pic.PicRepresentableAbVar) (hzero : PicZeroChar0.PicZeroAbVar0)
    (A : PkgI3.AbVar K) {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P)
    (z : Spec (CommRingCat.of ℂ) ⟶ P.left) (σ : K →+* ℂ)
    (hz : z ≫ P.hom = Spec.map (CommRingCat.ofHom σ))
    (hz' : z ≫ (T09Pic.dualP rep (GrpObj.inv (X := A.X))).left = z) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra K E) (_ : FiniteDimensional K E)
      (e : E →+* ℂ) (t : Spec (CommRingCat.of E) ⟶ P.left),
      e.comp (algebraMap K E) = σ ∧ t ≫ P.hom = Spec.map (CommRingCat.ofHom (algebraMap K E)) ∧
      t ≫ (T09Pic.dualP rep (GrpObj.inv (X := A.X))).left = t ∧
      z = Spec.map (CommRingCat.ofHom e) ≫ t :=
  ZInQ.PazukiPicardFixedLocus.fixedPicard_point_definedOver hrep hzero A rep z σ hz hz'

#print axioms ZInQ.PazukiPicardFixedLocus.locallyQuasiFinite_fixedPicard
#print axioms ZInQ.PazukiPicardFixedLocus.fixedPicard_point_definedOver
