import ZInQKernel.Contrib.OneProof.PazukiFixedQuasiFinite
import ZInQKernel.Contrib.OneProof.PazukiPicardInvolution

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

-- Start with a complex point of the actual scheme equalizer, over the identity
-- embedding of the geometric ground field. Supply the two DZQ Picard inputs.
-- Multiplicativity, the inverse action and local quasi-finiteness are derived.
example (hrep : T09Pic.PicRepresentableAbVar) (hzero : PicZeroChar0.PicZeroAbVar0)
    (A : PkgI3.AbVar ℂ) {P : Over (Spec (.of ℂ))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P)
    (B : PkgI3.AbVar ℂ) (j : B.X ⟶ P) (hj : T09Pic.IsPicZero rep B j) :
    let D := T09Pic.dualP rep (GrpObj.inv (X := A.X))
    ∀ s : Spec (.of ℂ) ⟶ equalizer D.left (𝟙 P.left),
      s ≫ (equalizer.ι D.left (𝟙 P.left) ≫ P.hom) = 𝟙 _ →
      (equalizer.ι D.left (𝟙 P.left) ≫ P.hom).QuasiFiniteAt (s (IsLocalRing.closedPoint ℂ)) := by
  let D := T09Pic.dualP rep (GrpObj.inv (X := A.X))
  let i := equalizer.ι D.left (𝟙 P.left)
  change ∀ s : Spec (.of ℂ) ⟶ equalizer D.left (𝟙 P.left),
    s ≫ (i ≫ P.hom) = 𝟙 _ → (i ≫ P.hom).QuasiFiniteAt (s (IsLocalRing.closedPoint ℂ))
  intro s hs
  let r : 𝟙_ (Over (Spec (.of ℂ))) ⟶ P :=
    Over.homMk (s ≫ i) (by rw [Category.assoc]; exact hs)
  have hi : i ≫ D.left = i := by
    simpa only [Category.comp_id] using equalizer.condition D.left (𝟙 P.left)
  have hr : r ≫ D = r := by
    apply Over.OverMorphism.ext
    change (s ≫ i) ≫ D.left = s ≫ i
    rw [Category.assoc, hi]
  exact ZInQ.PazukiFixedQuasiFinite.picard_fixed_quasiFiniteAt_section A rep B j hj
    (ZInQ.PazukiPicardInvolution.dualP_isMonHom rep (GrpObj.inv (X := A.X)))
    (ZInQ.PazukiPicardInvolution.dualP_inv_on_picZero hrep hzero rep hj)
    r hr (s (IsLocalRing.closedPoint ℂ)) rfl

#print axioms ZInQ.PazukiPicardInvolution.dualP_isMonHom
#print axioms ZInQ.PazukiPicardInvolution.dualP_inv_on_picZero
#print axioms ZInQ.PazukiFixedQuasiFinite.picard_fixed_quasiFiniteAt_section
