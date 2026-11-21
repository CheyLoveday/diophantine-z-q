import ZInQKernel.Contrib.OneProof.PhiSurjCharZero
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Sites.SheafifyGrpMap

/-! Pullback by inversion on the represented Picard scheme and its identity component. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace ZInQ.PazukiPicardInvolution

open PkgI3 PkgI3.AbVar T09Pic PicDict

variable {K : Type} [Field K]

-- Keep the tensor law during sheafification of DZQ's existing pullback map.
private def picPresheafGroupMap {A : AbVar K} (f : A.X ⟶ A.X) :
    picardPresheafGrp A.X.hom ⟶ picardPresheafGrp A.X.hom where
  app T := GrpCat.ofHom (Scheme.Pic.mapHom (famMap f T.unop))
  naturality T U g := by
    apply GrpCat.hom_ext
    exact MonoidHom.ext ((picPresheafMap f).naturality_apply g)

/-- DZQ's represented dual pullback is a group homomorphism on the full relative
Picard scheme. This applies even when a test class has no global bundle representative. -/
theorem dualP_isMonHom {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (f : A.X ⟶ A.X) :
    letI := picardFunctorCommGrpObj A.X.hom rep
    IsMonHom (dualP rep f) := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  let s : picardFunctorGrp A.X.hom ⟶ picardFunctorGrp A.X.hom :=
    sheafifyGrpMap (Scheme.fppfTopology.over _) (picPresheafGroupMap f)
  let g := GrpObj.mapOfRepresentableBy (sourceFunctor := picardFunctorGrp A.X.hom)
    (targetFunctor := picardFunctorGrp A.X.hom) rep rep s
  have hg : g.hom.hom = dualP rep f := by
    apply rep.homEquiv.injective
    have h := GrpObj.homEquiv_mapOfRepresentableBy rep rep s (𝟙 P)
    rw [Category.id_comp] at h
    exact h.trans (rep.homEquiv.apply_symm_apply _).symm
  rw [← hg]
  exact g.hom.isMonHom_hom

/-- Inversion pulls a translation-invariant class back to its inverse. The
addition formula is restricted to the graph of inversion, whose sum is zero. -/
theorem inv_pullback_of_isTI [IsAlgClosed K] [CharZero K]
    (hrep : PicRepresentableAbVar) (hzero : PicZeroChar0.PicZeroAbVar0)
    (A : AbVar K) (c : A.X.left.Pic) (hc : AC.IsTI (X := A) c) :
    Scheme.Pic.map ι[A.X].left c = c⁻¹ := by
  let graph := CartesianMonoidalCategory.lift (𝟙 A.X) ι[A.X]
  have hzeroMap : graph.left ≫ (μ[A.X]).left = A.X.hom ≫ η[A.X].left :=
    congrArg Over.Hom.left (GrpObj.right_inv A.X)
  have hz : Scheme.Pic.map (A.X.hom ≫ η[A.X].left) c = 1 := by
    rw [Scheme.Pic.map_comp, Subsingleton.elim (α := (Spec (CommRingCat.of K)).Pic)
      (Scheme.Pic.map η[A.X].left c) 1, Scheme.Pic.map_one]
  have hf : graph.left ≫ pullback.fst A.X.hom A.X.hom = 𝟙 _ := by simp [graph]
  have hs : graph.left ≫ pullback.snd A.X.hom A.X.hom = ι[A.X].left := by simp [graph]
  apply eq_inv_of_mul_eq_one_right
  have h := congrArg (Scheme.Pic.map graph.left) (PhiSurj.mu_pic_of_isTI0 hrep hzero A c hc)
  rw [← Scheme.Pic.map_comp, hzeroMap, hz, Scheme.Pic.map_mul, ← Scheme.Pic.map_comp,
    ← Scheme.Pic.map_comp, hf, hs, Scheme.Pic.map_id] at h
  exact h.symm

-- DZQ's pullback on families restricts on the geometric fiber to its own group inversion.
private theorem famMap_inv (A : AbVar K) :
    famMap ι[A.X] (ptK K) = ι[(AKbar A).X].left := by
  change famMap ι[A.X] (ptK K) =
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).map
      ι[A.X]).left
  apply pullback.hom_ext <;> simp [famMap, Over.pullback_map_left]

/-- The restriction of pullback by inversion to the actual open Picard identity
component is group inversion. The equality is one of scheme morphisms over K. -/
theorem dualP_inv_on_picZero [CharZero K]
    (hrep : PicRepresentableAbVar) (hzero : PicZeroChar0.PicZeroAbVar0)
    {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P)
    {B : AbVar K} {j : B.X ⟶ P} (hj : IsPicZero rep B j) :
    j ≫ dualP rep ι[A.X] = ι[B.X] ≫ j := by
  obtain ⟨v, hv⟩ := exists_dual_on_picZero rep hj ι[A.X]
  have he : v.hom = ι[B.X] := by
    apply AVGlue.hom_ext_of_points
    intro y
    apply picClass_injective rep hj
    rw [picClass_dual rep j _ _ hv, famMap_inv]
    have ht := picZeroPtsTranslInv_of_leaves pushforwardUnitUniversal geomIntegralProd
      K A P rep B j hj y
    have hi := inv_pullback_of_isTI hrep hzero (AKbar A) (picClass rep j y) ((isTI_iff _).2 ht)
    exact hi.trans ((picHom rep hj).map_inv y).symm
  rw [← hv, he]

end ZInQ.PazukiPicardInvolution
