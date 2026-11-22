import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.BaseChange
import ZInQKernel.Contrib.OneProof.PicDictionary

/-! The full relative Picard representation and its dual pullback after scalar extension. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace ZInQ.PazukiPicardBaseChange

universe u

variable {S S' X X' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
  {g : S' ⟶ S} {π : X' ⟶ X} {P : Over S}

/-- Restrict test schemes along the base map. Adjunction identifies the
classifying morphisms with those into the pullback of the representative. -/
private def restrictRepresentation (g : S' ⟶ S)
    {F : (Over S)ᵒᵖ ⥤ Type (u + 1)} (r : F.RepresentableBy P) :
    ((Over.map g).op ⋙ F).RepresentableBy ((Over.pullback g).obj P) where
  homEquiv := ((Over.mapPullbackAdj g).homEquiv _ _).symm.trans r.homEquiv
  homEquiv_comp a t := by
    change r.homEquiv (((Over.mapPullbackAdj g).homEquiv _ _).symm (a ≫ t)) = _
    rw [(Over.mapPullbackAdj g).homEquiv_naturality_left_symm, r.homEquiv_comp]
    rfl

/-- The actual base change of the representing scheme represents the full
relative Picard functor of the pulled-back family. -/
def fullPicardRepresentation (sq : IsPullback π f' f g)
    (r : (picardFunctor f).obj.RepresentableBy P) :
    (picardFunctor f').obj.RepresentableBy ((Over.pullback g).obj P) :=
  (restrictRepresentation g r).ofIso (picardFunctorIsoOfIsPullback sq)

/-- The classifying equivalence transports precisely the class of the
adjoint point through the canonical relative Picard base-change map. -/
theorem fullPicardRepresentation_apply (sq : IsPullback π f' f g)
    (r : (picardFunctor f).obj.RepresentableBy P)
    {T : Over S'} (y : T ⟶ (Over.pullback g).obj P) :
    (fullPicardRepresentation sq r).homEquiv y =
      (picardFunctorIsoOfIsPullback sq).hom.app (op T)
        (r.homEquiv (((Over.mapPullbackAdj g).homEquiv _ _).symm y)) := rfl

section AbelianVariety

open PkgI3 T09Pic

variable {K L : Type} [Field K] [Field L] {A : AbVar K} {B : AbVar L}
  {b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)}
  {a : B.X.left ⟶ A.X.left} (sq : IsPullback a B.X.hom A.X.hom b)

/-- On a represented bundle, pullback by the dual on the sheaf is induced by
the original endomorphism on the first factor of the family. -/
private theorem dualSheafMap_on_class (u : A.X ⟶ A.X)
    (T : Over (Spec (CommRingCat.of K))) (c : (pullback A.X.hom T.hom).Pic) :
    (dualSheafMap u).app (op T) ((toPicardFunctor A.X.hom).app (op T) c) =
      (toPicardFunctor A.X.hom).app (op T) (Scheme.Pic.map (famMap u T) c) :=
  congrArg (fun n => n.app (op T) c) (toPicardFunctor_comp_dualSheafMap u)

/-- Pullback of Picard classes along endomorphisms commutes with scalar
extension on every test scheme. Rigidification at the zero section supplies
a global bundle representative of each relative class for this family. -/
theorem dualSheafMap_baseChange (u : A.X ⟶ A.X) (v : B.X ⟶ B.X)
    (hu : v.left ≫ a = a ≫ u.left) (T : Over (Spec (CommRingCat.of L)))
    (x : (picardFunctor A.X.hom).obj.obj (op ((Over.map b).obj T))) :
    (picardFunctorIsoOfIsPullback sq).hom.app (op T)
        ((dualSheafMap u).app (op ((Over.map b).obj T)) x) =
      (dualSheafMap v).app (op T) ((picardFunctorIsoOfIsPullback sq).hom.app (op T) x) := by
  let e := PicDict.Θ A PicDict.pushforwardUnitUniversal
  obtain ⟨c, hc⟩ := (e.app (op ((Over.map b).obj T))).toEquiv.surjective x
  change (toPicardFunctor A.X.hom).app _ c.1 = x at hc
  have hmaps : (pullbackIsoOfIsPullback sq T).hom ≫ famMap u ((Over.map b).obj T) =
      famMap v T ≫ (pullbackIsoOfIsPullback sq T).hom := by
    apply pullback.hom_ext <;> simp [famMap, Category.assoc, hu]
  have hbc (z : (pullback A.X.hom ((Over.map b).obj T).hom).Pic) :
      (picardFunctorIsoOfIsPullback sq).hom.app (op T)
          ((toPicardFunctor A.X.hom).app (op ((Over.map b).obj T)) z) =
        (toPicardFunctor B.X.hom).app (op T) (Scheme.Pic.map (pullbackIsoOfIsPullback sq T).hom z) := by
    simpa only [Functor.op_obj] using picardFunctorIsoOfIsPullback_hom_app_toPicardFunctor sq (op T) z
  rw [← hc, dualSheafMap_on_class u ((Over.map b).obj T) c.1,
    hbc (Scheme.Pic.map (famMap u ((Over.map b).obj T)) c.1), hbc c.1,
    dualSheafMap_on_class v T (Scheme.Pic.map (pullbackIsoOfIsPullback sq T).hom c.1)]
  apply congrArg (fun z => (toPicardFunctor B.X.hom).app (op T) z)
  exact (Scheme.Pic.map_comp _ _ _).symm.trans
    ((congrArg (fun f => Scheme.Pic.map f c.1) hmaps).trans (Scheme.Pic.map_comp _ _ _))

/-- Base change commutes with the represented DZQ morphism for a compatible
pair of endomorphisms of abelian varieties. -/
theorem dualP_baseChange {Q : Over (Spec (CommRingCat.of K))}
    (r : (picardFunctor A.X.hom).obj.RepresentableBy Q)
    (u : A.X ⟶ A.X) (v : B.X ⟶ B.X) (hu : v.left ≫ a = a ≫ u.left) :
    (Over.pullback b).map (dualP r u) = dualP (fullPicardRepresentation sq r) v := by
  let R := fullPicardRepresentation sq r
  let T := (Over.pullback b).obj Q
  let adj := Over.mapPullbackAdj b
  have hm : (adj.homEquiv T Q).symm ((Over.pullback b).map (dualP r u)) =
      (adj.homEquiv T Q).symm (𝟙 T) ≫ dualP r u := by
    simpa only [Category.id_comp] using adj.homEquiv_naturality_right_symm (𝟙 T) (dualP r u)
  apply R.homEquiv.injective
  change R.homEquiv _ = R.homEquiv (R.homEquiv.symm _)
  rw [Equiv.apply_symm_apply]
  change (picardFunctorIsoOfIsPullback sq).hom.app (op T)
        (r.homEquiv ((adj.homEquiv T Q).symm ((Over.pullback b).map (dualP r u)))) =
      (dualSheafMap v).app (op T)
        ((picardFunctorIsoOfIsPullback sq).hom.app (op T)
          (r.homEquiv ((adj.homEquiv T Q).symm (𝟙 T))))
  rw [hm, comp_dualP, Equiv.apply_symm_apply]
  exact dualSheafMap_baseChange sq u v hu T _

/-- In particular the transported Picard endomorphism is precisely pullback
by inversion on the scalar extension of the original abelian variety. -/
theorem dualP_inv_baseChange [Algebra K L] (A : AbVar K)
    {Q : Over (Spec (CommRingCat.of K))}
    (r : (picardFunctor A.X.hom).obj.RepresentableBy Q) :
    let β := Spec.map (CommRingCat.ofHom (algebraMap K L))
    let sq := IsPullback.of_hasPullback A.X.hom β
    (Over.pullback β).map (dualP r ι[A.X]) =
      dualP (A := A.baseChange L) (fullPicardRepresentation sq r) ι[(A.baseChange L).X] := by
  let β := Spec.map (CommRingCat.ofHom (algebraMap K L))
  apply dualP_baseChange (IsPullback.of_hasPullback A.X.hom β) r
  change ((Over.pullback β).map ι[A.X]).left ≫ pullback.fst A.X.hom β = _
  simp [β, Over.pullback_map_left] <;> rfl

end AbelianVariety

end ZInQ.PazukiPicardBaseChange
