import ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.isDefEq.respectTransparency false

theorem isMonHom_pullbackComp {S S' S'' : Scheme.{0}} (f : S'' ⟶ S') (g : S' ⟶ S) (U : Over S) [GrpObj U] :
    letI : GrpObj ((Over.pullback (f ≫ g)).obj U) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback g).obj U) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback f).obj ((Over.pullback g).obj U)) := Functor.grpObjObj
    let ε : (Over.pullback (f ≫ g)).obj U ⟶ (Over.pullback f).obj ((Over.pullback g).obj U) :=
      (Over.pullbackComp f g).hom.app U
    IsMonHom ε := by
  letI : GrpObj ((Over.pullback (f ≫ g)).obj U) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback g).obj U) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback f).obj ((Over.pullback g).obj U)) := Functor.grpObjObj
  let M : Mon (Over S) := Mon.mk U
  let A := ((Functor.mapMonNatIso (Over.pullbackComp f g)).hom.app M)
  let B := ((Functor.mapMonCompIso (F := Over.pullback g) (G := Over.pullback f)).hom.app M)
  have h3 := (A ≫ B).isMonHom_hom
  intro ε
  convert h3 using 1 <;> (try rfl)
  all_goals simp [A, B, ε]
