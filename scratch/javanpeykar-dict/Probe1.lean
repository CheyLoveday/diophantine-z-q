import ZInQKernel.OneProof.H.TailY
import ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.FieldExtension
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Dimension

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.HeightSplit

namespace JDProbe

variable {K : Type} [Field K] {J J' : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- base change of an isomorphism -/
noncomputable def bcIso (e : J.X ≅ J'.X) : (J.baseChange L).X ≅ (J'.baseChange L).X :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso e

theorem bcIso_isMonHom (e : J.X ≅ J'.X) [IsMonHom e.hom] : IsMonHom (bcIso (L := L) e).hom := by
  exact Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (f := e.hom)

noncomputable def transport (𝒢 : GroupModel J L) (e : J.X ≅ J'.X) [IsMonHom e.hom] :
    GroupModel J' L where
  G := 𝒢.G
  grp := 𝒢.grp
  smooth := 𝒢.smooth
  separated := 𝒢.separated
  qc := 𝒢.qc
  gen := 𝒢.gen ≪≫ bcIso e
  gen_hom := by
    let _ : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
    have := 𝒢.gen_hom
    have := bcIso_isMonHom (L := L) e
    show IsMonHom (𝒢.gen.hom ≫ (bcIso e).hom)
    infer_instance

noncomputable def transportM {g : ℕ} (M : MetrizedModel J L g) (e : J.X ≅ J'.X) [IsMonHom e.hom] :
    MetrizedModel J' L g where
  model := transport M.model e
  hodge := M.hodge
  lattice_eq := M.lattice_eq
  arch := M.arch

theorem transportM_height {g : ℕ} (M : MetrizedModel J L g) (e : J.X ≅ J'.X) [IsMonHom e.hom] :
    (transportM M e).hodge.modelHeight = M.hodge.modelHeight := rfl

end JDProbe
