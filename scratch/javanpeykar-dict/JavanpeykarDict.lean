import ZInQKernel.OneProof.H.TailY
import ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.FieldExtension
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Dimension

noncomputable section

set_option linter.unusedSectionVars false

namespace JavanpeykarDict

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.HeightSplit
open LeafModCurves (IsCurve IsJacobian IsBelyiFunction)
open ZInQ.LeafPush2 (ffAlgebra javanpeykarBound)

/-! ## 1. The published stable height is an isomorphism invariant -/

section HeightIso

variable {K : Type} [Field K] {J J' : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- `e_L : J_L ≅ J'_L`, the base change of an isomorphism `e : J ≅ J'`. -/
def bcIso (e : J.X ≅ J'.X) : (J.baseChange L).X ≅ (J'.baseChange L).X :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso e

theorem bcIso_isMonHom (e : J.X ≅ J'.X) [IsMonHom e.hom] : IsMonHom (bcIso (L := L) e).hom := by
  exact Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (f := e.hom)

/-- A group model of `J_L` is a group model of `J'_L` through `e_L` (same scheme over `𝓞_L`). -/
def transport (𝒢 : GroupModel J L) (e : J.X ≅ J'.X) [IsMonHom e.hom] : GroupModel J' L where
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

/-- A metrized model of `J_L` is one of `J'_L` (same Hodge data). -/
def transportM {g : ℕ} (M : MetrizedModel J L g) (e : J.X ≅ J'.X) [IsMonHom e.hom] :
    MetrizedModel J' L g where
  model := transport M.model e
  hodge := M.hodge
  lattice_eq := M.lattice_eq
  arch := M.arch

theorem bcIso_trans_symm (e : J.X ≅ J'.X) : bcIso (L := L) e ≪≫ bcIso e.symm = Iso.refl _ := by
  have h : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso e ≪≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso e.symm =
      Iso.refl ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj J.X) := by
    rw [Functor.mapIso_symm, Iso.self_symm_id]
  exact h

theorem transport_transport (𝒢 : GroupModel J L) (e : J.X ≅ J'.X) [IsMonHom e.hom]
    [IsMonHom e.symm.hom] : transport (transport 𝒢 e) e.symm = 𝒢 := by
  cases 𝒢
  simp only [transport]
  congr 1
  rw [Iso.trans_assoc, bcIso_trans_symm, Iso.trans_refl]

theorem height_transport (𝒢 : GroupModel J L) (e : J.X ≅ J'.X) [IsMonHom e.hom] :
    (transport 𝒢 e).height = 𝒢.height := by
  have : IsMonHom e.symm.hom := by change IsMonHom e.inv; infer_instance
  unfold GroupModel.height
  apply le_antisymm
  · refine le_iInf fun g => le_iInf fun M => le_iInf fun hM => ?_
    refine iInf_le_of_le g (iInf_le_of_le (transportM M e) (iInf_le_of_le ?_ le_rfl))
    show transport M.model e = transport 𝒢 e
    rw [hM]
  · refine le_iInf fun g => le_iInf fun M' => le_iInf fun hM' => ?_
    refine iInf_le_of_le g (iInf_le_of_le (transportM M' e.symm) (iInf_le_of_le ?_ le_rfl))
    show transport M'.model e.symm = 𝒢
    rw [hM', transport_transport]

theorem bijective_comp_iso {Y Z W : Over (Spec (CommRingCat.of L))} (i : Z ≅ W) :
    Function.Bijective fun u : Y ⟶ Z => u ≫ i.hom :=
  ⟨fun a b h => by simpa using congrArg (· ≫ i.inv) h, fun b => ⟨b ≫ i.inv, by simp⟩⟩

theorem isNeronModel_transport (𝒩 : GroupModel J L) (e : J.X ≅ J'.X) [IsMonHom e.hom]
    (h : 𝒩.IsNeronModel) : (transport 𝒩 e).IsNeronModel := by
  intro Y _
  have h1 := (bijective_comp_iso (Y := (Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) L)))).obj Y) (bcIso (L := L) e)).comp (h Y)
  refine (congrArg Function.Bijective ?_).mpr h1
  funext f
  change (Over.pullback _).map f ≫ (𝒩.gen.hom ≫ (bcIso e).hom) =
    ((Over.pullback _).map f ≫ 𝒩.gen.hom) ≫ (bcIso e).hom
  exact (Category.assoc _ _ _).symm

theorem isSemistable_transport (𝒩 : GroupModel J L) (e : J.X ≅ J'.X) [IsMonHom e.hom]
    (h : IsSemistable 𝒩) : IsSemistable (transport 𝒩 e) := h

/-- **The published stable height is invariant under isomorphism of abelian varieties (glue,
proved).** -/
theorem isStableFaltingsHeight_of_iso (e : J.X ≅ J'.X) [IsMonHom e.hom] {x : ℝ}
    (h : IsStableFaltingsHeight J x) : IsStableFaltingsHeight J' x := by
  obtain ⟨L, _, _, _, 𝒩, hN, hS, hx⟩ := h
  exact ⟨L, _, _, _, transport 𝒩 e, isNeronModel_transport 𝒩 e hN,
    isSemistable_transport 𝒩 e hS, by rw [height_transport]; exact hx⟩

end HeightIso

end JavanpeykarDict
