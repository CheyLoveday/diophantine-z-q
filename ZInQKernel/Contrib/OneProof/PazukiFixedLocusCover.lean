import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import ZInQKernel.Contrib.OneProof.PicLocFinType
import ZInQKernel.Contrib.OneProof.PazukiFixedQuasiFinite
import ZInQKernel.Contrib.OneProof.PazukiPicardInvolution

/-! Quasi-finiteness on the whole geometric fixed locus of Picard pullback by inversion. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace ZInQ.PazukiFixedLocusCover

variable {k : Type} [Field k]

/-- For a locally finite-type scheme over an algebraically closed field, it
suffices to prove quasi-finiteness at the images of rational sections. -/
theorem locallyQuasiFinite_of_sections [IsAlgClosed k] {X : Scheme.{0}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (atSection : ∀ s : Spec (.of k) ⟶ X, s ≫ p = 𝟙 _ →
      p.QuasiFiniteAt (s (IsLocalRing.closedPoint k))) : LocallyQuasiFinite p := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  have ho (x : X) (hx : x ∈ closedPoints X) : IsOpen ({x} : Set X) := by
    let s := pointOfClosedPoint p x hx
    have hq := atSection s (pointOfClosedPoint_comp p x hx)
    rw [show s (IsLocalRing.closedPoint k) = x from pointOfClosedPoint_apply p x hx _] at hq
    have h1 := Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hq
    have h2 := (p.fiberHomeo (p x)).isOpenMap _ h1
    rw [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply] at h2
    have hopen : IsOpen (p.base ⁻¹' {p x}) := by
      have hfull : p.base ⁻¹' {p x} = Set.univ :=
        Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
      rw [hfull]
      exact isOpen_univ
    simpa using hopen.isOpenMap_subtype_val _ h2
  have hopen : IsOpen (closedPoints X) := by
    refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
    exact ⟨{x}, Set.singleton_subset_iff.mpr hx, ho x hx, Set.mem_singleton _⟩
  have hclosed (x : X) : x ∈ closedPoints X := by
    by_contra hx
    have hn : ((closedPoints X)ᶜ).Nonempty := ⟨x, hx⟩
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hn hopen.isClosed_compl.isLocallyClosed
    exact hy hyc
  haveI : DiscreteTopology X :=
    discreteTopology_iff_isOpen_singleton.mpr fun x => ho x (hclosed x)
  exact locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr fun _ =>
    isDiscrete_iff_discreteTopology.mpr inferInstance

/-- The full equalizer of DZQ's actual Picard involution is locally quasi-finite
over an algebraically closed field of characteristic zero. There can be infinitely
many components. The two Picard hypotheses are those of the inversion formula. -/
theorem picard_fixed_locallyQuasiFinite [IsAlgClosed k] [CharZero k]
    (hrep : T09Pic.PicRepresentableAbVar) (hzero : PicZeroChar0.PicZeroAbVar0)
    (A : PkgI3.AbVar k) {P : Over (Spec (.of k))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) :
    LocallyQuasiFinite
      (equalizer.ι (T09Pic.dualP rep ι[A.X]).left (𝟙 P.left) ≫ P.hom) := by
  let D := T09Pic.dualP rep ι[A.X]
  let e := equalizer.ι D.left (𝟙 P.left)
  haveI : LocallyOfFiniteType P.hom := PicLFT.picLocFinType_proof k A P rep
  haveI : LocallyOfFiniteType e := inferInstanceAs (LocallyOfFiniteType (equalizer.ι D.left (𝟙 P.left)))
  obtain ⟨B, j, hj⟩ := hzero k A P rep
  apply locallyQuasiFinite_of_sections (e ≫ P.hom)
  intro q hq
  let s : 𝟙_ (Over (Spec (.of k))) ⟶ P := Over.homMk (q ≫ e) (by
    change (q ≫ e) ≫ P.hom = 𝟙 _
    rw [Category.assoc, hq])
  have hs : s ≫ D = s := by
    apply Over.OverMorphism.ext
    change (q ≫ equalizer.ι D.left (𝟙 P.left)) ≫ D.left = q ≫ equalizer.ι D.left (𝟙 P.left)
    rw [Category.assoc, equalizer.condition, Category.comp_id]
  exact PazukiFixedQuasiFinite.picard_fixed_quasiFiniteAt_section A rep B j hj
    (PazukiPicardInvolution.dualP_isMonHom rep ι[A.X])
    (PazukiPicardInvolution.dualP_inv_on_picZero hrep hzero rep hj) s hs _ rfl

end ZInQ.PazukiFixedLocusCover
