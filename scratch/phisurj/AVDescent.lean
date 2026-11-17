import ZInQKernel.Contrib.OneProof.PhiSurjDescent
import ZInQKernel.Contrib.OneProof.WeilFormulaTheta
import ZInQKernel.Contrib.OneProof.MumfordSquareMulN

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

namespace PhiSurj.AVDesc

open PicDict PkgI3 PkgI3.AbVar PicDict.Transport WeilProof WeilProof.Theta

variable {k : Type} [Field k]

/-- `[n]` is étale, surjective and proper (from weil-proof's `divisibleAC` argument). -/
theorem mul_props [IsAlgClosed k] (X : AbVar k) (n : ℕ) (hnk : (n : k) ≠ 0) :
    Etale (AC.mul X n).left ∧ Surjective (AC.mul X n).left ∧ IsProper (AC.mul X n).left := by
  have : GeometricallyConnected X.X.hom := geomConn_of_geomInt X.X.hom
  have : PkgI2.IsAbelianScheme (ObjBridge.toGrp X) := ⟨X.proper, X.smooth, inferInstance⟩
  have hE : Etale ((𝟙 (ObjBridge.toGrp X).X ^ n : (ObjBridge.toGrp X).X ⟶ (ObjBridge.toGrp X).X).left) :=
    ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof k (ObjBridge.toGrp X) n
      (by exact (IsUnit.mk0 _ hnk))
  have hE' : Etale (AC.mul X n).left := hE
  set f := (AC.mul X n).left with hfdef
  have hopen : IsOpenMap f := isOpenMap_of_generalizingMap f (Flat.generalizingMap f)
  have hw : f ≫ X.X.hom = X.X.hom := Over.w (AC.mul X n)
  have : IsProper (f ≫ X.X.hom) := by rw [hw]; infer_instance
  have hP : IsProper f := IsProper.of_comp f X.X.hom
  have hclosed : IsClosedMap f := f.isClosedMap
  have : IsIntegral X.X.left := GeometricallyIntegral.isIntegral_of_subsingleton X.X.hom
  have hrange : Set.range f = Set.univ := by
    have hne : (Set.range f).Nonempty := by
      obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
      exact ⟨_, ⟨η[X.X].left p, rfl⟩⟩
    exact (IsClopen.eq_univ ⟨hclosed.isClosed_range, hopen.isOpen_range⟩ hne)
  refine ⟨hE', ⟨fun y => ?_⟩, hP⟩
  have : y ∈ Set.range f := by rw [hrange]; trivial
  exact this

/-- `[n]` generates an fpqc covering. -/
theorem mul_cover [IsAlgClosed k] (X : AbVar k) (n : ℕ) (hnk : (n : k) ≠ 0) :
    Sieve.ofArrows (fun _ : PUnit.{1} => X.X.left) (fun _ => (AC.mul X n).left) ∈
      Scheme.fpqcTopology X.X.left := by
  obtain ⟨hE, hS, hP⟩ := mul_props X n hnk
  change Sieve.generate (Presieve.ofArrows _ _) ∈ _
  rw [Presieve.ofArrows_pUnit]
  exact Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fpqcPrecoverage _)

lemma tr_left_comp_mul {X : AbVar k} {n : ℕ} (x : AC.Kpt X) (hx : x ^ n = 1) :
    (AC.tr x).left ≫ (AC.mul X n).left = (AC.mul X n).left := by
  rw [← Over.comp_left, AC.tr_comp_mul x hx]

/-- The sections `y ↦ (y, y + x)`, `x ∈ X[n]`, are open immersions. -/
instance sec_isOpenImmersion [IsAlgClosed k] {X : AbVar k} {n : ℕ} [Fact ((n : k) ≠ 0)] (x : AC.Kpt X) (hx : x ^ n = 1) :
    IsOpenImmersion (Desc.sec (AC.mul X n).left (tr_left_comp_mul x hx)) := by
  obtain ⟨hE, -, -⟩ := mul_props X n (Fact.out)
  exact ZInQ.Contrib.AbVarBC.MulRigidity.isOpenImmersion_of_section _
    (pullback.fst (AC.mul X n).left (AC.mul X n).left) (pullback.lift_fst _ _ _)

end PhiSurj.AVDesc
