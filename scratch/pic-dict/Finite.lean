import ZInQKernel.Contrib.OneProof.PicDictionary

/-! # pic-dict: `FiniteOfFiniteKerPts` (a homomorphism with finitely many `K̄`-points in its kernel is finite) -/

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace PicDict

open T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing

variable {K : Type} [Field K]

/-- Over a closed point `b`, there are finitely many `K̄`-points (they are the `K`-embeddings of the finite
extension `κ(b)` into `K̄`). -/
theorem finite_pts_over {B : AbVar K} (b : B.X.left) (hb : IsClosed {b}) :
    {y : B.Pt (AlgebraicClosure K) |
      y.left (IsLocalRing.closedPoint (AlgebraicClosure K)) = b}.Finite := by
  haveI : IsFinite (B.X.left.fromSpecResidueField b ≫ B.X.hom) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hb
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  let φ := Spec.preimage (B.X.left.fromSpecResidueField b ≫ B.X.hom)
  have hφ : Spec.map φ = B.X.left.fromSpecResidueField b ≫ B.X.hom := Spec.map_preimage _
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  letI : Algebra K (B.X.left.residueField b) := φ.hom.toAlgebra
  haveI : Module.Finite K (B.X.left.residueField b) := hfin
  let mk : (B.X.left.residueField b →ₐ[K] AlgebraicClosure K) → (Spec (CommRingCat.of (AlgebraicClosure K)) ⟶
      B.X.left) := fun ψ =>
    Spec.map (CommRingCat.ofHom (ψ : B.X.left.residueField b →+* AlgebraicClosure K)) ≫
      B.X.left.fromSpecResidueField b
  have key : ∀ y : B.Pt (AlgebraicClosure K),
      y.left (IsLocalRing.closedPoint (AlgebraicClosure K)) = b → ∃ ψ, y.left = mk ψ := by
    intro y hy
    have e1 : ∀ (x : B.X.left) (hx : x = b) (ψ : B.X.left.residueField x ⟶
        CommRingCat.of (AlgebraicClosure K)), ∃ ψ' : B.X.left.residueField b ⟶
          CommRingCat.of (AlgebraicClosure K),
        Spec.map ψ ≫ B.X.left.fromSpecResidueField x = Spec.map ψ' ≫ B.X.left.fromSpecResidueField b := by
      intro x hx ψ; subst hx; exact ⟨ψ, rfl⟩
    have hy' : (Scheme.SpecToEquivOfField (AlgebraicClosure K) B.X.left y.left).1 = b := hy
    obtain ⟨ψ', hψ'⟩ := e1 _ hy' (Scheme.SpecToEquivOfField (AlgebraicClosure K) B.X.left y.left).2
    have hyl : y.left = Spec.map ψ' ≫ B.X.left.fromSpecResidueField b := by
      rw [← hψ']
      exact ((Scheme.SpecToEquivOfField (AlgebraicClosure K) B.X.left).symm_apply_apply y.left).symm
    have hw : φ ≫ ψ' = CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ, ← Category.assoc, ← hyl]
      exact Over.w y
    refine ⟨{ toRingHom := ψ'.hom, commutes' := fun a => ?_ }, hyl⟩
    exact congrArg (fun χ => χ.hom a) hw
  apply Set.Finite.of_finite_image (f := fun y : B.Pt (AlgebraicClosure K) => y.left)
  · refine (Set.finite_range mk).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨ψ, h⟩ := key y hy
    exact ⟨ψ, h.symm⟩
  · intro y _ y' _ h
    exact Over.OverMorphism.ext h

end PicDict
