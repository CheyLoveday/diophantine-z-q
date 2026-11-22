import ZInQKernel.Contrib.OneProof.PazukiSymmetricDescent
import Mathlib.Basic.Complex.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj
namespace ZInQ.PazukiSymmetricDescent

-- Use the actual pullback and tensor product on classes of A, on both sides.
example {K : Type} [Field K] (A : PkgI3.AbVar K) (L M : A.X.left.Pic)
    (hL : Scheme.Pic.map (GrpObj.inv (X := A.X)).left L = L)
    (hM : Scheme.Pic.map (GrpObj.inv (X := A.X)).left M = M⁻¹) :
    Scheme.Pic.map (GrpObj.inv (X := A.X)).left (L * M) = L * M ↔ M ^ 2 = 1 :=
  symmetric_tensor_iff_sq_eq_one A L M hL hM

-- Instantiate at the intended overfield. Require one finite extension,
-- compatible embeddings, a descended fixed point and recovery of the input s.
example {K : Type} [Field K] [NumberField K] {X : Scheme}
    (p : X ⟶ Spec (CommRingCat.of K)) (i : X ⟶ X)
    (s : Spec (CommRingCat.of ℂ) ⟶ X) (σ : K →+* ℂ)
    (hs : s ≫ p = Spec.map (CommRingCat.ofHom σ)) (hf : s ≫ i = s ≫ 𝟙 X)
    (hq : (equalizer.ι i (𝟙 X) ≫ p).QuasiFiniteAt
      (equalizer.lift s hf (IsLocalRing.closedPoint ℂ))) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra K E) (_ : FiniteDimensional K E)
      (embedding : E →+* ℂ) (t : Spec (CommRingCat.of E) ⟶ X),
      embedding.comp (algebraMap K E) = σ ∧
      t ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K E)) ∧
      t ≫ i = t ∧ s = Spec.map (CommRingCat.ofHom embedding) ≫ t :=
  fixedPoint_numberField_factor p i s σ hs hf hq

end ZInQ.PazukiSymmetricDescent

#print axioms ZInQ.PazukiSymmetricDescent.symmetric_tensor_iff_sq_eq_one
#print axioms ZInQ.PazukiSymmetricDescent.symmetric_twist_iff_sq_eq_one
#print axioms ZInQ.PazukiSymmetricDescent.numberField_factor_of_quasiFiniteAt
#print axioms ZInQ.PazukiSymmetricDescent.fixedPoint_numberField_factor
