import ZInQKernel.Contrib.OneProof.RC.HCMV21.GeometricKernel
import ZInQKernel.Contrib.OneProof.MulEtale

/-! The integer multiplication maps used in the Tate calculation are
finite étale in residue characteristic prime to that integer. -/

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory PkgI3.AbVar
open ZInQ.Contrib.AbVarBC
open scoped CategoryTheory.MonObj

/-- On the actual geometric abelian variety, multiplication by a
nonzero scalar integer in the field is finite, étale and surjective. -/
theorem finiteEtale_mul_of_ne_zero {k : Type} [Field k]
    (A : PkgI3.AbVar k) (n : ℕ) (hn : (n : k) ≠ 0) :
    IsFinite (((n : ℤ) : A.End).hom).left ∧
    Etale (((n : ℤ) : A.End).hom).left ∧
    Surjective (((n : ℤ) : A.End).hom).left := by
  have hconn : GeometricallyConnected A.X.hom := ⟨by
    intro K _ y Z fst snd h
    let : IrreducibleSpace Z :=
      GeometricallyIrreducible.geometrically_irreducibleSpace y fst snd h
    infer_instance⟩
  have : PkgI2.IsAbelianScheme (ObjBridge.toGrp A) :=
    ⟨A.proper, A.smooth, hconn⟩
  have heq : (((n : ℤ) : A.End).hom) = (𝟙 A.X : A.X ⟶ A.X) ^ n := by
    simpa only [Category.id_comp] using AvSplit.comp_natCast_hom' A (𝟙 A.X) n
  have hE : Etale (((n : ℤ) : A.End).hom).left := by
    rw [heq]
    exact ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof
      k (ObjBridge.toGrp A) n (isUnit_iff_ne_zero.mpr hn)
  have : LocallyQuasiFinite (((n : ℤ) : A.End).hom).left :=
    MulRigidity.locallyQuasiFinite_of_formallyUnramified _
  have hf := MulRigidity.isIsogenyMor_of_lqf_of_isOpenMap A _
    (Scheme.Hom.isOpenMap (((n : ℤ) : A.End).hom).left)
  exact ⟨hf.1, hE, hf.2⟩

/-- Consequently multiplication is surjective on geometric points.
This application of scheme surjectivity does not require characteristic zero. -/
theorem surjective_nsmul_of_ne_zero {k : Type} [Field k]
    (A : PkgI3.AbVar k) (n : ℕ) (hn : (n : k) ≠ 0) :
    Function.Surjective (fun x : Additive (A.Pt (AlgebraicClosure k)) => n • x) := by
  obtain ⟨hf, -, hs⟩ := finiteEtale_mul_of_ne_zero A n hn
  let := hf
  let := hs
  intro x
  obtain ⟨P, hP⟩ := ZInQ.Contrib.TateLatticeTorsion.surjective_geometricPoints_of_finite
    (((n : ℤ) : A.End).hom) (Additive.toMul x)
  refine ⟨Additive.ofMul P, ?_⟩
  change Additive.ofMul (P ^ n) = x
  rw [← AvSplit.comp_natCast_hom' A P n]
  exact congrArg Additive.ofMul hP

/-- Saturation of the geometric Hom image at every prime that is
invertible in the residue field. -/
theorem exists_eq_nsmul_of_primeTo_homT_dvd {k : Type} [Field k] {A B : PkgI3.AbVar k}
    (f : Hom A B) (ℓ n : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (h : ∀ x : A.T ℓ, ∃ y : B.T ℓ, homT f x = (ℓ : ℤ_[ℓ]) ^ n • y) :
    ∃ g : Hom A B, f = (ℓ ^ n : ℕ) • g := by
  have hn : ((ℓ ^ n : ℕ) : k) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero n hℓ
  obtain ⟨hf, he, hs⟩ := finiteEtale_mul_of_ne_zero A (ℓ ^ n) hn
  let := hf
  let := he
  let := hs
  exact exists_eq_nsmul_of_etale_homT_dvd f ℓ n (surjective_nsmul_of_ne_zero A ℓ hℓ) h

end ZInQ.Manuscript.RC.HCMV21
