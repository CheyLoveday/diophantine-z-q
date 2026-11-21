import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.NumberTheory.NumberField.Basic
import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Group

/-!
The pointwise symmetry calculation and the residue-field factorization used in
the proposed fixed-locus proof of symmetric line bundle descent.
-/

namespace ZInQ.PazukiSymmetricDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

/-- On Picard classes themselves, symmetry of a twist through a fixed class is
exactly two-torsion whenever pullback inverts the twisting class. -/
theorem symmetric_tensor_iff_sq_eq_one {K : Type} [Field K] (A : PkgI3.AbVar K)
    (L M : A.X.left.Pic)
    (hL : Scheme.Pic.map (GrpObj.inv (X := A.X)).left L = L)
    (hM : Scheme.Pic.map (GrpObj.inv (X := A.X)).left M = M⁻¹) :
    Scheme.Pic.map (GrpObj.inv (X := A.X)).left (L * M) = L * M ↔ M ^ 2 = 1 := by
  rw [Scheme.Pic.map_mul, hL, hM]
  constructor
  · intro h
    have hi : M⁻¹ = M := mul_left_cancel h
    calc
      M ^ 2 = M⁻¹ * M := by rw [pow_two, hi]
      _ = 1 := inv_mul_cancel M
  · intro h
    have hi : M⁻¹ = M := calc
      M⁻¹ = M⁻¹ * (M ^ 2) := by rw [h, mul_one]
      _ = M := by rw [pow_two, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hi]

/-- In a translate of the dual abelian variety through a symmetric class, the
symmetric classes correspond to the two-torsion. `j` is the map on points into
the Picard group. `hinv` records the pullback action on its image. -/
theorem symmetric_twist_iff_sq_eq_one {K : Type} [Field K] (A : PkgI3.AbVar K)
    {G : Type} [CommGroup G] (j : G →* A.X.left.Pic) (hj : Function.Injective j)
    (L : A.X.left.Pic)
    (hL : Scheme.Pic.map (GrpObj.inv (X := A.X)).left L = L)
    (hinv : ∀ M, Scheme.Pic.map (GrpObj.inv (X := A.X)).left (j M) = j (M⁻¹))
    (M : G) :
    Scheme.Pic.map (GrpObj.inv (X := A.X)).left (L * j M) = L * j M ↔ M ^ 2 = 1 := by
  have hM : Scheme.Pic.map (GrpObj.inv (X := A.X)).left (j M) = (j M)⁻¹ := by
    rw [hinv M, map_inv]
  rw [symmetric_tensor_iff_sq_eq_one A L (j M) hL hM, ← map_pow]
  exact map_eq_one_iff j hj

/-- A field-valued point at which the structure morphism is quasi-finite factors
through the residue field of its image. If the ground field is a number field,
this factor is a number field and the embedding extends the original one. -/
theorem numberField_factor_of_quasiFiniteAt {K F : Type} [Field K] [NumberField K] [Field F]
    {X : Scheme} (p : X ⟶ Spec (CommRingCat.of K)) (s : Spec (CommRingCat.of F) ⟶ X)
    (σ : K →+* F) (hs : s ≫ p = Spec.map (CommRingCat.ofHom σ))
    (hfin : p.QuasiFiniteAt (s (IsLocalRing.closedPoint F))) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra K E) (_ : FiniteDimensional K E)
      (e : E →+* F) (t : Spec (CommRingCat.of E) ⟶ X),
      e.comp (algebraMap K E) = σ ∧
      t ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K E)) ∧
      s = Spec.map (CommRingCat.ofHom e) ≫ t := by
  let q := Scheme.SpecToEquivOfField F X s
  let t := X.fromSpecResidueField q.1
  have hs_factor : Spec.map q.2 ≫ t = s := (Scheme.SpecToEquivOfField F X).symm_apply_apply s
  haveI : LocallyQuasiFinite (X.fromSpecStalk q.1 ≫ p) :=
    Scheme.Hom.quasiFiniteAt_iff.mp (show p.QuasiFiniteAt q.1 from hfin)
  have hq : LocallyQuasiFinite (t ≫ p) := by
    change LocallyQuasiFinite ((Spec.map (X.residue q.1) ≫ X.fromSpecStalk q.1) ≫ p)
    rw [Category.assoc]
    infer_instance
  let φ := Spec.preimage (t ≫ p)
  have hφ : Spec.map φ = t ≫ p := Spec.map_preimage _
  have hspec : LocallyQuasiFinite (Spec.map φ) := by
    rw [hφ]
    exact hq
  have hφq : (φ.hom).QuasiFinite :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite) (φ := φ)).mp hspec
  letI : Algebra K (X.residueField q.1) := φ.hom.toAlgebra
  haveI : Algebra.QuasiFinite K (X.residueField q.1) := by
    rw [← RingHom.quasiFinite_algebraMap, RingHom.algebraMap_toAlgebra]
    exact hφq
  haveI : Module.Finite K (X.residueField q.1) := Module.Finite.of_quasiFinite
  haveI : NumberField (X.residueField q.1) := NumberField.of_module_finite K _
  have hσ : φ ≫ q.2 = CommRingCat.ofHom σ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, ← Category.assoc, hs_factor]
    exact hs
  refine ⟨↥(X.residueField q.1), inferInstance, inferInstance, inferInstance, inferInstance, q.2.hom, t, ?_, ?_, ?_⟩
  · apply RingHom.ext
    intro a
    exact congrArg (fun f => f.hom a) hσ
  · exact hφ.symm
  · exact hs_factor.symm

/-- Factor a fixed field-valued point through a number-field-valued fixed point.
The quasi-finiteness hypothesis is at the image in the scheme equalizer. -/
theorem fixedPoint_numberField_factor {K F : Type} [Field K] [NumberField K] [Field F]
    {X : Scheme} (p : X ⟶ Spec (CommRingCat.of K)) (i : X ⟶ X)
    (s : Spec (CommRingCat.of F) ⟶ X) (σ : K →+* F)
    (hs : s ≫ p = Spec.map (CommRingCat.ofHom σ)) (hfixed : s ≫ i = s ≫ 𝟙 X)
    (hfin : (equalizer.ι i (𝟙 X) ≫ p).QuasiFiniteAt
      (equalizer.lift s hfixed (IsLocalRing.closedPoint F))) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra K E) (_ : FiniteDimensional K E)
      (e : E →+* F) (t : Spec (CommRingCat.of E) ⟶ X),
      e.comp (algebraMap K E) = σ ∧
      t ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K E)) ∧
      t ≫ i = t ∧ s = Spec.map (CommRingCat.ofHom e) ≫ t := by
  have hs' : equalizer.lift s hfixed ≫ (equalizer.ι i (𝟙 X) ≫ p) =
      Spec.map (CommRingCat.ofHom σ) := by
    rw [← Category.assoc, equalizer.lift_ι, hs]
  obtain ⟨E, hE, hNF, hAlg, hfinite, e, v, hσ, hv, hfactor⟩ :=
    numberField_factor_of_quasiFiniteAt _ _ σ hs' hfin
  letI : Field E := hE
  letI : Algebra K E := hAlg
  refine ⟨E, hE, hNF, hAlg, hfinite, e, v ≫ equalizer.ι i (𝟙 X), hσ, ?_, ?_, ?_⟩
  · rw [Category.assoc, hv]
  · rw [Category.assoc, equalizer.condition, Category.comp_id]
  · calc
      s = equalizer.lift s hfixed ≫ equalizer.ι i (𝟙 X) := (equalizer.lift_ι _ _).symm
      _ = Spec.map (CommRingCat.ofHom e) ≫ (v ≫ equalizer.ι i (𝟙 X)) := by
        rw [hfactor, Category.assoc]

end ZInQ.PazukiSymmetricDescent
