import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Density
import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Infinity
import ZInQKernel.Contrib.OneProof.RC.AtkinRational.PointReading

/-! Generic fibre of (O.7), tex 8487–8489 and 9101–9113.
The density passage and interface are on the spot (c). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Classical MatrixGroups TauCeti.ExactDivisor
open AlgebraicGeometry CategoryTheory UpperHalfPlane WeierstrassCurve ModularCurve
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Contrib.RC53Assist.IsogenyScheme
open ZInQ.Manuscript.RC.PreparedParam ZInQ.Manuscript.RC.AtkinPin
open ZInQ.Manuscript.RC.ParamAtScale

namespace ZInQ.Manuscript.RC.AtkinRational

/-- A comparison on the fixed projective Weierstrass model: the difference
of the two morphisms' field readings is itself read by a morphism. This
property mentions neither the Atkin–Lehner action nor the parametrization. -/
def RepresentsDifference (N : ℕ) [NeZero N] (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  ∀ (u v : (X0Branch.model N).X ⟶ Proj E.toProjective.grading)
    (_ : u ≫ projectiveOverQ E = (X0Branch.model N).overQ)
    (_ : v ≫ projectiveOverQ E = (X0Branch.model N).overQ) (e : ℤ),
    ∃ D : (X0Branch.model N).X ⟶ Proj E.toProjective.grading,
      D ≫ projectiveOverQ E = (X0Branch.model N).overQ ∧
      ∀ (F : Type) [Field F] [Algebra ℚ F] (x : FieldPoint (X0Branch.model N).overQ F),
        projectiveValue (x.val ≫ D) =
          projectiveValue (x.val ≫ u) - e • projectiveValue (x.val ≫ v)

set_option maxHeartbeats 600000 in
/-- On the interior, the signed difference is constant by the complex chart
identity and faithful reading on the projective elliptic curve. The interior
contains a dominant point, so reducedness of the source and separatedness of
the target give equality of morphisms with the descended rational constant
map. Evaluate there at the rational cusp and then extend fields. -/
theorem based_of_representedDifference {N Q : ℕ} [NeZero N] {hQ : Q ∥ N}
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (W : RationalAtkin (X0Branch.model N) hQ)
    (π : (X0Branch.model N).X ⟶ Proj E.toProjective.grading)
    (hπ : π ≫ projectiveOverQ E = (X0Branch.model N).overQ)
    (b : FieldPoint (X0Branch.model N).overQ ℚ) (hb : projectiveValue (b.comp π hπ).val = 0)
    (e : ℤ)
    (hchart : ∀ base τ : ℍ,
      let P := fun t : ℍ => projectiveValue (((X0Branch.model N).complexPoint t).comp π hπ).val
      P (atkinGL hQ • τ) = e • P τ + (P (atkinGL hQ • base) - e • P base))
    (D : (X0Branch.model N).X ⟶ Proj E.toProjective.grading)
    (hD : D ≫ projectiveOverQ E = (X0Branch.model N).overQ)
    (hread : ∀ (F : Type) [Field F] [Algebra ℚ F]
      (x : FieldPoint (X0Branch.model N).overQ F),
      projectiveValue (x.val ≫ D) =
        projectiveValue (((x.comp W.hom W.overQ).comp π hπ).val) -
          e • projectiveValue (x.comp π hπ).val) :
    BasedAtkinOnPoints (X0Branch.model N) W π hπ b e := by
  let X := X0Branch.model N
  let P := fun t : ℍ => projectiveValue ((X.complexPoint t).comp π hπ).val
  have ht (τ : ℍ) : projectiveValue ((X.complexPoint τ).val ≫ D) =
      P (atkinGL hQ • τ) - e • P τ := by
    rw [hread ℂ (X.complexPoint τ), W.chart]
  have hc (τ : ℍ) : X0Model.complexPoint N τ ≫ D =
      X0Model.complexPoint N default ≫ D := by
    apply projectiveValue_injective_of_origin E (b.comp π hπ).val hb
    change projectiveValue ((X.complexPoint τ).val ≫ D) =
      projectiveValue ((X.complexPoint default).val ≫ D)
    rw [ht, ht default]
    have h := hchart default τ
    change P (atkinGL hQ • τ) = _ at h
    rw [h]
    change e • P τ + (P (atkinGL hQ • default) - e • P default) - e • P τ = _
    abel
  have hd := eq_constant_of_chart (projectiveOverQ E) D hD b.val _ hc
  intro F _ _ x
  let a := b.map (Algebra.ofId ℚ F)
  have ha : x.val ≫ D = a.val ≫ D := by
    conv_lhs => rw [hd]
    change x.val ≫ X.overQ ≫ b.val ≫ D =
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ F)) ≫ b.val) ≫ D
    rw [← Category.assoc, x.property, Category.assoc]
  have hh := (hread F x).symm.trans ((congrArg (projectiveValue (E := E)) ha).trans (hread F a))
  dsimp only
  rw [zsmul_sub]
  have hh' := congrArg (fun z => z + (e • projectiveValue (x.comp π hπ).val -
    projectiveValue (((a.comp W.hom W.overQ).comp π hπ).val))) hh
  convert hh' using 1 <;> abel

/-- The (O.7) generic statement for the at-scale join, conditional only on
representing the ordinary Weierstrass point operations on the fixed Proj.
The exact divisor involution and the eigenvalue are the constructed ones. -/
theorem genericFibreAtScale_of_representsDifference {ℓ Q : ℕ} [(Ecurve ℓ).IsElliptic]
    [NeZero (newformLevel (Ecurve ℓ))]
    (f : HeckeRing.GL2.Newform (newformLevel (Ecurve ℓ)) 2) (hχ : f.χ = 1)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 (f.toCuspFormGamma0 hχ)).coeff n =
      ((Ecurve ℓ).LFunction n : ℂ))
    (hQ : Q ∥ newformLevel (Ecurve ℓ)) {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat)
    {κ : ℂ} (hκ : IsParamScale (newformLevel (Ecurve ℓ)) (f.toCuspFormGamma0 hχ) Lat κ)
    (hr : ∃ c : ℚ, (c : ℂ) = κ)
    (hLaw : RepresentsDifference (newformLevel (Ecurve ℓ)) (Ecurve ℓ)) :
    let N := newformLevel (Ecurve ℓ)
    let X := X0Branch.model N
    let W := rationalAtkin hQ
    let e := (signUnit f hχ hQ : ℤ)
    ∃ (π : X.X ⟶ Proj (Ecurve ℓ).toProjective.grading)
      (hπ : π ≫ projectiveOverQ (Ecurve ℓ) = X.overQ), IsDominant π ∧
      (∀ τ : ℍ, projectiveValue ((X.complexPoint τ).comp π hπ).val =
        phiAn (Ecurve ℓ) (f.toCuspFormGamma0 hχ) Lat κ τ) ∧
      projectiveValue ((infinityPoint N).comp π hπ).val = 0 ∧
      BasedAtkinOnPoints X W π hπ (infinityPoint N) e ∧
      ∀ (F : Type) [Field F] [Algebra ℚ F] (x : FieldPoint X.overQ F),
        projectiveValue ((x.comp W.hom W.overQ).comp π hπ).val =
          e • projectiveValue (x.comp π hπ).val +
            Affine.Point.map (W' := (Ecurve ℓ).toAffine) (Algebra.ofId ℚ F)
              (projectiveValue (((infinityPoint N).comp W.hom W.overQ).comp π hπ).val) := by
  let N := newformLevel (Ecurve ℓ)
  let X := X0Branch.model N
  let W := rationalAtkin hQ
  let e := (signUnit f hχ hQ : ℤ)
  obtain ⟨π, hπ, hd, hscale, hzero⟩ :=
    algebraicParametrizationAtScale_atInfinity (f.toCuspFormGamma0 hχ) hf hLat hκ hr
  obtain ⟨D, hD, hread⟩ :=
    hLaw (W.hom ≫ π) π (by rw [Category.assoc, hπ, W.overQ]) hπ e
  have h := based_of_representedDifference W π hπ (infinityPoint N) hzero e
    (projectiveValue_transform_chart X f hχ hQ Lat κ hLat π hπ hscale) D hD
    (fun F _ _ x => by simpa only [FieldPoint.comp, Category.assoc] using hread F x)
  exact ⟨π, hπ, hd, hscale, hzero, h,
    translatedAtkinAtInfinity W π hπ e h hzero⟩

#print axioms RepresentsDifference
#print axioms based_of_representedDifference
#print axioms genericFibreAtScale_of_representsDifference

end ZInQ.Manuscript.RC.AtkinRational
