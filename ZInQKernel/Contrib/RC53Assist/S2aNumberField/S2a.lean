import ZInQKernel.Contrib.RC53Assist.S2aNumberField.ProjectiveComparison
import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral
import Mathlib.NumberTheory.NumberField.Basic

/-!
# S2a over every number field

Every one-dimensional abelian variety over a field `K` of characteristic zero, in each of the
three presentations of `ZInQKernel/HDecomp/Objects.lean` (`PkgI3.AbVar`,
`PkgI2.IsAbelianVariety`, `PkgI2.IsAbelianScheme`), is isomorphic over `K` to the projective
model of a nonsingular Weierstrass equation over `K`; the isomorphism sends the identity to the
point at infinity `O = [0 : 1 : 0]`, and its pullback of rational functions is the
Riemann–Roch identification `e` composed with the function-field identification of the
projective model. In particular this holds over every number field
(`abVar_projectiveWeierstrassModel_numberField`).

The statements have exactly the shape of the rational versions
(`ZInQ.Contrib.RC53Assist.GroupDifferentials.abVar_projectiveWeierstrassModel_unconditional`
and its siblings), with `ℚ` replaced by `K`. No hypothesis beyond the objects themselves and
characteristic zero (respectively the number-field structure) is assumed.

Mathematical locator: Silverman, *The Arithmetic of Elliptic Curves*, second edition,
Proposition III.3.1; Milne, *Abelian varieties*, version 2.00 (2008), IV, Propositions 6.4 and
6.6, printed p. 152, and I, Theorem 3.1, printed pp. 16–17.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.S2aNumberField

open AlgebraicGeometry CategoryTheory
open ZInQ.Contrib.RC53Assist.AbelianCurve (functionFieldAlgebra abelian_scheme_integral)

/-- THEOREM (proved). The function field of a one-dimensional `PkgI3.AbVar` over a field of
characteristic zero is an elliptic function field. Locator: `abelian_isEllipticFunctionField`;
`PkgI3.AbVar` in `ZInQKernel/HDecomp/Objects.lean`. -/
theorem abVar_isEllipticFunctionField_charZero (K : Type) [Field K] [CharZero K]
    (A : PkgI3.AbVar K) (hdim : A.dim = 1) :
    letI := abelian_scheme_integral A.X
    letI := functionFieldAlgebra A.X.hom
    TauCeti.IsEllipticFunctionField K A.X.left.functionField := by
  haveI := abelian_scheme_integral A.X
  exact abelian_isEllipticFunctionField A.X hdim

/-- THEOREM (proved). Pointed scheme-level S2a for the project's `PkgI3.AbVar` over a field of
characteristic zero. Locator: `abelian_projectiveWeierstrassModel`; `PkgI3.AbVar` in
`ZInQKernel/HDecomp/Objects.lean`. -/
theorem abVar_projectiveWeierstrassModel_charZero (K : Type) [Field K] [CharZero K]
    (A : PkgI3.AbVar K) (hdim : A.dim = 1) :
    letI := abelian_scheme_integral A.X
    letI := functionFieldAlgebra A.X.hom
    ∃ E : WeierstrassCurve K, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[K] A.X.left.functionField)
        (i : A.X.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = A.X.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint A.X) = pointO E := by
  haveI := abelian_scheme_integral A.X
  exact abelian_projectiveWeierstrassModel A.X hdim

/-- THEOREM (proved, S2a over every number field). Every one-dimensional `PkgI3.AbVar` over a
number field `K` is isomorphic over `K` to the projective model of a nonsingular Weierstrass
equation over `K`, sending the identity to the point at infinity, with the specified
function-field pullback. Locator: `abVar_projectiveWeierstrassModel_charZero`; a number field
has characteristic zero. -/
theorem abVar_projectiveWeierstrassModel_numberField :
    ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K), A.dim = 1 →
      letI := abelian_scheme_integral A.X
      letI := functionFieldAlgebra A.X.hom
      ∃ E : WeierstrassCurve K, E.IsElliptic ∧
        ∃ (e : E.toAffine.FunctionField ≃ₐ[K] A.X.left.functionField)
          (i : A.X.left ≅ Proj E.toProjective.grading),
          i.hom ≫ projectiveStructure E = A.X.hom ∧
          i.hom.functionFieldMap.hom =
            e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
          i.hom (identityPoint A.X) = pointO E := by
  intro K _ _ A hdim
  exact abVar_projectiveWeierstrassModel_charZero K A hdim

/-- THEOREM (proved). Pointed scheme-level S2a for the project's `PkgI2.IsAbelianVariety` over
a field of characteristic zero. Locator: `abelian_projectiveWeierstrassModel`;
`PkgI2.IsAbelianVariety` in `ZInQKernel/HDecomp/Objects.lean`. -/
theorem groupAbVar_projectiveWeierstrassModel_charZero (K : Type) [Field K] [CharZero K]
    (A : Grp (Over (Spec (.of K)))) [PkgI2.IsAbelianVariety A]
    (hdim : topologicalKrullDim A.X.left = 1) :
    letI := (inferInstance : PkgI2.IsAbelianVariety A).geomIntegral
    letI := abelian_scheme_integral A.X
    letI := functionFieldAlgebra A.X.hom
    ∃ E : WeierstrassCurve K, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[K] A.X.left.functionField)
        (i : A.X.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = A.X.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint A.X) = pointO E := by
  haveI := (inferInstance : PkgI2.IsAbelianVariety A).proper
  haveI := (inferInstance : PkgI2.IsAbelianVariety A).smooth
  haveI := (inferInstance : PkgI2.IsAbelianVariety A).geomIntegral
  haveI := abelian_scheme_integral A.X
  exact abelian_projectiveWeierstrassModel A.X hdim

/-- THEOREM (proved). An abelian scheme over a field in the geometrically connected
presentation `PkgI2.IsAbelianScheme` is geometrically integral.
Locator: `TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`. -/
theorem abelianScheme_geometricallyIntegral {K : Type} [Field K]
    (A : Grp (Over (Spec (.of K)))) [h : PkgI2.IsAbelianScheme A] :
    GeometricallyIntegral A.X.hom := by
  haveI := h.smooth
  haveI := h.geomConnected
  exact TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral A.X.hom

/-- THEOREM (proved). The underlying scheme of such an abelian scheme over a field is integral.
Locator: `abelianScheme_geometricallyIntegral`; Mathlib,
`GeometricallyIntegral.isIntegral_of_subsingleton`. -/
theorem abelianScheme_integral {K : Type} [Field K]
    (A : Grp (Over (Spec (.of K)))) [PkgI2.IsAbelianScheme A] : IsIntegral A.X.left := by
  haveI := abelianScheme_geometricallyIntegral A
  exact abelian_scheme_integral A.X

/-- THEOREM (proved). Pointed scheme-level S2a for the geometrically connected presentation
`PkgI2.IsAbelianScheme` over a field of characteristic zero; geometric integrality is derived.
Locator: `abelianScheme_geometricallyIntegral`; `abelian_projectiveWeierstrassModel`. -/
theorem abelianScheme_projectiveWeierstrassModel_charZero (K : Type) [Field K] [CharZero K]
    (A : Grp (Over (Spec (.of K)))) [h : PkgI2.IsAbelianScheme A]
    (hdim : topologicalKrullDim A.X.left = 1) :
    letI := abelianScheme_integral A
    letI := functionFieldAlgebra A.X.hom
    ∃ E : WeierstrassCurve K, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[K] A.X.left.functionField)
        (i : A.X.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = A.X.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint A.X) = pointO E := by
  haveI := h.proper
  haveI := h.smooth
  haveI := abelianScheme_geometricallyIntegral A
  haveI := abelianScheme_integral A
  exact abelian_projectiveWeierstrassModel A.X hdim

end ZInQ.Contrib.RC53Assist.S2aNumberField
