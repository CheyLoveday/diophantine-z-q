import ZInQKernel.Contrib.RC53Assist.AbelianCurve.ObjectBridge
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral

/-!
# The geometrically connected abelian-scheme presentation

The actual `PkgI2.IsAbelianScheme` definition uses properness, smoothness and
geometrically connected fibres. The proved smoothness-to-geometric-integrality
lemma in the tree supplies geometric integrality; it is not an additional
printed input. Thus the same two differential inputs suffice for this
presentation and for `PkgI3.AbVar`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AbelianCurve

open AlgebraicGeometry CategoryTheory
open ZInQ.Contrib.RC53Assist.IsogenyScheme

/-- THEOREM (proved). A rational abelian scheme in the actual geometrically connected
presentation is geometrically integral.
Locators: `ZInQKernel/HDecomp/Objects.lean`, `PkgI2.IsAbelianScheme`, lines 801–804;
`TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral` in
`TauCeti/AlgebraicGeometry/Morphisms/Smooth/GeometricallyIntegral.lean`. -/
theorem abelianScheme_geometricallyIntegral
    (A : Grp (Over (Spec (.of ℚ)))) [h : PkgI2.IsAbelianScheme A] :
    GeometricallyIntegral A.X.hom := by
  haveI := h.smooth
  haveI := h.geomConnected
  exact TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral A.X.hom

/-- THEOREM (proved). The underlying rational abelian scheme is integral.
Locator: `abelianScheme_geometricallyIntegral` and
Mathlib, `GeometricallyIntegral.isIntegral_of_subsingleton`. -/
theorem abelianScheme_integral
    (A : Grp (Over (Spec (.of ℚ)))) [PkgI2.IsAbelianScheme A] : IsIntegral A.X.left := by
  haveI := abelianScheme_geometricallyIntegral A
  exact abelian_scheme_integral A.X

/-- THEOREM (proved, geometrically connected S2a part 1). The function field of a
one-dimensional rational abelian scheme is an algebraic function field of one variable
with exact rational constants. Geometric integrality is derived, not assumed.
Locators: `abelianScheme_geometricallyIntegral`; `abelian_functionField` above. -/
theorem abelianScheme_functionField
    (A : Grp (Over (Spec (.of ℚ)))) [h : PkgI2.IsAbelianScheme A]
    (hdim : topologicalKrullDim A.X.left = 1) :
    letI := abelianScheme_integral A
    letI := functionFieldAlgebra A.X.hom
    TauCeti.IsFunctionField ℚ A.X.left.functionField ∧
      IsIntegrallyClosedIn ℚ A.X.left.functionField := by
  haveI := h.proper
  haveI := h.smooth
  haveI := abelianScheme_geometricallyIntegral A
  haveI := abelianScheme_integral A
  exact abelian_functionField A.X hdim

/-- THEOREM (proved, geometrically connected S2a part 3). The identity of a one-dimensional
rational abelian scheme gives a degree-one place, with no genus or differential input.
Locators: `abelianScheme_integral`; `smoothIdentityPlace_degree` above. -/
theorem abelianScheme_identityPlace_degree
    (A : Grp (Over (Spec (.of ℚ)))) [h : PkgI2.IsAbelianScheme A]
    (hdim : topologicalKrullDim A.X.left = 1) :
    letI := abelianScheme_integral A
    letI := h.smooth
    letI := functionFieldAlgebra A.X.hom
    (smoothIdentityPlace A.X hdim).degree = 1 := by
  haveI := abelianScheme_integral A
  haveI := h.smooth
  exact smoothIdentityPlace_degree A.X hdim

/-- THEOREM (proved reduction, exact geometrically connected presentation of S2a). An actual
one-dimensional rational abelian scheme is isomorphic over the rationals to an actual
nonsingular projective Weierstrass model after the two named differential inputs.
The identity is sent to infinity and the specified function-field pullback is realized.
Locators: `PkgI2.IsAbelianScheme` in `ZInQKernel/HDecomp/Objects.lean`;
`abelianScheme_geometricallyIntegral`; `abelian_projectiveWeierstrassModel` above. -/
theorem abelianScheme_projectiveWeierstrassModel
    (hT : InvariantDifferentialTrivialization) (hC : RegularDifferentialComparison)
    (A : Grp (Over (Spec (.of ℚ)))) [h : PkgI2.IsAbelianScheme A]
    (hdim : topologicalKrullDim A.X.left = 1) :
    letI := abelianScheme_integral A
    letI := functionFieldAlgebra A.X.hom
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[ℚ] A.X.left.functionField)
        (i : A.X.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = A.X.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint A.X) = pointO E := by
  haveI := h.proper
  haveI := h.smooth
  haveI := abelianScheme_geometricallyIntegral A
  haveI := abelianScheme_integral A
  exact abelian_projectiveWeierstrassModel hT hC A.X hdim

end ZInQ.Contrib.RC53Assist.AbelianCurve
