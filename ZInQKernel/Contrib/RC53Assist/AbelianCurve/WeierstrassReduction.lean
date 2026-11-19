import ZInQKernel.Contrib.RC53Assist.AbelianCurve.DifferentialLine
import ZInQKernel.Contrib.RC53Assist.InvariantDifferential.WeierstrassModel

/-!
# Weierstrass coordinates for the identity of a group curve

The geometric inputs are exactly the two propositions in `DifferentialLine.lean`.
Every subsequent function-field step is proved. The existence theorem uses the
proved `s2b_rational`. The stronger coordinate theorem uses the same
Riemann–Roch construction with the actual degree-one place of the identity,
so the two coordinate functions have their only poles there.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AbelianCurve

open AlgebraicGeometry CategoryTheory

/-- THEOREM (proved reduction). A one-dimensional abelian group scheme over the rationals
has a nonsingular Weierstrass function-field model after the two named differential inputs.
Locator: `ZInQ.Contrib.RC53Assist.InvariantDifferential.s2b_rational`, proved from
Silverman, manuscript bibitem `silverman`, Proposition III.3.1. -/
theorem abelian_weierstrassModel
    (hT : InvariantDifferentialTrivialization) (hC : RegularDifferentialComparison)
    (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    ∃ W : WeierstrassCurve.Affine ℚ, W.IsElliptic ∧
      Nonempty (W.FunctionField ≃ₐ[ℚ] G.left.functionField) := by
  letI := functionFieldAlgebra G.hom
  exact ZInQ.Contrib.RC53Assist.InvariantDifferential.s2b_rational
    (isFunctionField_of_dimension_one G.hom hdim) (functionField_exact_constants G.hom)
    (abelian_isEllipticFunctionField hT hC G hdim)

/-- THEOREM (proved reduction, identity-based S2b). The Weierstrass coordinates have sole
poles of orders two and three at the identity's place and generate the actual function field.
Locator: `ZInQ.Contrib.RC53Assist.InvariantDifferential.exists_weierstrassModel_of_genus_eq_one`,
Silverman, Proposition III.3.1; `smoothIdentityPlace_degree`. -/
theorem abelian_weierstrassCoordinates
    (hT : InvariantDifferentialTrivialization) (hC : RegularDifferentialComparison)
    (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    let P := smoothIdentityPlace G hdim
    ∃ W : WeierstrassCurve.Affine ℚ, W.IsElliptic ∧
      ∃ e : W.FunctionField ≃ₐ[ℚ] G.left.functionField,
        P.ord (e W.genericX) = -2 ∧ P.ord (e W.genericY) = -3 ∧
        (∀ Q : TauCeti.Place ℚ G.left.functionField, Q ≠ P → 0 ≤ Q.ord (e W.genericX)) ∧
        (∀ Q : TauCeti.Place ℚ G.left.functionField, Q ≠ P → 0 ≤ Q.ord (e W.genericY)) := by
  letI := functionFieldAlgebra G.hom
  exact ZInQ.Contrib.RC53Assist.InvariantDifferential.exists_weierstrassModel_of_genus_eq_one
    (isFunctionField_of_dimension_one G.hom hdim) (functionField_exact_constants G.hom)
    (abelian_genus_one_of_differentials hT hC G hdim) (smoothIdentityPlace_degree G hdim)

end ZInQ.Contrib.RC53Assist.AbelianCurve
