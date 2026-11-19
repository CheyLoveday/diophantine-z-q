import ZInQKernel.Contrib.RC53Assist.GroupDifferentials.Trivialization
import ZInQKernel.Contrib.RC53Assist.AbelianCurveInputs.S2aConsequence
import ZInQKernel.Contrib.RC53Assist.AbelianCurve.SchemeBridge

/-!
# S2a without remaining inputs

`AbelianCurveInputs/S2aConsequence.lean` reduces the pointed scheme-level S2a conclusion to the
single proposition `AbelianCurve.InvariantDifferentialTrivialization`, the regular-differential
comparison being proved in `AbelianCurveInputs/LocalFacts.lean`. That proposition is proved in
`GroupDifferentials/Trivialization.lean`. The theorems below are the resulting statements
with no hypothesis beyond the objects themselves: every one-dimensional rational abelian
variety, in each of the three presentations of `ZInQKernel/HDecomp/Objects.lean`, is
isomorphic over the rationals to an actual nonsingular projective Weierstrass model, sending
the identity to the point at infinity, with the specified function-field pullback.

Each statement is copied from the corresponding conditional theorem with the hypothesis
`hT : InvariantDifferentialTrivialization` (and, for the scheme presentation, also
`hC : RegularDifferentialComparison`) discharged.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.GroupDifferentials

open AlgebraicGeometry CategoryTheory
open ZInQ.Contrib.RC53Assist.AbelianCurve
open ZInQ.Contrib.RC53Assist.IsogenyScheme

/-- PROVED. A proper smooth geometrically integral group curve over the rationals has an
elliptic function field. Locator: `S2aConsequence.abelian_isEllipticFunctionField_of_trivialization`
with `invariantDifferentialTrivialization`. -/
theorem abelian_isEllipticFunctionField_unconditional
    (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    TauCeti.IsEllipticFunctionField ℚ G.left.functionField :=
  AbelianCurveInputs.S2aConsequence.abelian_isEllipticFunctionField_of_trivialization
    invariantDifferentialTrivialization G hdim

/-- PROVED. Pointed scheme-level S2a for a proper smooth geometrically integral group curve
over the rationals. Locator:
`S2aConsequence.abelian_projectiveWeierstrassModel_of_trivialization` with
`invariantDifferentialTrivialization`. -/
theorem abelian_projectiveWeierstrassModel_unconditional
    (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[ℚ] G.left.functionField)
        (i : G.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = G.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint G) = pointO E :=
  AbelianCurveInputs.S2aConsequence.abelian_projectiveWeierstrassModel_of_trivialization
    invariantDifferentialTrivialization G hdim

/-- PROVED. Pointed scheme-level S2a for the project's `PkgI3.AbVar`. Locator:
`S2aConsequence.abVar_projectiveWeierstrassModel_of_trivialization` with
`invariantDifferentialTrivialization`; `PkgI3.AbVar` in `ZInQKernel/HDecomp/Objects.lean`. -/
theorem abVar_projectiveWeierstrassModel_unconditional
    (A : PkgI3.AbVar ℚ) (hdim : A.dim = 1) :
    letI := abelian_scheme_integral A.X
    letI := functionFieldAlgebra A.X.hom
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[ℚ] A.X.left.functionField)
        (i : A.X.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = A.X.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint A.X) = pointO E :=
  AbelianCurveInputs.S2aConsequence.abVar_projectiveWeierstrassModel_of_trivialization
    invariantDifferentialTrivialization A hdim

/-- PROVED. Pointed scheme-level S2a for the project's `PkgI2.IsAbelianVariety`. Locator:
`S2aConsequence.groupAbVar_projectiveWeierstrassModel_of_trivialization` with
`invariantDifferentialTrivialization`. -/
theorem groupAbVar_projectiveWeierstrassModel_unconditional
    (A : Grp (Over (Spec (.of ℚ)))) [PkgI2.IsAbelianVariety A]
    (hdim : topologicalKrullDim A.X.left = 1) :
    letI := (inferInstance : PkgI2.IsAbelianVariety A).geomIntegral
    letI := abelian_scheme_integral A.X
    letI := functionFieldAlgebra A.X.hom
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[ℚ] A.X.left.functionField)
        (i : A.X.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = A.X.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint A.X) = pointO E :=
  AbelianCurveInputs.S2aConsequence.groupAbVar_projectiveWeierstrassModel_of_trivialization
    invariantDifferentialTrivialization A hdim

/-- PROVED. Pointed scheme-level S2a for the project's geometrically connected presentation
`PkgI2.IsAbelianScheme`. Locator: `AbelianCurve.abelianScheme_projectiveWeierstrassModel`
with `invariantDifferentialTrivialization` and `LocalFacts.regularDifferentialComparison`. -/
theorem abelianScheme_projectiveWeierstrassModel_unconditional
    (A : Grp (Over (Spec (.of ℚ)))) [PkgI2.IsAbelianScheme A]
    (hdim : topologicalKrullDim A.X.left = 1) :
    letI := abelianScheme_integral A
    letI := functionFieldAlgebra A.X.hom
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[ℚ] A.X.left.functionField)
        (i : A.X.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = A.X.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint A.X) = pointO E :=
  abelianScheme_projectiveWeierstrassModel invariantDifferentialTrivialization
    AbelianCurveInputs.LocalFacts.regularDifferentialComparison A hdim

end ZInQ.Contrib.RC53Assist.GroupDifferentials
