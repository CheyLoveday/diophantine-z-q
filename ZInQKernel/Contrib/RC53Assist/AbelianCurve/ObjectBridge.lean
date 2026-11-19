import ZInQKernel.Contrib.RC53Assist.AbelianCurve.ProjectiveComparison
import ZInQKernel.HDecomp.Objects

/-!
# Specialization to the project's abelian varieties

These theorems use the actual `PkgI3.AbVar` and `PkgI2.IsAbelianVariety`
definitions in `ZInQKernel/HDecomp/Objects.lean`, rather than a replacement
notion of an abelian variety. The former has a group object `X` with proper,
smooth and geometrically integral structure morphism. Its `dim` is the
Krull dimension of `X.left`. The latter packages the same conditions on
an object of `Grp (Over (Spec k))`.

The separate `PkgI2.IsAbelianScheme` definition uses geometrically connected
fibres. It is not silently substituted for geometric integrality in these
statements.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AbelianCurve

open AlgebraicGeometry CategoryTheory
open ZInQ.Contrib.RC53Assist.IsogenyScheme

/-- THEOREM (proved, actual-object S2a part 1). The actual one-dimensional abelian variety's
function field is an algebraic function field of one variable over the rationals, with exact constants.
Locator: `ZInQKernel/HDecomp/Objects.lean`, `PkgI3.AbVar` and `PkgI3.AbVar.dim`,
lines 162–181; `abelian_functionField` above. Here “one-variable” means finite over some
rational function subfield, not isomorphic to the purely rational function field. -/
theorem abVar_functionField (A : PkgI3.AbVar ℚ) (hdim : A.dim = 1) :
    letI := abelian_scheme_integral A.X
    letI := functionFieldAlgebra A.X.hom
    TauCeti.IsFunctionField ℚ A.X.left.functionField ∧
      IsIntegrallyClosedIn ℚ A.X.left.functionField := by
  haveI := abelian_scheme_integral A.X
  exact abelian_functionField A.X hdim

/-- THEOREM (proved, actual-object S2a part 3). The identity of the actual one-dimensional
abelian variety supplies a degree-one place without any differential or genus input.
Locator: `ZInQKernel/HDecomp/Objects.lean`, `PkgI3.AbVar.grp`;
`smoothIdentityPlace_degree` above. -/
theorem abVar_identityPlace_degree (A : PkgI3.AbVar ℚ) (hdim : A.dim = 1) :
    letI := abelian_scheme_integral A.X
    letI := functionFieldAlgebra A.X.hom
    (smoothIdentityPlace A.X hdim).degree = 1 := by
  haveI := abelian_scheme_integral A.X
  exact smoothIdentityPlace_degree A.X hdim

/-- THEOREM (proved reduction, actual-object S2a). The actual one-dimensional abelian variety
is isomorphic over the rationals to the actual nonsingular projective Weierstrass model, after
exactly the two named differential inputs. The identity is sent to infinity, and the pullback
of rational functions is the Riemann–Roch field identification.
Locators: `ZInQKernel/HDecomp/Objects.lean`, `PkgI3.AbVar`;
`abelian_projectiveWeierstrassModel` above; Silverman, Proposition III.3.1. -/
theorem abVar_projectiveWeierstrassModel
    (hT : InvariantDifferentialTrivialization) (hC : RegularDifferentialComparison)
    (A : PkgI3.AbVar ℚ) (hdim : A.dim = 1) :
    letI := abelian_scheme_integral A.X
    letI := functionFieldAlgebra A.X.hom
    ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧
      ∃ (e : E.toAffine.FunctionField ≃ₐ[ℚ] A.X.left.functionField)
        (i : A.X.left ≅ Proj E.toProjective.grading),
        i.hom ≫ projectiveStructure E = A.X.hom ∧
        i.hom.functionFieldMap.hom =
          e.toRingHom.comp (projFunctionFieldEquiv E).toRingHom ∧
        i.hom (identityPoint A.X) = pointO E := by
  haveI := abelian_scheme_integral A.X
  exact abelian_projectiveWeierstrassModel hT hC A.X hdim

/-- THEOREM (proved reduction, group-object presentation). The second actual abelian-variety
presentation in the project has the same pointed projective-model conclusion.
Locators: `ZInQKernel/HDecomp/Objects.lean`, `PkgI2.IsAbelianVariety`, lines 791–797;
its three fields and `abelian_projectiveWeierstrassModel` above. -/
theorem groupAbVar_projectiveWeierstrassModel
    (hT : InvariantDifferentialTrivialization) (hC : RegularDifferentialComparison)
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
        i.hom (identityPoint A.X) = pointO E := by
  haveI := (inferInstance : PkgI2.IsAbelianVariety A).proper
  haveI := (inferInstance : PkgI2.IsAbelianVariety A).smooth
  haveI := (inferInstance : PkgI2.IsAbelianVariety A).geomIntegral
  haveI := abelian_scheme_integral A.X
  exact abelian_projectiveWeierstrassModel hT hC A.X hdim

end ZInQ.Contrib.RC53Assist.AbelianCurve
