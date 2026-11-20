import ZInQKernel.Contrib.RC53Assist.S2aNumberField.RegularComparison
import ZInQKernel.Contrib.RC53Assist.GroupDifferentials.Trivialization
import ZInQKernel.Contrib.RC53Assist.InvariantDifferential.WeierstrassModel

/-!
# Genus one and Weierstrass coordinates for group curves in characteristic zero

For a proper smooth geometrically integral group curve `G` over a field `K` of characteristic
zero:

* the sheafified relative Kähler differentials are a trivial line sheaf
  (`differentialSheaf_trivial`), by translation invariance and the fibre at the identity;
* the function field has genus one (`abelian_genus_one`): the global differentials are
  one-dimensional over `K` (trivial line sheaf, constant global functions), and they are the
  holomorphic Weil differentials (`regularDifferentialComparison`);
* the function field is elliptic, with the identity as a place of degree one
  (`abelian_isEllipticFunctionField`);
* Riemann–Roch at the identity place gives a nonsingular Weierstrass equation over `K` and a
  `K`-algebra isomorphism of function fields whose coordinates have their only poles at the
  identity, of orders two and three (`abelian_weierstrassCoordinates`). Characteristic zero
  makes `K` perfect, which gives nonsingularity.

These are the statements of the rational version in the modules
`ZInQKernel.Contrib.RC53Assist.AbelianCurve.DifferentialLine`,
`ZInQKernel.Contrib.RC53Assist.AbelianCurve.WeierstrassReduction` and
`ZInQKernel.Contrib.RC53Assist.GroupDifferentials.Trivialization`, for a general base.

Mathematical locator: Milne, *Abelian varieties*, version 2.00 (2008), IV, Propositions 6.4
and 6.6, printed p. 152; Silverman, *The Arithmetic of Elliptic Curves*, second edition,
Proposition III.3.1 and Chapter II, §§4–5.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.S2aNumberField

open AlgebraicGeometry CategoryTheory
open ZInQ.Contrib.RC53Assist.AbelianCurve (functionFieldAlgebra differentialSheaf
  globalSectionsModule isFunctionField_of_dimension_one functionField_exact_constants
  finrank_globalSections_trivial_line)

variable {K : Type} [Field K]

/-- THEOREM (proved). The sheafified relative Kähler differentials of a smooth integral group
curve over a field of characteristic zero form a trivial line sheaf.
Locator: Milne, cited 2008 notes, IV, Proposition 6.4(a)–(b), printed p. 152;
`GroupDifferentials.nonempty_relativeDifferentials_iso_unit_of_grpObj` (any base field) and
`smooth_relativeDimension_one` (characteristic zero). -/
theorem differentialSheaf_trivial [CharZero K] (G : Over (Spec (.of K))) [GrpObj G]
    [IsIntegral G.left] [Smooth G.hom] (hdim : topologicalKrullDim G.left = 1) :
    Nonempty (differentialSheaf G.hom ≅ SheafOfModules.unit G.left.ringCatSheaf) := by
  letI : GrpObj (Over.mk G.hom) := inferInstanceAs (GrpObj G)
  haveI := smooth_relativeDimension_one G.hom hdim
  exact ZInQ.Contrib.RC53Assist.GroupDifferentials.nonempty_relativeDifferentials_iso_unit_of_grpObj
    G.hom

/-- THEOREM (proved). A proper smooth geometrically integral group curve over a field of
characteristic zero has a function field of genus one.
Locator: Milne IV.6.4 and the free-line case of IV.6.6; `regularDifferentialComparison`;
`TauCeti.finrank_weilDifferentialFiltration_zero`. -/
theorem abelian_genus_one [CharZero K] (G : Over (Spec (.of K))) [GrpObj G]
    [IsIntegral G.left] [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    TauCeti.genus K G.left.functionField = 1 := by
  letI := functionFieldAlgebra G.hom
  letI := globalSectionsModule G.hom (differentialSheaf G.hom)
  obtain ⟨e⟩ := differentialSheaf_trivial G hdim
  obtain ⟨c⟩ := regularDifferentialComparison G.left G.hom hdim
  rw [← TauCeti.finrank_weilDifferentialFiltration_zero
    (isFunctionField_of_dimension_one G.hom hdim) (functionField_exact_constants G.hom),
    ← c.finrank_eq]
  exact finrank_globalSections_trivial_line G.hom (differentialSheaf G.hom) e

/-- THEOREM (proved). The function field of a proper smooth geometrically integral group curve
over a field of characteristic zero is an elliptic function field.
Locator: `abelian_genus_one` and `ellipticFunctionField_of_genus_one`. -/
theorem abelian_isEllipticFunctionField [CharZero K] (G : Over (Spec (.of K))) [GrpObj G]
    [IsIntegral G.left] [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    TauCeti.IsEllipticFunctionField K G.left.functionField :=
  ellipticFunctionField_of_genus_one G hdim (abelian_genus_one G hdim)

/-- THEOREM (proved). Weierstrass coordinates at the identity: a nonsingular Weierstrass curve
over `K` and a `K`-algebra isomorphism of function fields whose coordinates have their only
poles at the identity place, of orders two and three.
Locator: `InvariantDifferential.exists_weierstrassModel_of_genus_eq_one` (perfect constants),
Silverman, Proposition III.3.1; `smoothIdentityPlace_degree`. -/
theorem abelian_weierstrassCoordinates [CharZero K] (G : Over (Spec (.of K))) [GrpObj G]
    [IsIntegral G.left] [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    let P := smoothIdentityPlace G hdim
    ∃ W : WeierstrassCurve.Affine K, W.IsElliptic ∧
      ∃ e : W.FunctionField ≃ₐ[K] G.left.functionField,
        P.ord (e W.genericX) = -2 ∧ P.ord (e W.genericY) = -3 ∧
        (∀ Q : TauCeti.Place K G.left.functionField, Q ≠ P → 0 ≤ Q.ord (e W.genericX)) ∧
        (∀ Q : TauCeti.Place K G.left.functionField, Q ≠ P → 0 ≤ Q.ord (e W.genericY)) := by
  letI := functionFieldAlgebra G.hom
  exact ZInQ.Contrib.RC53Assist.InvariantDifferential.exists_weierstrassModel_of_genus_eq_one
    (isFunctionField_of_dimension_one G.hom hdim) (functionField_exact_constants G.hom)
    (abelian_genus_one G hdim) (smoothIdentityPlace_degree G hdim)

end ZInQ.Contrib.RC53Assist.S2aNumberField
