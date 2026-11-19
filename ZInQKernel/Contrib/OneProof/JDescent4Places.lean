import ZInQKernel.Contrib.OneProof.JDescent3FunctionField
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Dominant
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.Extension.Basic

/-! Centers of places on the actual abelian curve, and compatibility with étale pullback. -/

namespace HDec.CMBranch.CMjBridges

open CategoryTheory AlgebraicGeometry

noncomputable section

attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra

variable {K : Type} [Field K]

/-- Every place of the actual function field is centered at a closed point, and its
valuation ring is the image of the local ring at that point. -/
theorem abVar_exists_placeCenter (A : PkgI3.AbVar K) (hdim : A.dim = 1)
    (P : TauCeti.Place K (AbVarFunctionField A)) :
    ∃ x : A.X.left, IsClosed ({x} : Set A.X.left) ∧
      (algebraMap (A.X.left.presheaf.stalk x) (AbVarFunctionField A)).range =
        P.integers.toSubring := by
  let := abVar_smoothRelDimOne A hdim
  let v : AlgebraicCurve.Place K (AbVarFunctionField A) :=
    ⟨P.integers, P.algebraMap_mem_integers, P.integers_ne_top, inferInstance⟩
  exact AlgebraicCurve.exists_closedPoint_range_stalk_eq A.X.hom v

/-- Every closed point of the actual abelian curve gives a Tau Ceti place. -/
theorem abVar_exists_placeOf_closedPoint [CharZero K] (A : PkgI3.AbVar K) (hdim : A.dim = 1)
    (x : A.X.left) (hx : IsClosed ({x} : Set A.X.left)) :
    ∃ P : TauCeti.Place K (AbVarFunctionField A),
      (algebraMap (A.X.left.presheaf.stalk x) (AbVarFunctionField A)).range =
        P.integers.toSubring := by
  let := abVar_smoothRelDimOne A hdim
  obtain ⟨v, hv⟩ := AlgebraicCurve.exists_place_range_stalk_eq A.X.hom x hx
  let P := TauCeti.Place.ofValuationSubring (A := v.toValuationSubring)
    (abVar_isFunctionField A hdim) v.algebraMap_mem' v.ne_top'
  exact ⟨P, by simpa [P, TauCeti.Place.integers_ofValuationSubring] using hv⟩

#print axioms abVar_exists_placeCenter
#print axioms abVar_exists_placeOf_closedPoint

end

end HDec.CMBranch.CMjBridges
