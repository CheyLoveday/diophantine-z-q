import ZInQKernel.Contrib.OneProof.RC.ModelTorsion.Monogenic
import ZInQKernel.Contrib.OneProof.RC.ModelTorsion.Separability

/-! # The finite étale algebra of torsion abscissae -/

namespace WeierstrassCurve.ModelTorsion

open Polynomial
open scoped TensorProduct

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The abscissa algebra over a ring where the level and elliptic discriminant
are units. -/
theorem abscissaAlgebra_finite_etale (W : WeierstrassCurve A) [W.IsElliptic]
    {n : ℕ} (hn : IsUnit (n : A)) :
    IsUnit (polynomialDiscriminant (xPolynomial W n) (isUnit_leadingCoeff_xPolynomial W hn)) ∧
      Module.Finite A (AdjoinRoot (xPolynomial W n)) ∧
      Module.Free A (AdjoinRoot (xPolynomial W n)) ∧
      Algebra.Etale A (AdjoinRoot (xPolynomial W n)) := by
  apply monogenic_of_separable_specializations
  intro K _ i
  rw [← map_xPolynomial]
  exact separable_xPolynomial (W.map i) (by simpa using (hn.map i).ne_zero)

/-- Extension of scalars on the abscissa algebra sends the root generator to
the abscissa of the base-changed curve. -/
noncomputable def abscissaAlgebraBaseChange (W : WeierstrassCurve A) (n : ℕ) [Algebra A B] :
    B ⊗[A] AdjoinRoot (xPolynomial W n) ≃ₐ[B]
      AdjoinRoot (xPolynomial (W.map (algebraMap A B)) n) := by
  let p := xPolynomial W n
  let i : A →ₐ[A] B ⊗[A] A := Algebra.TensorProduct.includeRight
  let e := Algebra.TensorProduct.rid A B B
  refine (AdjoinRoot.tensorAlgEquiv p (p.map i.toRingHom) rfl).trans
    (AdjoinRoot.mapAlgEquiv e _ _ ?_)
  change Associated ((p.map i.toRingHom).map e.toRingHom) _
  rw [Polynomial.map_map, map_xPolynomial]
  have he : e.toRingHom.comp i.toRingHom = algebraMap A B := by
    ext x
    simp [e, i, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]
  rw [he]

theorem abscissaAlgebraBaseChange_root (W : WeierstrassCurve A) (n : ℕ) [Algebra A B] :
    abscissaAlgebraBaseChange (B := B) W n (1 ⊗ₜ AdjoinRoot.root (xPolynomial W n)) =
      AdjoinRoot.root (xPolynomial (W.map (algebraMap A B)) n) := by
  rw [abscissaAlgebraBaseChange, AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root]
  rw [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root]

#print axioms abscissaAlgebra_finite_etale
#print axioms abscissaAlgebraBaseChange_root

end WeierstrassCurve.ModelTorsion
