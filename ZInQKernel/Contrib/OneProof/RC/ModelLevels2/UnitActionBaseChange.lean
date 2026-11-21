import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.UnitAction

/-! # Scalar extension of the geometric level action -/

namespace WeierstrassCurve.ModelLevels

variable {A : Type*} [CommRing A] (W : WeierstrassCurve A) [W.IsElliptic]
  {n : ℕ} (hN : IsUnit ((n + 3 : ℕ) : A))

section ScalarExtension

open scoped TensorProduct

variable {B : Type*} [CommRing B] [Algebra A B]

/-- The action on the exact-order cover after scalar extension from the
coefficient domain, via the canonical exact-order comparison. The target
coefficient ring may be nonreduced. -/
noncomputable def exactOrderUnitAutBaseChange [IsDomain A] :
    (ZMod (n + 3))ˣ →*
      (ExactOrderAlgebra (W.map (algebraMap A B))
          (show IsUnit ((n + 3 : ℕ) : B) by
            simpa only [map_natCast] using hN.map (algebraMap A B)) ≃ₐ[B]
        ExactOrderAlgebra (W.map (algebraMap A B))
          (show IsUnit ((n + 3 : ℕ) : B) by
            simpa only [map_natCast] using hN.map (algebraMap A B))) :=
  ((exactOrderBaseChange (B := B) W hN).autCongr.toMonoidHom).comp {
    toFun := fun a => Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B)
      (exactOrderUnitAut W hN a)
    map_one' := by
      rw [map_one]
      exact Algebra.TensorProduct.congr_refl
    map_mul' := by
      intro a b
      rw [map_mul]
      exact Algebra.TensorProduct.congr_trans
        (AlgEquiv.refl : B ≃ₐ[B] B) AlgEquiv.refl _ _ }

/-- The induced action on the specialized cover intertwines
the exact-order comparison on simple tensors. -/
theorem exactOrderUnitAutBaseChange_tmul [IsDomain A] (a : (ZMod (n + 3))ˣ)
    (b : B) (x : ExactOrderAlgebra W hN) :
    exactOrderUnitAutBaseChange (B := B) W hN a
        (exactOrderBaseChange (B := B) W hN (b ⊗ₜ[A] x)) =
      exactOrderBaseChange (B := B) W hN (b ⊗ₜ[A] (exactOrderUnitAut W hN a) x) := by
  simp [exactOrderUnitAutBaseChange, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply]

#print axioms exactOrderUnitAutBaseChange
#print axioms exactOrderUnitAutBaseChange_tmul

end ScalarExtension

end WeierstrassCurve.ModelLevels
