import ZInQKernel.Contrib.RC53Assist.CoordProvenance.ExistingScalar
import ZInQKernel.Contrib.RC53Assist.CoordProvenance.EndpointComparison
import ZInQKernel.Contrib.RC53Assist.CoordProvenance.FullModelAdapter
import ZInQKernel.Contrib.RC53Assist.CoordProvenance.CoefficientRealization

/-!
# Recorded obstructions to unbound endpoint provenance

These obstructions were found in an independent review.  A proof that selects
an endpoint from a step does not preserve that selection when its exported
type forgets every readback identity.  The resulting free existential is true
for every scalar.  A nonzero adjugate alone does not repair an unbound model.

For a fixed homotopy-aware comparison at a nonzero target coordinate, the
uncomputed retained-basis equation is equivalent to coordinate equality.
It is therefore a conditional normalization leaf until a determinant
calculation from the actual fixed diagrams supplies it.

The coefficient-field diagrams and inverse-disk calculation remain valid;
the final examples record why the latter is not an integral record cast.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions

open Matrix CategoryTheory
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (IsCoordOn)
open ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar (existing_scalar_unique)
open ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport

/-- A free finite-core existential admits every prescribed scalar. -/
theorem free_endpoint_every_scalar {R : Type} [CommRing R] (u : R) :
    ∃ (m : ℕ) (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
      (z w : Fin (m + 1) → R), IsCoordOn D z w u := by
  refine ⟨0, 0, (fun _ => u), (fun _ => 1), ?_⟩
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.adjugate_fin_one, Matrix.vecMulVec_apply]

/-- The exact original endpoint existential has all-zero witnesses for every scalar. -/
theorem exact_endpoint_zero_witness {R : Type} [CommRing R] (u : R) :
    ∃ (n : ℕ)
      (D : Matrix (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (Fin n ⊕ (Fin 2 ⊕ Fin 2)) R)
      (z w : Fin n ⊕ (Fin 2 ⊕ Fin 2) → R), IsCoordOn D z w u := by
  refine ⟨0, 0, 0, 0, ?_⟩
  simp [IsCoordOn]

/-- Nonzero adjugate and closed representatives do not bind a freely chosen endpoint. -/
theorem free_regular_endpoint_every_scalar {K : Type} [Field K] (u : K) :
    ∃ (m : ℕ) (D : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
      (z w : Fin (m + 1) → K),
      D.adjugate ≠ 0 ∧ D *ᵥ z = 0 ∧ w ᵥ* D = 0 ∧ IsCoordOn D z w u := by
  refine ⟨0, 0, (fun _ => u), (fun _ => 1), ?_, ?_, ?_, ?_⟩
  · rw [Matrix.adjugate_fin_one]
    exact one_ne_zero
  · simp
  · simp
  · ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.adjugate_fin_one, Matrix.vecMulVec_apply]

/-- Once the matrix and representatives are fixed and regular, a zero cycle cannot fake a nonzero scalar. -/
theorem zero_fixed_cycle_forces_scalar_zero {K : Type} [Field K]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι K) (w : ι → K) (u : K) (hadj : D.adjugate ≠ 0)
    (hu : IsCoordOn D 0 w u) : u = 0 := by
  have h0 : IsCoordOn D 0 w 0 := by simp [IsCoordOn]
  exact existing_scalar_unique D 0 w u 0 hadj hu h0

theorem zero_adjugate_loophole {K : Type} [Field K] (u : K) :
    IsCoordOn (0 : Matrix (Fin 2) (Fin 2) K) 0 0 u := by
  simp [IsCoordOn]

section BasisEquivalence

variable {K : Type} [Field K]
  {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type}
  [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3]
  [Fintype ι0'] [Fintype ι1'] [Fintype ι2'] [Fintype ι3']
  [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
  [DecidableEq ι0'] [DecidableEq ι1'] [DecidableEq ι2'] [DecidableEq ι3']
  {C : FourCx K ι0 ι1 ι2 ι3} {D : FourCx K ι0' ι1' ι2' ι3'}
  {zC : ι1 → K} {lC : ι2 → K} {zD : ι1' → K} {lD : ι2' → K}

/-- At nonzero target coordinate the uncomputed basis leaf restates coordinate equality. -/
theorem retained_basis_iff_coordinate_equality
    (H : HomotopyComparison C D zC lC zD lD)
    (hzC : C.d1 *ᵥ zC = 0) (hlC : lC ᵥ* C.d1 = 0)
    (hzD : D.d1 *ᵥ zD = 0) (hlD : lD ᵥ* D.d1 = 0)
    (σC : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))
    (σD : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit))
    (hcone : torsion (BasedCx.cone (H.augMap hzC hlC hzD hlD)) (σD.sumCongr σC.symm) ≠ 0)
    (hnz : kmCoord D zD lD hzD hlD σD ≠ 0) :
    (torsion (BasedCx.cone (H.augMap hzC hlC hzD hlD)) (σD.sumCongr σC.symm) =
      (-1) ^ Fintype.card (ι1 ⊕ (ι3 ⊕ Unit))) ↔
      kmCoord C zC lC hzC hlC σC = kmCoord D zD lD hzD hlD σD := by
  constructor
  · exact H.coordinate_eq_of_retained_basis hzC hlC hzD hlD σC σD
  · intro heq
    have hc := H.coordinate_in_original_basis hzC hlC hzD hlD σC σD hcone
    have hf : H.retainedFactor hzC hlC hzD hlD σC σD = 1 :=
      mul_right_cancel₀ hnz (hc.symm.trans (heq.trans (one_mul _).symm))
    have h := congrArg (fun x : K => x *
      torsion (BasedCx.cone (H.augMap hzC hlC hzD hlD)) (σD.sumCongr σC.symm)) hf
    unfold HomotopyComparison.retainedFactor at h
    rw [mul_assoc, inv_mul_cancel₀ hcone, mul_one, one_mul] at h
    exact h.symm

end BasisEquivalence

theorem same_disk_numeric_counterexample : (2 : ℚ)⁻¹ * 1 ≠ (2 : ℚ) * 1 :=
  ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.same_disk_factor_obstruction
    2 1 (by norm_num) (by norm_num) (by norm_num)

theorem no_integral_half_disk :
    ¬ ∃ E : Matrix (Fin 1) (Fin 1) ℤ,
      E.map (Int.castRingHom ℚ) =
        (Matrix.map (fun _ _ => (2 : ℤ) : Matrix (Fin 1) (Fin 1) ℤ) (Int.castRingHom ℚ))⁻¹ := by
  let D : Matrix (Fin 1) (Fin 1) ℤ := fun _ _ => 2
  have hD : IsUnit (D.map (Int.castRingHom ℚ)).det := by
    rw [Matrix.det_fin_one]
    change IsUnit (2 : ℚ)
    norm_num
  have hnot : ¬ IsUnit D.det := by
    rw [Matrix.det_fin_one]
    change ¬ IsUnit (2 : ℤ)
    rintro ⟨u, hu⟩
    rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num at hu
  exact ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.no_integral_inverse_disk_lift
    (Int.castRingHom ℚ) Int.cast_injective D hD hnot

section IntegralPole

open ZInQ.Manuscript.RC.Determinant (Lam)
open ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients

def poleDisk : Matrix (Fin 1) (Fin 1) Lam := fun _ _ => PowerSeries.X

/-- The inverse-disk obstruction occurs in the actual integral power-series realization at X. -/
theorem no_integral_X_inverse_disk :
    ¬ ∃ E : Matrix (Fin 1) (Fin 1) Lam,
      E.map integralToLaurent = (poleDisk.map integralToLaurent)⁻¹ := by
  have hX : (PowerSeries.X : Lam) ≠ 0 := by
    intro h
    have hc := congrArg (PowerSeries.coeff 1) h
    simp at hc
  have hD : IsUnit (poleDisk.map integralToLaurent).det := by
    rw [Matrix.det_fin_one]
    change IsUnit (integralToLaurent (PowerSeries.X : Lam))
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff integralToLaurent integralToLaurent_injective).mpr hX)
  have hnot : ¬ IsUnit poleDisk.det := by
    rw [Matrix.det_fin_one]
    change ¬ IsUnit (PowerSeries.X : Lam)
    intro h
    have hc : IsUnit (0 : ℤ_[2]) := by
      simpa using h.map (PowerSeries.constantCoeff : Lam →+* ℤ_[2])
    exact not_isUnit_zero hc
  exact ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.no_integral_inverse_disk_lift
    integralToLaurent integralToLaurent_injective poleDisk hD hnot

end IntegralPole

section ExactRegularEndpointObstruction

/-- The exact four-dimensional index of the unbound stored-endpoint exports. -/
abbrev EndpointIndex := Fin 0 ⊕ (Fin 2 ⊕ Fin 2)

def endpointPivot : EndpointIndex := Sum.inr (Sum.inl 0)

/-- One fixed corank-one matrix, independent of the scalar being prescribed. -/
def freeEndpointMatrix (R : Type) [CommRing R] : Matrix EndpointIndex EndpointIndex R :=
  Matrix.diagonal (fun i => if i = endpointPivot then 0 else 1)

/-- The fixed adjugate calculation was found in an independent review. -/
theorem freeEndpoint_adjugate (R : Type) [CommRing R] :
    (freeEndpointMatrix R).adjugate = Matrix.diagonal (Pi.single endpointPivot (1 : R)) := by
  rw [freeEndpointMatrix, Matrix.adjugate_diagonal]
  congr 1
  funext i
  by_cases hi : i = endpointPivot
  · subst i
    rw [Pi.single_eq_same]
    apply Finset.prod_eq_one
    intro j hj
    exact ite_eq_right (Finset.mem_erase.mp hj).1
  · rw [Pi.single_eq_of_ne hi]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hi, Finset.mem_univ endpointPivot⟩)
    exact ite_eq_left rfl

/-- The exact free regular-endpoint existential holds for every scalar, even
over a nontrivial commutative ring and without any step or actual Selmer data. -/
theorem exact_free_regular_endpoint_every_scalar (R : Type) [CommRing R] [Nontrivial R] (u : R) :
    ∃ (n : ℕ) (D : Matrix (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (Fin n ⊕ (Fin 2 ⊕ Fin 2)) R)
      (z w : Fin n ⊕ (Fin 2 ⊕ Fin 2) → R), IsCoordOn D z w u ∧ D.adjugate ≠ 0 := by
  refine ⟨0, freeEndpointMatrix R, Pi.single endpointPivot u, Pi.single endpointPivot 1, ?_, ?_⟩
  · unfold IsCoordOn
    rw [freeEndpoint_adjugate]
    ext i j
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal, Pi.single_apply]
    split_ifs <;> simp_all [eq_comm]
  · intro hzero
    have he := congrFun (congrFun hzero endpointPivot) endpointPivot
    rw [freeEndpoint_adjugate] at he
    simp at he

/-- Closedness of the free vectors also does not bind them to an actual endpoint. -/
theorem fixed_free_endpoint_closed (R : Type) [CommRing R] (u : R) :
    freeEndpointMatrix R *ᵥ Pi.single endpointPivot u = 0 ∧
      Pi.single endpointPivot (1 : R) ᵥ* freeEndpointMatrix R = 0 := by
  constructor
  · ext i
    by_cases hi : i = endpointPivot <;>
      simp [freeEndpointMatrix, Matrix.mulVec, dotProduct, Matrix.diagonal, Pi.single_apply, hi]
  · ext i
    by_cases hi : i = endpointPivot <;>
      simp [freeEndpointMatrix, Matrix.vecMul, dotProduct, Matrix.diagonal, Pi.single_apply, hi]

end ExactRegularEndpointObstruction

end ZInQ.Contrib.RC53Assist.CoordProvenance.ReviewObstructions
