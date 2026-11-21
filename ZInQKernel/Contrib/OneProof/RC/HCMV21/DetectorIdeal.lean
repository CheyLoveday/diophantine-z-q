import ZInQKernel.Contrib.OneProof.RC.HCMV21.RamifiedCoset
import ZInQKernel.Contrib.OneProof.RC.HCMV21.RightIdealCoordinates
import Mathlib.RingTheory.TensorProduct.Maps

/-! At the detector, the level is a unit. The common completed
level-one order is the valuation order of the division algebra.
Its principal right ideals and its residue characters are read in
that order (tex 9146–9148, 9249–9255). -/

namespace ZInQ.Manuscript.RC.HCMV21

open LocalDivision
open scoped TensorProduct

variable {q : ℕ} [Fact q.Prime]

/-- Extend a geometric scalar character to the completed integral
endomorphism ring. The coefficient action uses reduction modulo `q`. -/
noncomputable def completeScalarCharacter {R k : Type*} [Ring R] [Field k] [CharP k q]
    (χ : R →+* k) : (ℤ_[q] ⊗[ℤ] R) →+* k :=
  (Algebra.TensorProduct.lift
      (((ZMod.castHom (dvd_refl q) k).comp PadicInt.toZMod).toIntAlgHom)
      χ.toIntAlgHom (fun _ _ => Commute.all _ _)).toRingHom

@[simp] theorem completeScalarCharacter_one_tmul {R k : Type*}
    [Ring R] [Field k] [CharP k q] (χ : R →+* k) (x : R) :
    completeScalarCharacter (q := q) χ ((1 : ℤ_[q]) ⊗ₜ[ℤ] x) = χ x := by
  simp [completeScalarCharacter]

/-- The tangent character of the level-one geometric endomorphism
ring, once its completion is placed in division coordinates, is the
reduction character followed by a unique residue-field embedding. -/
theorem completeScalarCharacter_factors {R k : Type*} [Ring R] [Field k] [CharP k q]
    [Fact (q % 4 = 3)] (χ : R →+* k) (e : (ℤ_[q] ⊗[ℤ] R) ≃+* order q) :
    ∃! j : GaloisField q 2 →+* k,
      j.comp ((red (p := q)).comp e.toRingHom) = completeScalarCharacter χ := by
  rcases division_scalar_factors ((completeScalarCharacter χ).comp e.symm.toRingHom) with
    ⟨j, hj, huniq⟩
  refine ⟨j, RingHom.ext fun x => ?_, fun j' hj' => huniq j' (RingHom.ext fun x => ?_)⟩
  · change j (red (e x)) = completeScalarCharacter χ x
    have hh := DFunLike.congr_fun hj (e x)
    change j (red (e x)) = completeScalarCharacter χ (e.symm (e x)) at hh
    simpa only [RingEquiv.symm_apply_apply] using hh
  · change j' (red x) = completeScalarCharacter χ (e.symm x)
    have hh := DFunLike.congr_fun hj' (e.symm x)
    change j' (red (e (e.symm x))) = completeScalarCharacter χ (e.symm x) at hh
    simpa only [RingEquiv.apply_symm_apply] using hh

variable [Fact (q % 4 = 3)]

/-- In the explicit division algebra, any maximal finite order is the
valuation order. Each element of a finite subalgebra is integral. -/
theorem detector_order_eq_of_maximal (S : Subalgebra ℤ_[q] (D q))
    (hS : Module.Finite ℤ_[q] S)
    (hmax : ∀ T : Subalgebra ℤ_[q] (D q), Module.Finite ℤ_[q] T → S ≤ T → T ≤ S) :
    S = order q := by
  have h : S ≤ order q := fun x hx => integral_mem_order
    ((isIntegral_algHom_iff S.val Subtype.val_injective).mpr (IsIntegral.of_finite ℤ_[q] (⟨x, hx⟩ : S)))
  exact le_antisymm h (hmax _ finite_order h)

/-- The left order of a principal detector ideal is again the valuation
order, since conjugation preserves reduced norm. -/
theorem detector_leftOrder_eq (g : (D q)ˣ) (x : D q) :
    Set.MapsTo (fun y : D q => x * y)
      ((fun r : D q => (g : D q) * r) '' (order q : Set (D q)))
      ((fun r : D q => (g : D q) * r) '' (order q : Set (D q))) ↔ x ∈ order q := by
  rw [show (order q : Set (D q)) = (order q).toSubring from rfl,
    preserves_principalRightIdeal_iff]
  change (↑g⁻¹ : D q) * x * (g : D q) ∈ order q ↔ x ∈ order q
  rw [mem_order_iff_nrd, mem_order_iff_nrd, nrd_conj]

/-- Every nonzero finite right lattice over the detector order is
principal. Choose a generator of largest reduced-norm absolute value
among a finite set of integral generators. -/
theorem detector_rightLattice_principal
    (I : Submodule ℤ_[q] (D q)) (hI : I.FG) (hn : I ≠ ⊥)
    (hr : ∀ x ∈ I, ∀ r ∈ order q, x * r ∈ I) :
    ∃ g : (D q)ˣ, (I : Set (D q)) = (fun r : D q => (g : D q) * r) '' (order q : Set (D q)) := by
  classical
  obtain ⟨S, hS⟩ := hI
  have hSle : (S : Set (D q)) ⊆ I := by rw [← hS]; exact Submodule.subset_span
  have hpos : ∃ x ∈ (S : Set (D q)), x ≠ 0 := by
    by_contra! h
    exact hn (le_bot_iff.mp (hS ▸ Submodule.span_le.mpr fun x hx => by simp [h x hx]))
  obtain ⟨x, hxS, hx⟩ := hpos
  obtain ⟨y, hyS, hy⟩ := Set.exists_max_image (S : Set (D q)) (fun z => ‖nrd z‖)
    S.finite_toSet ⟨x, hxS⟩
  have hy₀ : y ≠ 0 := by
    intro he
    have := hy x hxS
    have hz : nrd (0 : D q) = 0 := (nrd_eq_zero _).mpr rfl
    rw [he, hz, norm_zero, norm_le_zero_iff, nrd_eq_zero] at this
    exact hx this
  let g := unitOfNonzero y hy₀
  refine ⟨g, Set.Subset.antisymm ?_ ?_⟩
  · have hmul (z : D q) : (↑g⁻¹ : D q) * z ∈ order q ↔ ‖nrd z‖ ≤ ‖nrd y‖ := by
      have hg : nrd (↑g⁻¹ : D q) * nrd y = 1 := by
        rw [← map_mul]
        change nrd ((↑g⁻¹ : D q) * (g : D q)) = 1
        rw [Units.inv_mul, map_one]
      have hnorm : ‖nrd (↑g⁻¹ : D q)‖ * ‖nrd y‖ = 1 := by
        rw [← norm_mul, hg, norm_one]
      have hp : 0 < ‖nrd (↑g⁻¹ : D q)‖ :=
        norm_pos_iff.mpr (mt (nrd_eq_zero _).mp (g⁻¹).ne_zero)
      rw [mem_order_iff_nrd, map_mul, norm_mul, ← hnorm, mul_le_mul_iff_right₀ hp]
    have hgen (z : D q) (hz : z ∈ I) : (↑g⁻¹ : D q) * z ∈ order q := by
      rw [← hS] at hz
      induction hz using Submodule.span_induction with
      | mem z hz => exact (hmul z).mpr (hy z hz)
      | zero => rw [mul_zero]; exact (order q).zero_mem
      | add z w _ _ hz hw => rw [mul_add]; exact (order q).add_mem hz hw
      | smul a z _ hz =>
        rw [Algebra.mul_smul_comm]
        exact (order q).smul_mem hz a
    intro z hz
    refine ⟨_, hgen z hz, ?_⟩
    change (g : D q) * ((↑g⁻¹ : D q) * z) = z
    rw [← mul_assoc, Units.mul_inv, one_mul]
  · rintro _ ⟨r, h, rfl⟩
    exact hr y (hSle hyS) r h

end ZInQ.Manuscript.RC.HCMV21
