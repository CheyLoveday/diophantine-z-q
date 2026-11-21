import Mathlib.Algebra.Quaternion
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Two algebraic parts of the stabilizer calculation (tex 9127–9131,
9161–9166). The centralizer fixes every label, and the maximal order
of the quadratic algebra is recovered by intersecting an integral order. -/

namespace ZInQ.Manuscript.RC.HCMV21

open scoped Quaternion

/-- In `(a,b)`, a quaternion commuting with a nonscalar `x` belongs
to the span of `1,x`. Written over a field so this can also be used at a
completion. -/
theorem eq_scalar_add_smul_of_commute {k : Type*} [Field k] [NeZero (2 : k)]
    {a b : k} (ha : a ≠ 0) (hb : b ≠ 0) {x y : ℍ[k,a,0,b]}
    (hx : x.imI ≠ 0 ∨ x.imJ ≠ 0 ∨ x.imK ≠ 0) (h : Commute y x) :
    ∃ r s : k, y = algebraMap k ℍ[k,a,0,b] r + s • x := by
  have h2 : (2 : k) ≠ 0 := NeZero.ne _
  have hI := congrArg QuaternionAlgebra.imI h.eq
  have hJ := congrArg QuaternionAlgebra.imJ h.eq
  have hK := congrArg QuaternionAlgebra.imK h.eq
  simp only [QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul,
    zero_mul, add_zero] at hI hJ hK
  have hIJ : y.imI * x.imJ = y.imJ * x.imI := by
    apply mul_left_cancel₀ h2
    linear_combination hK
  have hJK : y.imJ * x.imK = y.imK * x.imJ := by
    apply mul_left_cancel₀ (mul_ne_zero h2 hb)
    linear_combination -hI
  have hIK : y.imI * x.imK = y.imK * x.imI := by
    apply mul_left_cancel₀ (mul_ne_zero h2 ha)
    linear_combination hJ
  have build (s : k) (hi : y.imI = s * x.imI) (hj : y.imJ = s * x.imJ)
      (hk : y.imK = s * x.imK) : ∃ r t : k, y = algebraMap k ℍ[k,a,0,b] r + t • x := by
    refine ⟨y.re - s * x.re, s, QuaternionAlgebra.ext ?_ ?_ ?_ ?_⟩
    · simp [QuaternionAlgebra.algebraMap_eq, smul_eq_mul]
    · simpa [QuaternionAlgebra.algebraMap_eq, smul_eq_mul] using hi
    · simpa [QuaternionAlgebra.algebraMap_eq, smul_eq_mul] using hj
    · simpa [QuaternionAlgebra.algebraMap_eq, smul_eq_mul] using hk
  have slope {p q u v : k} (hv : v ≠ 0) (he : p * v = u * q) : p = u / v * q := by
    apply mul_right_cancel₀ hv
    rw [he, mul_right_comm, div_mul_cancel₀ _ hv]
  rcases hx with hi | hj | hk
  · exact build _ (div_mul_cancel₀ _ hi).symm (slope hi hIJ.symm) (slope hi hIK.symm)
  · exact build _ (slope hj hIJ) (div_mul_cancel₀ _ hj).symm (slope hj hJK.symm)
  · exact build _ (slope hk hIK) (slope hk hJK) (div_mul_cancel₀ _ hk).symm

/-- A rational (or local) quaternion unit preserving all the labels of
an embedded field comes from a unit of that field. This is a pointwise
centralizer statement; it does not allow conjugating the labels. -/
theorem commute_units_iff_mem_fieldUnits
    {k F : Type*} [Field k] [NeZero (2 : k)] [Field F] [Algebra k F]
    {a b : k} (ha : a ≠ 0) (hb : b ≠ 0) (ι : F →ₐ[k] ℍ[k,a,0,b])
    (x : F) (hx : (ι x).imI ≠ 0 ∨ (ι x).imJ ≠ 0 ∨ (ι x).imK ≠ 0)
    (u : ℍ[k,a,0,b]ˣ) :
    (∀ t : F, Commute (u : ℍ[k,a,0,b]) (ι t)) ↔
      u ∈ (Units.map ι.toMonoidHom).range := by
  constructor
  · intro h
    obtain ⟨r, s, he⟩ := eq_scalar_add_smul_of_commute ha hb hx (h x)
    let v := algebraMap k F r + s • x
    have hv : ι v = u := by simp only [v, map_add, AlgHom.commutes, map_smul]; exact he.symm
    have hv0 : v ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hv
      exact u.ne_zero hv.symm
    exact ⟨Units.mk0 v hv0, Units.ext hv⟩
  · rintro ⟨v, rfl⟩ t
    exact (Commute.all (v : F) t).map ι.toMonoidHom

/-- If an order contains the integral closure of the base in the
embedded field (or split algebra), it intersects that algebra in
exactly this integral closure. Finiteness is used only on the order. -/
theorem comap_order_eq_integralClosure {R F B : Type*} [CommRing R] [CommRing F]
    [Ring B] [Algebra R F] [Algebra R B] (ι : F →ₐ[R] B) (hi : Function.Injective ι)
    (S : Subalgebra R B) [Module.Finite R S]
    (hS : integralClosure R F ≤ S.comap ι) :
    S.comap ι = integralClosure R F := by
  refine le_antisymm (fun x hx => ?_) hS
  change IsIntegral R x
  apply (isIntegral_algHom_iff ι hi).mp
  exact (Subalgebra.isIntegral_iff S).mp inferInstance (ι x) hx

/-- Apply the integral-closure intersection both to a unit and to its
inverse. This is the local right stabilizer calculation. -/
theorem isOrderUnit_iff_isIntegral_and_inv {R F B : Type*}
    [CommRing R] [CommRing F] [Ring B] [Algebra R F] [Algebra R B]
    (ι : F →ₐ[R] B) (hi : Function.Injective ι)
    (S : Subalgebra R B) [Module.Finite R S] (hS : integralClosure R F ≤ S.comap ι)
    (u : Fˣ) :
    (ι (u : F) ∈ S ∧ ι (↑u⁻¹ : F) ∈ S) ↔
      IsIntegral R (u : F) ∧ IsIntegral R (↑u⁻¹ : F) := by
  change ((u : F) ∈ S.comap ι ∧ (↑u⁻¹ : F) ∈ S.comap ι) ↔ _
  rw [comap_order_eq_integralClosure ι hi S hS]
  rfl

end ZInQ.Manuscript.RC.HCMV21
