import ZInQKernel.Contrib.OneProof.RC.O7Orbits.MaximalSplit

/-! Local ambient conjugacy and the quaternion centralizer, on-the-spot (c). -/

noncomputable section

open scoped Quaternion

namespace ZInQ.Manuscript.RC.LocalTorus

open O7Orbits Matrix LocalWeights

/-- The centralizer of a nonzero trace-zero quaternion over a field of
characteristic zero is its linear span with 1 (on-the-spot (c)). -/
theorem local_centralizer_span {K : Type*} [Field K] [CharZero K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    {x y : ℍ[K,a,0,b]} (hx : x.re = 0) (hx0 : x ≠ 0) (h : Commute y x) :
    ∃ t : K, y = algebraMap K (ℍ[K,a,0,b]) y.re + t • x := by
  have hI := congrArg QuaternionAlgebra.imI h.eq
  have hJ := congrArg QuaternionAlgebra.imJ h.eq
  have hK := congrArg QuaternionAlgebra.imK h.eq
  simp only [QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul,
    zero_mul, add_zero] at hI hJ hK
  have eJK : y.imJ * x.imK = y.imK * x.imJ := by
    apply mul_left_cancel₀ hb
    linear_combination -(1 / 2 : K) * hI
  have eIK : y.imI * x.imK = y.imK * x.imI := by
    apply mul_left_cancel₀ ha
    linear_combination (1 / 2 : K) * hJ
  have eIJ : y.imI * x.imJ = y.imJ * x.imI := by
    linear_combination (1 / 2 : K) * hK
  have finish (t : K) (hI : y.imI = t * x.imI) (hJ : y.imJ = t * x.imJ)
      (hK : y.imK = t * x.imK) : y = algebraMap K (ℍ[K,a,0,b]) y.re + t • x := by
    apply QuaternionAlgebra.ext
    · simp [QuaternionAlgebra.algebraMap_eq, hx, smul_eq_mul]
    · simpa [QuaternionAlgebra.algebraMap_eq, smul_eq_mul] using hI
    · simpa [QuaternionAlgebra.algebraMap_eq, smul_eq_mul] using hJ
    · simpa [QuaternionAlgebra.algebraMap_eq, smul_eq_mul] using hK
  have eqdiv (r s u v : K) (hv : v ≠ 0) (h : r * v = u * s) :
      r = u / v * s := by
    apply mul_right_cancel₀ hv
    rw [h, mul_right_comm, div_mul_cancel₀ _ hv]
  by_cases hI0 : x.imI = 0
  · by_cases hJ0 : x.imJ = 0
    · have hK0 : x.imK ≠ 0 := fun h => hx0 (QuaternionAlgebra.ext hx hI0 hJ0 h)
      exact ⟨y.imK / x.imK, finish _ (eqdiv _ _ _ _ hK0 eIK)
        (eqdiv _ _ _ _ hK0 eJK) (div_mul_cancel₀ _ hK0).symm⟩
    · exact ⟨y.imJ / x.imJ, finish _ (eqdiv _ _ _ _ hJ0 eIJ)
        (div_mul_cancel₀ _ hJ0).symm (eqdiv _ _ _ _ hJ0 eJK.symm)⟩
  · exact ⟨y.imI / x.imI, finish _ (div_mul_cancel₀ _ hI0).symm
      (eqdiv _ _ _ _ hI0 eIJ.symm) (eqdiv _ _ _ _ hI0 eIK.symm)⟩

/-- Two trace-one matrices with the same determinant are ambient conjugate
if neither is scalar. This is the split local form of Skolem–Noether
needed here, including the case of a split quadratic source. -/
theorem split_ambient_conj {K : Type*} [Field K] {X Y : Mat K}
    (hx : X.trace = 1) (hy : Y.trace = 1) (hd : X.det = Y.det)
    (hnx : ∀ a : K, X ≠ algebraMap K (Mat K) a)
    (hny : ∀ a : K, Y ≠ algebraMap K (Mat K) a) :
    ∃ u : (Mat K)ˣ, (↑u⁻¹ : _) * X * ↑u = Y := by
  have cyclic (A : Mat K) (hn : ∀ a : K, A ≠ algebraMap K (Mat K) a) :
      ∃ v w, IsUnit (cyclicColumns A v w) := by
    by_cases hc : A 1 0 = 0
    · by_cases hb : A 0 1 = 0
      · have hh : A 1 1 - A 0 0 ≠ 0 := by
          intro h
          have he := sub_eq_zero.mp h
          apply hn (A 0 0)
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.algebraMap_matrix_apply, hc, hb, he]
        exact ⟨1, 1, (Matrix.isUnit_iff_isUnit_det _).mpr
          (by simpa [cyclicColumns, det_fin_two, hc, hb] using isUnit_iff_ne_zero.mpr hh)⟩
      · exact ⟨0, 1, (Matrix.isUnit_iff_isUnit_det _).mpr
          (by simpa [cyclicColumns, det_fin_two] using (isUnit_iff_ne_zero.mpr hb).neg)⟩
    · exact ⟨1, 0, (Matrix.isUnit_iff_isUnit_det _).mpr
        (by simpa [cyclicColumns, det_fin_two] using isUnit_iff_ne_zero.mpr hc)⟩
  obtain ⟨v, w, hU⟩ := cyclic X hnx
  obtain ⟨v', w', hV⟩ := cyclic Y hny
  let U := hU.unit
  let V := hV.unit
  let C : Mat K := !![0, -X.det; 1, 1]
  have h (A : Mat K) (g : (Mat K)ˣ) (i j : K)
      (hg : (g : Mat K) = cyclicColumns A i j) (ht : A.trace = 1)
      (he : A.det = X.det) : (↑g⁻¹ : Mat K) * A * ↑g = C := by
    have hm : A * (g : Mat K) = (g : Mat K) * C := by
      rw [hg, cyclicColumns_companion A ht, he]
    rw [mul_assoc, hm, ← mul_assoc, Units.inv_mul, one_mul]
  have hX := h X U v w hU.unit_spec hx rfl
  have hY := h Y V v' w' hV.unit_spec hy hd.symm
  refine ⟨U * V⁻¹, ?_⟩
  rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
  calc
    _ = (V : Mat K) * ((↑U⁻¹ : Mat K) * X * ↑U) * ↑V⁻¹ := by noncomm_ring
    _ = Y := by rw [hX, ← hY, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul,
                    Units.mul_inv_cancel_right]

/-- In a division algebra two roots of the same scalar square are
ambient conjugate when the first root does not commute with some element.
This is the division local form of Skolem–Noether used here. -/
theorem division_ambient_conj {K A : Type*} [Field K] [DivisionRing A] [Algebra K A]
    {X Y : A} {d : K} (hx : X * X = algebraMap K A d)
    (hy : Y * Y = algebraMap K A d) (hn : ∃ w : A, X * w ≠ w * X) :
    ∃ u : Aˣ, (↑u⁻¹ : _) * X * ↑u = Y := by
  suffices h : ∃ v : A, v ≠ 0 ∧ X * v = v * Y by
    obtain ⟨v, hv, he⟩ := h
    let u := Units.mk0 v hv
    refine ⟨u, ?_⟩
    change (↑u⁻¹ : A) * X * ↑u = Y
    rw [mul_assoc]
    change (↑u⁻¹ : A) * (X * v) = Y
    rw [he, ← mul_assoc]
    change (↑u⁻¹ : A) * (u : A) * Y = Y
    rw [Units.inv_mul, one_mul]
  by_cases h : X + Y = 0
  · obtain ⟨w, hw⟩ := hn
    refine ⟨X * w - w * X, sub_ne_zero.mpr hw, ?_⟩
    rw [show Y = -X by exact eq_neg_of_add_eq_zero_right h]
    rw [mul_sub, sub_mul, mul_neg, mul_neg, ← mul_assoc X X w, mul_assoc w X X, hx]
    have hc := Algebra.commutes (A := A) d w
    rw [hc, mul_assoc X w X]
    abel
  · refine ⟨X + Y, h, ?_⟩
    rw [mul_add, add_mul, hx, hy, add_comm]

end ZInQ.Manuscript.RC.LocalTorus
