import ZInQKernel.Contrib.OneProof.RC.O7Orbits.Actual

/-! Read the affine quadratic relation in the actual split order chart. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O7Orbits

open Eichler Visibility Matrix LocalWeights

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m : ℤ}

theorem splitOrderChart_compatible (s : O7Actual.StageAt O N M hN m) (p : Adelic.Prime)
    (hp : p.val ≠ s.ell) (y : (ActualOrder s).completion p.val) :
    matrixCast p.val (splitOrderChart s p hp y).val =
      Adelic.splitChart s.ell s.mod_four p hp y.val := by
  let f := Adelic.splitChart s.ell s.mod_four p hp
  let e := splitOrderChart s p hp
  have h := congrArg Subtype.val (e.symm_apply_apply y)
  change f.symm (matrixCast p.val (e y).val) = y.val at h
  exact f.symm_apply_eq.mp h

/-- The trace-zero norm condition of the actual support gives the same
quadratic relation in every integral local chart. -/
theorem localGenerator_square (s : O7Actual.StageAt O N M hN m) {D : ℤ} (H : SupportBridge s D)
    (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z) (p : Adelic.Prime) :
    (2 * localGenerator s H z x p - 1) ^ 2 = (disc s D : (ActualOrder s).completion p.val) := by
  have hx : x.val ^ 2 = (disc s D : B (-1) (-(s.ell : ℚ))) := by
    rw [pow_two, ← map_intCast (algebraMap ℚ (B (-1) (-(s.ell : ℚ))))]
    simp only [disc, Int.cast_mul, Int.cast_neg, Int.cast_natCast]
    apply (nrd_eq_mul_iff x.prop.1 (s.weights.m : ℚ) (D : ℚ) (-(s.weights.m : ℚ)) rfl).mp
    simpa only [index, Int.cast_mul, Int.cast_natCast] using x.prop.2.1
  apply Subtype.ext
  let v := (Adelic.classRepresentative z).val p
  let f := (unitConjRing v⁻¹).comp (toLocal p.val)
  change (2 * (localGenerator s H z x p).val - 1) ^ 2 =
    (disc s D : Bp p.val (-1) (-(s.ell : ℚ)))
  rw [localGenerator_spec]
  change (f x.val) ^ 2 = _
  rw [← map_pow, hx, map_intCast]

/-- On-the-spot (c): a nonscalar solution of the affine quadratic
equation in a two-by-two matrix ring over a field has the stipulated
trace and determinant. -/
theorem matrix_trace_det_of_affine {K : Type*} [Field K] (Y : Mat K) (c : K)
    (h : Y * Y - Y + algebraMap K (Mat K) c = 0)
    (hns : ∀ t : K, Y ≠ algebraMap K (Mat K) t) :
    Y.trace = 1 ∧ Y.det = c := by
  have hch : Y * Y - Y.trace • Y + algebraMap K (Mat K) Y.det = 0 := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
        Matrix.algebraMap_matrix_apply] <;> ring
  have he : (Y.trace - 1) • Y = algebraMap K (Mat K) (Y.det - c) := by
    apply sub_eq_zero.mp
    calc
      _ = (Y * Y - Y + algebraMap K (Mat K) c) -
          (Y * Y - Y.trace • Y + algebraMap K (Mat K) Y.det) := by
        rw [sub_smul, one_smul, map_sub]
        abel
      _ = 0 := by rw [h, hch, sub_self]
  have ht : Y.trace = 1 := by
    by_contra hn
    apply hns ((Y.trace - 1)⁻¹ * (Y.det - c))
    calc
      Y = (Y.trace - 1)⁻¹ • ((Y.trace - 1) • Y) := by
        rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hn), one_smul]
      _ = _ := by rw [he, Algebra.smul_def, ← map_mul]
  refine ⟨ht, sub_eq_zero.mp ?_⟩
  rw [ht, sub_self, zero_smul] at he
  exact (RingHom.injective (algebraMap K (Mat K))) (he.symm.trans (map_zero _).symm)

set_option maxHeartbeats 350000 in
/-- At a split place the actual support generator has characteristic
polynomial `T²-T+c`, where `disc = 1-4c`. -/
theorem split_generator_trace_det (s : O7Actual.StageAt O N M hN m) {D c : ℤ}
    (H : SupportBridge s D) (hc : disc s D = 1 - 4 * c) (hd : disc s D ≠ 0)
    (p : Adelic.Prime) (hp : p.val ≠ s.ell)
    (z : ClassSet (ActualOrder s)) (x : ActualSupport s D z) :
    let Y := splitOrderChart s p hp (localGenerator s H z x p)
    Y.val.trace = 1 ∧ Y.val.det = (c : ℤ_[p.val]) := by
  let f := Adelic.splitChart s.ell s.mod_four p hp
  let v := (Adelic.classRepresentative z).val p
  let Y := localGenerator s H z x p
  let W := f Y.val
  let A := (splitOrderChart s p hp Y).val
  have hW : matrixCast p.val A = W := splitOrderChart_compatible s p hp Y
  have hsq : (2 * W - 1) ^ 2 = (disc s D : Mat ℚ_[p.val]) := by
    have h := congrArg (f ∘ Subtype.val) (localGenerator_square s H z x p)
    change f ((2 * Y.val - 1) ^ 2) = f (disc s D : Bp p.val (-1) (-(s.ell : ℚ))) at h
    simpa only [map_pow, map_sub, map_mul, map_ofNat, map_one, map_intCast] using h
  have eq : W * W - W + algebraMap ℚ_[p.val] (Mat ℚ_[p.val]) (c : ℚ_[p.val]) = 0 := by
    have h := hsq
    rw [hc, Int.cast_sub, Int.cast_mul, Int.cast_one, Int.cast_ofNat,
      ← map_intCast (algebraMap ℚ_[p.val] (Mat ℚ_[p.val])) c] at h
    have hu : IsUnit (4 : Mat ℚ_[p.val]) := by
      simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (4 : ℚ_[p.val]) ≠ 0)).map
        (algebraMap ℚ_[p.val] (Mat ℚ_[p.val]))
    apply hu.mul_left_cancel
    rw [mul_zero]
    calc
      _ = (2 * W - 1) ^ 2 - (1 - 4 * (algebraMap ℚ_[p.val] (Mat ℚ_[p.val])) c) := by
        noncomm_ring
      _ = 0 := sub_eq_zero.mpr h
  have hn (t : ℚ_[p.val]) : W ≠ algebraMap ℚ_[p.val] (Mat ℚ_[p.val]) t := by
    intro h
    have hY : Y.val = algebraMap ℚ_[p.val] (Bp p.val (-1) (-(s.ell : ℚ))) t :=
      f.injective (h.trans (f.commutes t).symm)
    have hxin : unitConjRing v⁻¹ (toLocal p.val x.val) =
        algebraMap ℚ_[p.val] (Bp p.val (-1) (-(s.ell : ℚ))) (2 * t - 1) := by
      rw [← localGenerator_spec s H z x p]
      change 2 * Y.val - 1 = _
      rw [hY, map_sub, map_mul, map_ofNat, map_one]
    have hscalar : toLocal p.val x.val =
        algebraMap ℚ_[p.val] (Bp p.val (-1) (-(s.ell : ℚ))) (2 * t - 1) := by
      have ht := congrArg (unitConjRing v) hxin
      rw [unitConjRing_mul, mul_inv_cancel, unitConjRing_apply,
        Units.val_one, inv_one, Units.val_one, one_mul, mul_one] at ht
      rw [ht, unitConjRing_apply, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]
    have hi := congrArg QuaternionAlgebra.imI hscalar
    have hj := congrArg QuaternionAlgebra.imJ hscalar
    have hk := congrArg QuaternionAlgebra.imK hscalar
    change (x.val.imI : ℚ_[p.val]) = 0 at hi
    change (x.val.imJ : ℚ_[p.val]) = 0 at hj
    change (x.val.imK : ℚ_[p.val]) = 0 at hk
    have hx0 : x.val = 0 := by
      apply QuaternionAlgebra.ext x.prop.1
      · change x.val.imI = 0
        exact Rat.cast_injective (by simpa only [Rat.cast_zero] using hi)
      · change x.val.imJ = 0
        exact Rat.cast_injective (by simpa only [Rat.cast_zero] using hj)
      · change x.val.imK = 0
        exact Rat.cast_injective (by simpa only [Rat.cast_zero] using hk)
    have hs := localGenerator_spec s H z x p
    rw [hx0, map_zero, map_zero] at hs
    change 2 * Y.val - 1 = 0 at hs
    have hz := congrArg f hs
    rw [map_sub, map_mul, map_ofNat, map_one, map_zero] at hz
    change 2 * W - 1 = 0 at hz
    rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hsq
    have hz' := congrArg (fun A : Mat ℚ_[p.val] => A 0 0) hsq
    have hz'' : (0 : ℚ_[p.val]) = (disc s D : ℚ_[p.val]) := by
      exact hz'
    exact hd (Int.cast_eq_zero.mp hz''.symm)
  obtain ⟨ht, he⟩ := matrix_trace_det_of_affine W (c : ℚ_[p.val]) eq hn
  rw [← hW] at ht he
  change A.trace = 1 ∧ A.det = _
  constructor
  · apply Subtype.val_injective
    rw [Matrix.trace_fin_two] at ht
    change (↑(A 0 0) : ℚ_[p.val]) + ↑(A 1 1) = 1 at ht
    rw [Matrix.trace_fin_two, PadicInt.coe_add]
    exact ht
  · apply Subtype.val_injective
    rw [show matrixCast p.val A = (PadicInt.Coe.ringHom (p := p.val)).mapMatrix A from rfl,
      ← RingHom.map_det] at he
    exact he

end ZInQ.Manuscript.RC.O7Orbits
