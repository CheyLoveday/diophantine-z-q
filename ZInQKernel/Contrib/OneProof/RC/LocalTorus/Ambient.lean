import ZInQKernel.Contrib.OneProof.RC.PicardFibers.Assembly
import ZInQKernel.Contrib.OneProof.RC.LocalTorus.Conjugacy

/-! Local ambient conjugacy for the reference generator (tex 9155–9156).
The elementary intertwiners are on-the-spot (c). -/

noncomputable section

set_option maxHeartbeats 600000

open scoped Quaternion

namespace ZInQ.Manuscript.RC.LocalTorus

open Eichler Adelic O7Actual O7Orbits PicardFibers Matrix LocalWeights

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m : ℤ}
variable {F : Type} [Field F] [NumberField F]

/-- The reference root remains trace zero, with the same scalar square
after rational completion. -/
theorem local_reference_root (s : StageAt O N M hN m) {D : ℤ}
    (A : AdmissibleD s D) (Q : QuadraticBasis F (disc s D))
    (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ))) (p : Prime) :
    let x := toLocal p.val (referenceUnit s A Q ι).val
    x.re = 0 ∧ x * x = (disc s D : Bp p.val (-1) (-(s.ell : ℚ))) ∧ x ≠ 0 := by
  let x := (referenceUnit s A Q ι).val
  have hr := (referenceUnit_sphere s A Q ι).1
  have hs : x * x = (disc s D : B (-1) (-(s.ell : ℚ))) := by
    change ι (Q.model QuadraticAlgebra.omega) * ι (Q.model QuadraticAlgebra.omega) = _
    have hω : (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (disc s D : ℚ) 0) *
        QuadraticAlgebra.omega = algebraMap ℚ _ (disc s D : ℚ) := by
      simp [QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    rw [← map_mul, ← map_mul, hω, AlgEquiv.commutes, AlgHom.commutes, map_intCast]
  have hsq : toLocal p.val x * toLocal p.val x =
      (disc s D : Bp p.val (-1) (-(s.ell : ℚ))) := by rw [← map_mul, hs, map_intCast]
  refine ⟨by change (x.re : ℚ_[p.val]) = 0; rw [hr, Rat.cast_zero], hsq, ?_⟩
  intro hz
  rw [hz, zero_mul] at hsq
  have hh : (0 : ℚ_[p.val]) = (disc s D : ℚ_[p.val]) := by
    simpa only [QuaternionAlgebra.re_zero, QuaternionAlgebra.re_intCast] using
      congrArg QuaternionAlgebra.re hsq
  exact A.disc_neg.ne (Int.cast_eq_zero.mp hh.symm)

/-- The local affine generator has characteristic polynomial T² - T + c
in the split chart. -/
theorem split_reference (s : StageAt O N M hN m) {D c : ℤ}
    (A : AdmissibleD s D) (Q : QuadraticBasis F (disc s D))
    (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ))) (hc : disc s D = 1 - 4 * c)
    (p : Prime) (hp : p.val ≠ s.ell) :
    let X := splitChart s.ell s.mod_four p hp (toLocal p.val (referenceAffine s Q ι))
    X.trace = 1 ∧ X.det = (c : ℚ_[p.val]) ∧
      ∀ a : ℚ_[p.val], X ≠ algebraMap ℚ_[p.val] (Mat ℚ_[p.val]) a := by
  let g := splitChart s.ell s.mod_four p hp
  let x := toLocal p.val (referenceUnit s A Q ι).val
  let W := toLocal p.val (referenceAffine s Q ι)
  let X := g W
  have hα : 2 * W - 1 = x := by
    simpa only [map_sub, map_mul, map_ofNat, map_one] using
      congrArg (toLocal p.val) (referenceAffine_spec s A Q ι)
  obtain ⟨hr, hs, hn⟩ := local_reference_root s A Q ι p
  have hns (a : ℚ_[p.val]) : X ≠ algebraMap ℚ_[p.val] (Mat ℚ_[p.val]) a := by
    intro h
    have hW : W = algebraMap ℚ_[p.val] (Bp p.val (-1) (-(s.ell : ℚ))) a :=
      g.injective (h.trans (g.commutes a).symm)
    have hx : x = algebraMap ℚ_[p.val] (Bp p.val (-1) (-(s.ell : ℚ))) (2 * a - 1) := by
      rw [← hα, hW, map_sub, map_mul, map_ofNat, map_one]
    have hh : x.re = 2 * a - 1 := congrArg QuaternionAlgebra.re hx
    apply hn
    change x = 0
    change x.re = 0 at hr
    rw [hx, ← hh, hr, map_zero]
  have hsq : (2 * X - 1) ^ 2 = (disc s D : Mat ℚ_[p.val]) := by
    have hh : g ((2 * W - 1) ^ 2) = g (disc s D : Bp p.val (-1) (-(s.ell : ℚ))) := by
      rw [hα, pow_two, hs]
    simpa only [map_pow, map_sub, map_mul, map_ofNat, map_one, map_intCast] using hh
  have eq : X * X - X + algebraMap ℚ_[p.val] (Mat ℚ_[p.val]) (c : ℚ_[p.val]) = 0 := by
    rw [hc, Int.cast_sub, Int.cast_mul, Int.cast_one, Int.cast_ofNat,
      ← map_intCast (algebraMap ℚ_[p.val] (Mat ℚ_[p.val])) c] at hsq
    have hu : IsUnit (4 : Mat ℚ_[p.val]) := by
      simpa only [map_ofNat] using
        (isUnit_iff_ne_zero.mpr (by norm_num : (4 : ℚ_[p.val]) ≠ 0)).map
          (algebraMap ℚ_[p.val] (Mat ℚ_[p.val]))
    apply hu.mul_left_cancel
    rw [mul_zero]
    calc
      _ = (2 * X - 1) ^ 2 - (1 - 4 * (algebraMap ℚ_[p.val] (Mat ℚ_[p.val])) (c : ℚ_[p.val])) := by
        noncomm_ring
      _ = 0 := sub_eq_zero.mpr hsq
  obtain ⟨ht, he⟩ := matrix_trace_det_of_affine X (c : ℚ_[p.val]) eq hns
  exact ⟨ht, he, hns⟩

end ZInQ.Manuscript.RC.LocalTorus
