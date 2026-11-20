import ZInQKernel.Contrib.OneProof.RC.PicardFibers.TorusComparison
import ZInQKernel.Contrib.OneProof.RC.PicardFibers.Realization

/-! Supply the actual orbit-fiber input, conditional only on the local
realization and completed quadratic torus arithmetic. -/

noncomputable section

set_option maxHeartbeats 1000000

open scoped NumberField

namespace ZInQ.Manuscript.RC.PicardFibers

open Eichler Adelic O7Actual O7Orbits Visibility

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m : ℤ}
variable {F : Type} [Field F] [NumberField F]

theorem AdmissibleD.disc_neg {s : StageAt O N M hN m} {D : ℤ} (A : AdmissibleD s D) :
    disc s D < 0 :=
  lt_of_le_of_ne (show disc s D ≤ 0 from mul_nonpos_of_nonneg_of_nonpos A.positive.le
    (neg_nonpos.mpr (Int.natCast_nonneg _))) A.disc_squarefree.ne_zero

/-- The image of the integral affine generator in a chosen rational
embedding. The embedding can be chosen by the existing
`O7Orbits.exists_reference_embedding`. -/
def referenceAffine (s : StageAt O N M hN m) {D : ℤ}
    (Q : QuadraticBasis F (disc s D)) (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ))) :
    B (-1) (-(s.ell : ℚ)) :=
  ι ((1 + Q.model QuadraticAlgebra.omega) / 2)

private theorem reference_sq (s : StageAt O N M hN m) {D : ℤ}
    (Q : QuadraticBasis F (disc s D)) (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ))) :
    let x := ι (Q.model QuadraticAlgebra.omega)
    x * x = algebraMap ℚ (B (-1) (-(s.ell : ℚ))) (disc s D : ℚ) := by
  dsimp only
  have h : (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (disc s D : ℚ) 0) *
      QuadraticAlgebra.omega = algebraMap ℚ _ (disc s D : ℚ) := by
    simp [QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  rw [← map_mul, ← map_mul, h, AlgEquiv.commutes, AlgHom.commutes]

/-- The reference root is nonzero because its square is a nonzero rational. -/
def referenceUnit (s : StageAt O N M hN m) {D : ℤ}
    (A : AdmissibleD s D) (Q : QuadraticBasis F (disc s D))
    (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ))) : (B (-1) (-(s.ell : ℚ)))ˣ :=
  unitOfNeZero s.weights.ha s.weights.hb (ι (Q.model QuadraticAlgebra.omega)) (by
    intro h
    have hs := reference_sq s Q ι
    dsimp only at hs
    rw [h, zero_mul] at hs
    have hd : (0 : ℚ) = (disc s D : ℚ) := congrArg QuaternionAlgebra.re hs
    exact A.disc_neg.ne ((Int.cast_injective (α := ℚ))
      (hd.symm.trans (Int.cast_zero : ((0 : ℤ) : ℚ) = 0).symm)))

theorem referenceAffine_spec (s : StageAt O N M hN m) {D : ℤ}
    (A : AdmissibleD s D) (Q : QuadraticBasis F (disc s D))
    (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ))) :
    2 * referenceAffine s Q ι - 1 = (referenceUnit s A Q ι).val := by
  have h : 2 * ((1 + Q.model QuadraticAlgebra.omega) / 2) - 1 =
      Q.model QuadraticAlgebra.omega := by ring
  change 2 * referenceAffine s Q ι - 1 = ι (Q.model QuadraticAlgebra.omega)
  simpa only [referenceAffine, map_sub, map_mul, map_one, map_ofNat] using congrArg ι h

/-- A nonscalar square root of a negative rational has reduced trace zero
and the prescribed positive norm (tex 9123–9124 and 9150–9151). -/
theorem referenceUnit_sphere (s : StageAt O N M hN m) {D : ℤ}
    (A : AdmissibleD s D) (Q : QuadraticBasis F (disc s D))
    (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ))) :
    (referenceUnit s A Q ι).val.re = 0 ∧ nrd (referenceUnit s A Q ι).val = index s D := by
  let x := (referenceUnit s A Q ι).val
  have hs : x * x = algebraMap ℚ (B (-1) (-(s.ell : ℚ))) (disc s D : ℚ) :=
    reference_sq s Q ι
  have hd : (disc s D : ℚ) < 0 := by exact_mod_cast A.disc_neg
  have hx : x.re = 0 := by
    by_contra h
    have hi := congrArg QuaternionAlgebra.imI hs
    have hj := congrArg QuaternionAlgebra.imJ hs
    have hk := congrArg QuaternionAlgebra.imK hs
    simp only [QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul,
      QuaternionAlgebra.algebraMap_eq] at hi hj hk
    have eI : x.re * x.imI = 0 := by linear_combination hi / 2
    have eJ : x.re * x.imJ = 0 := by linear_combination hj / 2
    have eK : x.re * x.imK = 0 := by linear_combination hk / 2
    have he := congrArg QuaternionAlgebra.re hs
    simp [QuaternionAlgebra.re_mul, QuaternionAlgebra.algebraMap_eq,
      (mul_eq_zero.mp eI).resolve_left h, (mul_eq_zero.mp eJ).resolve_left h,
      (mul_eq_zero.mp eK).resolve_left h] at he
    have he' : x.re * x.re = (disc s D : ℚ) := by
      simpa only [disc, Int.cast_mul, Int.cast_neg, Int.cast_natCast, mul_neg] using he
    exact hd.not_ge (he' ▸ mul_self_nonneg x.re)
  refine ⟨hx, ?_⟩
  simpa only [index, Int.cast_mul, Int.cast_natCast] using
    (nrd_eq_mul_iff hx (s.weights.m : ℚ) (D : ℚ) (-(s.weights.m : ℚ)) rfl).mpr
      (by simpa only [disc, Int.cast_mul, Int.cast_neg, Int.cast_natCast] using hs)

/-- Tex 9155–9169: only the local tuple witnesses and the local completed
torus charts are missing. The output supplies the actual Picard fibers for
the fixed discriminant and reference embedding. -/
def picardFibers_of_local (s : StageAt O N M hN m) {D : ℤ}
    (A : AdmissibleD s D) (H : SupportBridge s D)
    (hh : legendreSym s.ell (-(s.weights.m : ℤ)) = -1)
    (Q : QuadraticBasis F (disc s D)) (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ)))
    (T : ∀ p, Nonempty (LocalTorusChart (ActualOrder s) ι (referenceUnit s A Q ι)
      (referenceAffine s Q ι) p))
    (L : ∀ t, HasLocalRealizations s (referenceAffine s Q ι) t) :
    PicardFibers s H (ClassGroup (𝓞 F)) := by
  let x₀ := referenceUnit s A Q ι
  let α := referenceAffine s Q ι
  let E (p : Prime) := (T p).some
  have hα := referenceAffine_spec s A Q ι
  have ⟨hx, hn⟩ := referenceUnit_sphere s A Q ι
  have hb t := realize_tuple s A H hα hx hn t (L t)
  let z := (hb fun _ => false).choose
  exact picardFibers_of_comparison s A H hh x₀ hα hx hn F
    (ideleCentralizerEquiv _ ι x₀ α E z.val z.prop)
    (ideleCentralizerEquiv_rational _ ι x₀ α E z.val z.prop Q s.weights.ha.ne
      s.weights.hb.ne hx rfl)
    (fun w => ideleCentralizerEquiv_integral _ ι x₀ α E z.val z.prop w.val w.prop) hb

/-- Package the equivalences using the existing actual `orbitFibers` constructor. -/
def orbitFibers_of_local (s : StageAt O N M hN m) {D : ℤ}
    (A : AdmissibleD s D) (H : SupportBridge s D)
    (hh : legendreSym s.ell (-(s.weights.m : ℤ)) = -1)
    (Q : QuadraticBasis F (disc s D)) (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ)))
    (T : ∀ p, Nonempty (LocalTorusChart (ActualOrder s) ι (referenceUnit s A Q ι)
      (referenceAffine s Q ι) p))
    (L : ∀ t, HasLocalRealizations s (referenceAffine s Q ι) t) :
    OrbitFibers s.visibility (index s D) N.primeFactors.card (ClassGroup (𝓞 F)) := by
  refine orbitFibers s H F Q A.disc_neg A.mod_eight ?_
  change PicardFibers s H (ClassGroup (𝓞 F))
  exact picardFibers_of_local s A H hh Q ι T L

end ZInQ.Manuscript.RC.PicardFibers
