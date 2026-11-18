import ZInQKernel.Contrib.OneProof.ManuscriptPole.GaloisCoefficients
import ZInQKernel.Contrib.OneProof.ManuscriptPole.GeometricTwoDivision

/-!
# Public geometric division consumers

The public division statements are checked with their complete telescopes
on the existing curve and its one rational algebraic closure. The literal
consumers retain the actual point group and the nonzero parameter guard.
Infinity and the three affine points of order two are included as targets.
-/

set_option autoImplicit false

open scoped Classical
open ZInQ.Contrib.OneProof.ManuscriptPole.GaloisCoefficients
open ZInQ.Contrib.OneProof.ManuscriptPole.GeometricTwoDivision

noncomputable section

set_option pp.fullNames true
set_option pp.universes true

/- The complete public quartic-root statement. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.GeometricTwoDivision.exists_quartic_root_avoiding_poles
example : ∀ (ell : ℚ) (hell : ell ≠ 0) (p : Qbar),
    ∃ u : Qbar,
      (u ^ 2 + 3 * (algebraMap ℚ Qbar ell) ^ 2) ^ 2 =
        4 * p * u * (u - algebraMap ℚ Qbar ell) *
          (u + 3 * algebraMap ℚ Qbar ell) ∧
      u ≠ 0 ∧ u ≠ algebraMap ℚ Qbar ell ∧
        u ≠ -3 * algebraMap ℚ Qbar ell :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.GeometricTwoDivision.exists_quartic_root_avoiding_poles
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.GeometricTwoDivision.exists_quartic_root_avoiding_poles

/- The complete public geometric doubling statement. -/
#check @ZInQ.Contrib.OneProof.ManuscriptPole.GeometricTwoDivision.geometricTwoSurjective
example : ∀ (ell : ℚ) (hell : ell ≠ 0),
    Function.Surjective (fun Q : GeometricPoints ell => (2 : ℕ) • Q) :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.GeometricTwoDivision.geometricTwoSurjective
#print axioms ZInQ.Contrib.OneProof.ManuscriptPole.GeometricTwoDivision.geometricTwoSurjective

/- The doubling statement on the literal base-change Point carrier. -/
example : ∀ (ell : ℚ) (hell : ell ≠ 0),
    Function.Surjective
      (fun Q : ((ZInQ.Manuscript.curve ell).baseChange (AlgebraicClosure ℚ)).toAffine.Point =>
        (2 : ℕ) • Q) :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.GeometricTwoDivision.geometricTwoSurjective

/- The existing closure and point carrier are used literally. -/
example : Qbar = AlgebraicClosure ℚ := rfl
example (ell : ℚ) : GeometricPoints ell =
    ((ZInQ.Manuscript.curve ell).baseChange (AlgebraicClosure ℚ)).toAffine.Point := rfl

example : Algebra ℚ Qbar := inferInstance
example : CharZero Qbar := inferInstance
example : DecidableEq Qbar := inferInstance

/- The additive dictionary is the actual imported Point dictionary. -/
example : ∀ (ell : ℚ),
    AddCommGroup (((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.Point) :=
  @ZInQ.Contrib.OneProof.ManuscriptPole.GaloisCoefficients.geometricPointsAddCommGroup

example (ell : ℚ) :
    ZInQ.Contrib.OneProof.ManuscriptPole.GaloisCoefficients.geometricPointsAddCommGroup ell =
      inferInstanceAs
        (AddCommGroup (((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.Point)) := rfl

example (ell : ℚ) (P : GeometricPoints ell) : (2 : ℕ) • P = P + P :=
  two_nsmul P

example (ell : ℚ) (hell : ell ≠ 0) (P : GeometricPoints ell) :
    (geometricMultiplicationHom ell hell 2).hom P = (2 : ℕ) • P := rfl

/- The target abscissa may be any of the three doubling poles. -/
example (ell : ℚ) (hell : ell ≠ 0) :
    ∃ u : Qbar,
      (u ^ 2 + 3 * (algebraMap ℚ Qbar ell) ^ 2) ^ 2 =
        4 * (0 : Qbar) * u * (u - algebraMap ℚ Qbar ell) *
          (u + 3 * algebraMap ℚ Qbar ell) ∧
      u ≠ 0 ∧ u ≠ algebraMap ℚ Qbar ell ∧
        u ≠ -3 * algebraMap ℚ Qbar ell :=
  exists_quartic_root_avoiding_poles ell hell 0

example (ell : ℚ) (hell : ell ≠ 0) :
    ∃ u : Qbar,
      (u ^ 2 + 3 * (algebraMap ℚ Qbar ell) ^ 2) ^ 2 =
        4 * (algebraMap ℚ Qbar ell) * u * (u - algebraMap ℚ Qbar ell) *
          (u + 3 * algebraMap ℚ Qbar ell) ∧
      u ≠ 0 ∧ u ≠ algebraMap ℚ Qbar ell ∧
        u ≠ -3 * algebraMap ℚ Qbar ell :=
  exists_quartic_root_avoiding_poles ell hell (algebraMap ℚ Qbar ell)

example (ell : ℚ) (hell : ell ≠ 0) :
    ∃ u : Qbar,
      (u ^ 2 + 3 * (algebraMap ℚ Qbar ell) ^ 2) ^ 2 =
        4 * (-3 * algebraMap ℚ Qbar ell) * u * (u - algebraMap ℚ Qbar ell) *
          (u + 3 * algebraMap ℚ Qbar ell) ∧
      u ≠ 0 ∧ u ≠ algebraMap ℚ Qbar ell ∧
        u ≠ -3 * algebraMap ℚ Qbar ell :=
  exists_quartic_root_avoiding_poles ell hell (-3 * algebraMap ℚ Qbar ell)

/- Infinity is retained as a target. -/
example (ell : ℚ) (hell : ell ≠ 0) :
    ∃ Q : GeometricPoints ell, (2 : ℕ) • Q = (0 : GeometricPoints ell) :=
  geometricTwoSurjective ell hell 0

/- Arbitrary affine targets have only their genuine nonsingularity condition. -/
example (ell : ℚ) (hell : ell ≠ 0) (p y : Qbar)
    (hP : ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.Nonsingular p y) :
    ∃ Q : GeometricPoints ell,
      (2 : ℕ) • Q = WeierstrassCurve.Affine.Point.some p y hP :=
  geometricTwoSurjective ell hell (WeierstrassCurve.Affine.Point.some p y hP)

/- Nonsingularity and order two are derived for the target with abscissa zero. -/
example (ell : ℚ) (hell : ell ≠ 0) :
    ∃ hP : ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.Nonsingular 0 0,
      (WeierstrassCurve.Affine.Point.some 0 0 hP : GeometricPoints ell) ≠ 0 ∧
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some 0 0 hP : GeometricPoints ell) = 0 ∧
      ∃ Q : GeometricPoints ell,
        (2 : ℕ) • Q = WeierstrassCurve.Affine.Point.some 0 0 hP := by
  letI : (ZInQ.Manuscript.curve ell).IsElliptic := manuscriptCurve_isElliptic hell
  letI : ((ZInQ.Manuscript.curve ell).baseChange Qbar).IsElliptic := by
    change ((ZInQ.Manuscript.curve ell).map (algebraMap ℚ Qbar)).IsElliptic
    infer_instance
  have hP : ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.Nonsingular 0 0 := by
    apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [WeierstrassCurve.toAffine, WeierstrassCurve.baseChange,
      WeierstrassCurve.map, ZInQ.Manuscript.curve, map_zero, map_mul,
      map_neg, map_pow, map_ofNat]
    ring
  refine ⟨hP, WeierstrassCurve.Affine.Point.some_ne_zero hP, ?_,
    geometricTwoSurjective ell hell (WeierstrassCurve.Affine.Point.some 0 0 hP)⟩
  rw [two_nsmul]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.toAffine,
    WeierstrassCurve.baseChange, WeierstrassCurve.map, ZInQ.Manuscript.curve, map_zero]
  ring

/- Nonsingularity and order two are derived for the target with abscissa ell. -/
example (ell : ℚ) (hell : ell ≠ 0) :
    ∃ hP : ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.Nonsingular
        (algebraMap ℚ Qbar ell) 0,
      (WeierstrassCurve.Affine.Point.some (algebraMap ℚ Qbar ell) 0 hP :
        GeometricPoints ell) ≠ 0 ∧
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some (algebraMap ℚ Qbar ell) 0 hP :
        GeometricPoints ell) = 0 ∧
      ∃ Q : GeometricPoints ell,
        (2 : ℕ) • Q = WeierstrassCurve.Affine.Point.some (algebraMap ℚ Qbar ell) 0 hP := by
  letI : (ZInQ.Manuscript.curve ell).IsElliptic := manuscriptCurve_isElliptic hell
  letI : ((ZInQ.Manuscript.curve ell).baseChange Qbar).IsElliptic := by
    change ((ZInQ.Manuscript.curve ell).map (algebraMap ℚ Qbar)).IsElliptic
    infer_instance
  have hP : ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.Nonsingular
      (algebraMap ℚ Qbar ell) 0 := by
    apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [WeierstrassCurve.toAffine, WeierstrassCurve.baseChange,
      WeierstrassCurve.map, ZInQ.Manuscript.curve, map_zero, map_mul,
      map_neg, map_pow, map_ofNat]
    ring
  refine ⟨hP, WeierstrassCurve.Affine.Point.some_ne_zero hP, ?_,
    geometricTwoSurjective ell hell
      (WeierstrassCurve.Affine.Point.some (algebraMap ℚ Qbar ell) 0 hP)⟩
  rw [two_nsmul]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.toAffine,
    WeierstrassCurve.baseChange, WeierstrassCurve.map, ZInQ.Manuscript.curve, map_zero]
  ring

/- Nonsingularity and order two are derived for the target with abscissa minus three ell. -/
example (ell : ℚ) (hell : ell ≠ 0) :
    ∃ hP : ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.Nonsingular
        (-3 * algebraMap ℚ Qbar ell) 0,
      (WeierstrassCurve.Affine.Point.some (-3 * algebraMap ℚ Qbar ell) 0 hP :
        GeometricPoints ell) ≠ 0 ∧
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some (-3 * algebraMap ℚ Qbar ell) 0 hP :
        GeometricPoints ell) = 0 ∧
      ∃ Q : GeometricPoints ell,
        (2 : ℕ) • Q = WeierstrassCurve.Affine.Point.some (-3 * algebraMap ℚ Qbar ell) 0 hP := by
  letI : (ZInQ.Manuscript.curve ell).IsElliptic := manuscriptCurve_isElliptic hell
  letI : ((ZInQ.Manuscript.curve ell).baseChange Qbar).IsElliptic := by
    change ((ZInQ.Manuscript.curve ell).map (algebraMap ℚ Qbar)).IsElliptic
    infer_instance
  have hP : ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.Nonsingular
      (-3 * algebraMap ℚ Qbar ell) 0 := by
    apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [WeierstrassCurve.toAffine, WeierstrassCurve.baseChange,
      WeierstrassCurve.map, ZInQ.Manuscript.curve, map_zero, map_mul,
      map_neg, map_pow, map_ofNat]
    ring
  refine ⟨hP, WeierstrassCurve.Affine.Point.some_ne_zero hP, ?_,
    geometricTwoSurjective ell hell
      (WeierstrassCurve.Affine.Point.some (-3 * algebraMap ℚ Qbar ell) 0 hP)⟩
  rw [two_nsmul]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.toAffine,
    WeierstrassCurve.baseChange, WeierstrassCurve.map, ZInQ.Manuscript.curve, map_zero]
  ring
