import ZInQKernel.Contrib.OneProof.ManuscriptPole.GaloisCoefficients
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Geometric division by two on the manuscript elliptic curve

The curve is the existing `ZInQ.Manuscript.curve ell`, with equation
`y^2 = x (x - ell) (x + 3 ell)`. Geometric points use its actual
base-change point group over the one algebraic closure of the rationals.

The proof solves the monic quartic obtained from the explicit doubling
formula. Its three possible poles have nonzero values when `ell` is
nonzero. A square root supplies an actual nonsingular affine point;
the doubling formula and negation give the required geometric half.
The point at infinity and affine targets of order two are included.

Only geometric division by two is treated. No rational half, higher
coefficient basis, Kummer map, local Selmer group or rank assertion is
supplied. Point-group and formula conventions follow the imported
Weierstrass-curve sources.
-/

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace ZInQ.Contrib.OneProof.ManuscriptPole.GeometricTwoDivision

open Polynomial
open ZInQ.Contrib.OneProof.ManuscriptPole.GaloisCoefficients

private def quartic (ell : ℚ) (p : Qbar) : Polynomial Qbar :=
  (X ^ 2 + C (3 * (algebraMap ℚ Qbar ell) ^ 2)) ^ 2 -
    C (4 * p) * X * (X - C (algebraMap ℚ Qbar ell)) *
      (X + C (3 * algebraMap ℚ Qbar ell))

private theorem parameter_ne_zero (ell : ℚ) (hell : ell ≠ 0) :
    algebraMap ℚ Qbar ell ≠ 0 := by
  intro h
  apply hell
  apply (algebraMap ℚ Qbar).injective
  exact h.trans (map_zero (algebraMap ℚ Qbar)).symm

private theorem quartic_expansion (ell : ℚ) (p : Qbar) :
    quartic ell p =
      X ^ 4 + C (-4 * p) * X ^ 3 +
      C (6 * (algebraMap ℚ Qbar ell) ^ 2 -
        8 * p * algebraMap ℚ Qbar ell) * X ^ 2 +
      C (12 * p * (algebraMap ℚ Qbar ell) ^ 2) * X +
      C (9 * (algebraMap ℚ Qbar ell) ^ 4) := by
  simp only [quartic, map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]
  ring

private theorem quartic_monic (ell : ℚ) (p : Qbar) :
    (quartic ell p).Monic := by
  change (quartic ell p).leadingCoeff = 1
  rw [quartic_expansion]
  have htail :
      (C (-4 * p) * X ^ 3 +
        C (6 * (algebraMap ℚ Qbar ell) ^ 2 -
          8 * p * algebraMap ℚ Qbar ell) * X ^ 2 +
        C (12 * p * (algebraMap ℚ Qbar ell) ^ 2) * X +
        C (9 * (algebraMap ℚ Qbar ell) ^ 4)).degree <
        ((X : Polynomial Qbar) ^ 4).degree := by
    simpa only [degree_X_pow] using!
      (degree_cubic_lt (a := -4 * p)
        (b := 6 * (algebraMap ℚ Qbar ell) ^ 2 -
          8 * p * algebraMap ℚ Qbar ell)
        (c := 12 * p * (algebraMap ℚ Qbar ell) ^ 2)
        (d := 9 * (algebraMap ℚ Qbar ell) ^ 4))
  simpa only [add_assoc, leadingCoeff_X_pow] using
    (leadingCoeff_add_of_degree_lt' htail)

private theorem quartic_natDegree (ell : ℚ) (p : Qbar) :
    (quartic ell p).natDegree = 4 := by
  rw [quartic_expansion]
  have htail :
      (C (-4 * p) * X ^ 3 +
        C (6 * (algebraMap ℚ Qbar ell) ^ 2 -
          8 * p * algebraMap ℚ Qbar ell) * X ^ 2 +
        C (12 * p * (algebraMap ℚ Qbar ell) ^ 2) * X +
        C (9 * (algebraMap ℚ Qbar ell) ^ 4)).degree <
        ((X : Polynomial Qbar) ^ 4).degree := by
    simpa only [degree_X_pow] using!
      (degree_cubic_lt (a := -4 * p)
        (b := 6 * (algebraMap ℚ Qbar ell) ^ 2 -
          8 * p * algebraMap ℚ Qbar ell)
        (c := 12 * p * (algebraMap ℚ Qbar ell) ^ 2)
        (d := 9 * (algebraMap ℚ Qbar ell) ^ 4))
  simpa only [add_assoc, natDegree_X_pow] using
    (natDegree_add_eq_left_of_degree_lt htail)

private theorem quartic_eval (ell : ℚ) (p u : Qbar) :
    (quartic ell p).eval u =
      (u ^ 2 + 3 * (algebraMap ℚ Qbar ell) ^ 2) ^ 2 -
        4 * p * u * (u - algebraMap ℚ Qbar ell) *
          (u + 3 * algebraMap ℚ Qbar ell) := by
  simp only [quartic, eval_sub, eval_pow, eval_add, eval_C, eval_mul, eval_X]

private theorem quartic_poles (ell : ℚ) (p : Qbar) :
    (quartic ell p).eval 0 = 9 * (algebraMap ℚ Qbar ell) ^ 4 ∧
    (quartic ell p).eval (algebraMap ℚ Qbar ell) =
      16 * (algebraMap ℚ Qbar ell) ^ 4 ∧
    (quartic ell p).eval (-3 * algebraMap ℚ Qbar ell) =
      144 * (algebraMap ℚ Qbar ell) ^ 4 := by
  constructor
  · rw [quartic_eval]
    ring
  · constructor <;> rw [quartic_eval] <;> ring

/-- The doubling quartic has a geometric root away from every possible pole. -/
theorem exists_quartic_root_avoiding_poles (ell : ℚ) (hell : ell ≠ 0)
    (p : Qbar) :
    ∃ u : Qbar,
      (u ^ 2 + 3 * (algebraMap ℚ Qbar ell) ^ 2) ^ 2 =
        4 * p * u * (u - algebraMap ℚ Qbar ell) *
          (u + 3 * algebraMap ℚ Qbar ell) ∧
      u ≠ 0 ∧ u ≠ algebraMap ℚ Qbar ell ∧
        u ≠ -3 * algebraMap ℚ Qbar ell := by
  have he : algebraMap ℚ Qbar ell ≠ 0 := parameter_ne_zero ell hell
  have hpos : 0 < (quartic ell p).natDegree := by
    rw [quartic_natDegree]
    norm_num
  have hdegree : (quartic ell p).degree ≠ 0 :=
    (natDegree_pos_iff_degree_pos.mp hpos).ne'
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root (quartic ell p) hdegree
  have hroot : (quartic ell p).eval u = 0 := hu
  have hpoles := quartic_poles ell p
  have hu0 : u ≠ 0 := by
    intro h
    have hz := hroot
    rw [h, hpoles.1] at hz
    exact (mul_ne_zero (by norm_num : (9 : Qbar) ≠ 0) (pow_ne_zero 4 he)) hz
  have hue : u ≠ algebraMap ℚ Qbar ell := by
    intro h
    have hz := hroot
    rw [h, hpoles.2.1] at hz
    exact (mul_ne_zero (by norm_num : (16 : Qbar) ≠ 0) (pow_ne_zero 4 he)) hz
  have huneg : u ≠ -3 * algebraMap ℚ Qbar ell := by
    intro h
    have hz := hroot
    rw [h, hpoles.2.2] at hz
    exact (mul_ne_zero (by norm_num : (144 : Qbar) ≠ 0) (pow_ne_zero 4 he)) hz
  refine ⟨u, ?_, hu0, hue, huneg⟩
  apply sub_eq_zero.mp
  simpa only [quartic_eval] using hroot

private theorem geometric_isElliptic (ell : ℚ) (hell : ell ≠ 0) :
    ((ZInQ.Manuscript.curve ell).baseChange Qbar).IsElliptic := by
  letI : (ZInQ.Manuscript.curve ell).IsElliptic := manuscriptCurve_isElliptic hell
  change ((ZInQ.Manuscript.curve ell).map (algebraMap ℚ Qbar)).IsElliptic
  infer_instance

private theorem geometric_equation_iff (ell : ℚ) (x y : Qbar) :
    ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.Equation x y ↔
      y ^ 2 = x * (x - algebraMap ℚ Qbar ell) *
        (x + 3 * algebraMap ℚ Qbar ell) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.toAffine, WeierstrassCurve.baseChange,
    WeierstrassCurve.map, ZInQ.Manuscript.curve, map_zero, map_mul,
    map_neg, map_pow, map_ofNat, zero_mul, zero_add, add_zero]
  rw [show x ^ 3 + (2 * algebraMap ℚ Qbar ell) * x ^ 2 +
      (-3 * (algebraMap ℚ Qbar ell) ^ 2) * x =
      x * (x - algebraMap ℚ Qbar ell) *
        (x + 3 * algebraMap ℚ Qbar ell) by ring]

private theorem geometric_duplication_data (ell : ℚ) :
    ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.a₁ = 0 ∧
    ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.a₃ = 0 ∧
    ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.b₂ =
      8 * algebraMap ℚ Qbar ell ∧
    ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.b₄ =
      -6 * (algebraMap ℚ Qbar ell) ^ 2 ∧
    ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.b₆ = 0 ∧
    ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.b₈ =
      -9 * (algebraMap ℚ Qbar ell) ^ 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [WeierstrassCurve.toAffine, WeierstrassCurve.baseChange,
      WeierstrassCurve.map, ZInQ.Manuscript.curve, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
      map_zero, map_mul, map_neg, map_pow, map_ofNat] <;> ring

private theorem exists_geometric_double_eq_affine
    (ell : ℚ) (hell : ell ≠ 0) (p y : Qbar)
    (hP : ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.Nonsingular p y) :
    ∃ Q : GeometricPoints ell,
      (2 : ℕ) • Q = WeierstrassCurve.Affine.Point.some p y hP := by
  let e : Qbar := algebraMap ℚ Qbar ell
  letI : ((ZInQ.Manuscript.curve ell).baseChange Qbar).IsElliptic :=
    geometric_isElliptic ell hell
  obtain ⟨u, hrel, hu0, hue, huneg⟩ :=
    exists_quartic_root_avoiding_poles ell hell p
  change (u ^ 2 + 3 * e ^ 2) ^ 2 =
    4 * p * u * (u - e) * (u + 3 * e) at hrel
  change u ≠ e at hue
  change u ≠ -3 * e at huneg
  have hplus : u + 3 * e ≠ 0 := by
    intro h
    apply huneg
    calc
      u = (u + 3 * e) - 3 * e := by ring
      _ = -3 * e := by rw [h]; ring
  have hcubic : u * (u - e) * (u + 3 * e) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hu0 (sub_ne_zero.mpr hue)) hplus
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq
    (u * (u - e) * (u + 3 * e)) (n := 2) (by norm_num)
  have hvne : v ≠ 0 := by
    intro h
    have hz := hv
    rw [h, zero_pow two_ne_zero] at hz
    exact hcubic hz.symm
  have heq :
      ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.Equation u v :=
    (geometric_equation_iff ell u v).mpr hv
  have hns :
      ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.Nonsingular u v :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular).mp heq
  obtain ⟨ha1, ha3, hb2, hb4, hb6, hb8⟩ := geometric_duplication_data ell
  have hnonvertical :
      v ≠ ((ZInQ.Manuscript.curve ell).baseChange Qbar).toAffine.negY u v := by
    intro h
    have hs : v = -v := by
      simpa only [WeierstrassCurve.Affine.negY, ha1, ha3,
        zero_mul, sub_zero] using h
    have htwo : (2 : Qbar) * v = 0 := by
      linear_combination hs
    exact hvne ((mul_eq_zero.mp htwo).resolve_left (by norm_num : (2 : Qbar) ≠ 0))
  have hden : (4 : Qbar) * u * (u - e) * (u + 3 * e) ≠ 0 := by
    rw [show (4 : Qbar) * u * (u - e) * (u + 3 * e) =
      4 * (u * (u - e) * (u + 3 * e)) by ring]
    exact mul_ne_zero (by norm_num : (4 : Qbar) ≠ 0) hcubic
  have hratio :
      (u ^ 2 + 3 * e ^ 2) ^ 2 /
        (4 * u * (u - e) * (u + 3 * e)) = p := by
    apply (div_eq_iff hden).mpr
    calc
      (u ^ 2 + 3 * e ^ 2) ^ 2 =
          4 * p * u * (u - e) * (u + 3 * e) := hrel
      _ = p * (4 * u * (u - e) * (u + 3 * e)) := by ring
  let Q : GeometricPoints ell := WeierstrassCurve.Affine.Point.some u v hns
  have hx :
      (WeierstrassCurve.Affine.Point.some u v hns +
        WeierstrassCurve.Affine.Point.some u v hns).xRep =
      (WeierstrassCurve.Affine.Point.some p y hP).xRep := by
    rw [WeierstrassCurve.Affine.Point.xRep_add_self_of_Y_ne hns hnonvertical,
      WeierstrassCurve.Affine.Point.xRep_some, hb2, hb4, hb6, hb8]
    have hnum :
        u ^ 4 - (-6 * e ^ 2) * u ^ 2 - 2 * (0 : Qbar) * u - (-9 * e ^ 4) =
          (u ^ 2 + 3 * e ^ 2) ^ 2 := by ring
    have hdem :
        4 * u ^ 3 + (8 * e) * u ^ 2 + 2 * (-6 * e ^ 2) * u + 0 =
          4 * u * (u - e) * (u + 3 * e) := by ring
    change ![(u ^ 4 - (-6 * e ^ 2) * u ^ 2 -
        2 * (0 : Qbar) * u - (-9 * e ^ 4)) /
      (4 * u ^ 3 + (8 * e) * u ^ 2 + 2 * (-6 * e ^ 2) * u + 0), 1] = ![p, 1]
    rw [hnum, hdem]
    exact congrArg (fun z : Qbar => ![z, (1 : Qbar)]) hratio
  let P : GeometricPoints ell := WeierstrassCurve.Affine.Point.some p y hP
  have hadd : Q + Q = P ∨ Q + Q = -P :=
    WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hx
  have hbranches : (2 : ℕ) • Q = P ∨ (2 : ℕ) • Q = -P := by
    simpa only [two_nsmul] using hadd
  rcases hbranches with hpositive | hnegative
  · exact ⟨Q, hpositive⟩
  · refine ⟨-Q, ?_⟩
    change (2 : ℕ) • (-Q) = P
    calc
      (2 : ℕ) • (-Q) = -((2 : ℕ) • Q) :=
        map_neg (nsmulAddMonoidHom (α := GeometricPoints ell) 2) Q
      _ = -(-P) := congrArg (fun R : GeometricPoints ell => -R) hnegative
      _ = P := neg_neg P

/-- Every actual geometric point of the manuscript curve has a geometric half. -/
theorem geometricTwoSurjective (ell : ℚ) (hell : ell ≠ 0) :
    Function.Surjective
      (fun Q : GeometricPoints ell => (2 : ℕ) • Q) := by
  intro P
  cases P with
  | zero =>
      exact ⟨0, nsmul_zero 2⟩
  | some p y hP =>
      exact exists_geometric_double_eq_affine ell hell p y hP

end ZInQ.Contrib.OneProof.ManuscriptPole.GeometricTwoDivision
