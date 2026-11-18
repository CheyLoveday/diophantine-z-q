import Research.DerivativeSwitch.ArithmeticBridge

/-!
# Raw-cup transport with the tame factor retained

The division-free calculation is over an arbitrary commutative ring. The
common-strict consumer is separately over a field and retains all of its
nondegeneracy assumptions. These statements do not instantiate arithmetic cup
products, traces, connecting maps, or determinant bases.
-/

namespace Research.DerivativeSwitch.TameFactor

open Matrix
open scoped Matrix

section Ring

variable {R : Type*} [CommRing R]

abbrev Plane (R : Type*) := Fin 2 → R
abbrev LocalPair (R : Type*) := Plane R × Plane R

def area (v x : Plane R) : R := v 0 * x 1 - v 1 * x 0

/-- The coefficient involution occurs once, inside this raw pairing. -/
def rawCup (J : Matrix (Fin 2) (Fin 2) R) (epsilon : R)
    (l r : LocalPair R) : R :=
  epsilon * (area l.1 (J *ᵥ r.2) - area l.2 (J *ᵥ r.1))

def transport (u h : R) (l : LocalPair R) : LocalPair R :=
  (u • l.1, (u * h) • l.2)

lemma area_smul_right (u : R) (v x : Plane R) :
    area v (u • x) = u * area v x := by
  simp only [area, Pi.smul_apply, smul_eq_mul]
  ring

lemma area_swap (v x : Plane R) : area x v = -area v x := by
  simp only [area]
  ring

lemma area_action (J : Matrix (Fin 2) (Fin 2) R) (v x : Plane R) :
    area (J *ᵥ v) (J *ᵥ x) = J.det * area v x := by
  simp only [area, Matrix.det_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

def qF (J : Matrix (Fin 2) (Fin 2) R) (epsilon kappa u h : R)
    (v x : Plane R) : R :=
  kappa * rawCup J epsilon (0, J *ᵥ x) (transport u h (v, 0))

def qS (J : Matrix (Fin 2) (Fin 2) R) (epsilon kappa u h : R)
    (v x : Plane R) : R :=
  kappa * rawCup J epsilon (x, 0) (transport u h (0, J *ᵥ v))

theorem qF_value (J : Matrix (Fin 2) (Fin 2) R) (epsilon kappa u h : R)
    (v x : Plane R) :
    qF J epsilon kappa u h v x = kappa * u * epsilon * J.det * area v x := by
  simp only [qF, rawCup, transport, smul_zero, Matrix.mulVec_zero,
    Matrix.mulVec_smul, area_smul_right]
  rw [area_action, area_swap]
  simp only [area, Pi.zero_apply, mul_zero, sub_self]
  ring

theorem qS_value (J : Matrix (Fin 2) (Fin 2) R) (epsilon kappa u h : R)
    (hinv : J * J = 1) (v x : Plane R) :
    qS J epsilon kappa u h v x = -(kappa * u * epsilon * h * area v x) := by
  simp only [qS, rawCup, transport, smul_zero, Matrix.mulVec_zero,
    Matrix.mulVec_smul, area_smul_right, Matrix.mulVec_mulVec, hinv,
    Matrix.one_mulVec]
  rw [area_swap]
  simp only [area, Pi.zero_apply, zero_mul, sub_self, sub_zero]
  ring

/-- No division or nonzero/unit hypothesis occurs in this ring identity. -/
theorem cross_identity (J : Matrix (Fin 2) (Fin 2) R) (epsilon kappa u h : R)
    (hinv : J * J = 1) (v x : Plane R) :
    h * qF J epsilon kappa u h v x + J.det * qS J epsilon kappa u h v x = 0 := by
  rw [qF_value, qS_value J epsilon kappa u h hinv]
  ring

end Ring

section Coordinates

open ScalarRatio

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- This uses the independently defined cofactor coordinates, including the
common strict factor. It does not define coordinates by the desired formula. -/
theorem coordinate_defect (d : CommonStrictData K I) (h uF uS : K)
    (huF : HasCoordinate (join d.D0 d.AF) (cycle d.hF d.v) d.lamF uF)
    (huS : HasCoordinate (join d.D0 d.AS)
      (cycle d.hS ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.v)) d.lamS uS) :
    uS - h * uF = (d.eta / d.theta) * (h * d.qF + d.delta * d.qS) := by
  obtain ⟨hf, hs⟩ := d.coordinate_values uF uS huF huS
  rw [hf, hs]
  ring

theorem coordinates_of_cross_identity (d : CommonStrictData K I) (h uF uS : K)
    (huF : HasCoordinate (join d.D0 d.AF) (cycle d.hF d.v) d.lamF uF)
    (huS : HasCoordinate (join d.D0 d.AS)
      (cycle d.hS ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.v)) d.lamS uS)
    (hcross : h * d.qF + d.delta * d.qS = 0) :
    uS = h * uF := by
  have he := coordinate_defect d h uF uS huF huS
  rw [hcross, mul_zero] at he
  exact sub_eq_zero.mp he

/-- The unit belongs to the specified integral subring. Common-zero rows and
common nonunit factors are allowed by this division-free conclusion. -/
theorem integral_unit_comparison (d : CommonStrictData K I) (R : Subring K)
    (h : Rˣ) (uF uS : K)
    (huF : HasCoordinate (join d.D0 d.AF) (cycle d.hF d.v) d.lamF uF)
    (huS : HasCoordinate (join d.D0 d.AS)
      (cycle d.hS ((d.J : Matrix (Fin 2) (Fin 2) K) *ᵥ d.v)) d.lamS uS)
    (hcross : unitValue R h * d.qF + d.delta * d.qS = 0) :
    UnitRelated R uF uS := by
  refine ⟨h⁻¹, ?_⟩
  rw [coordinates_of_cross_identity d (unitValue R h) uF uS huF huS hcross,
    ← mul_assoc, unitValue_inv_mul, one_mul]

end Coordinates

end Research.DerivativeSwitch.TameFactor
