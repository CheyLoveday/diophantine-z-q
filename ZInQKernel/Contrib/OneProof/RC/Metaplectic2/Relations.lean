import ZInQKernel.Contrib.OneProof.RC.Metaplectic.Generators
import ZInQKernel.Contrib.OneProof.RC.GaussSign.Product

/-! The upper and dilation relations, tex 8733–8738 and 8775–8777.
The proofs on the literal Schwartz–Bruhat model are on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Metaplectic2

open Intertwine Intertwine2 Metaplectic WeilIndex GaussSign Visibility
open scoped BigOperators

variable (a : Fin 3 → ℕ) (p : Place)

theorem upper_mul (b c : ℚ_[p.val]) :
    upperUnipotent a p b * upperUnipotent a p c = upperUnipotent a p (b + c) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change localPhase p (b * quad a x) * (localPhase p (c * quad a x) * f.1 x) =
    localPhase p ((b + c) * quad a x) * f.1 x
  rw [add_mul, localPhase_add, mul_assoc]

theorem upper_zero : upperUnipotent a p 0 = 1 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change localPhase p (0 * quad a x) * f.1 x = f.1 x
  rw [zero_mul, (localPhase_eq_one p 0).2 (zero_mem _), one_mul]

/-- The positive real factor is the cube of the square root of the local norm. -/
def dilationFactor (t : ℚ_[p.val]ˣ) : ℝ := Real.sqrt ‖(t : ℚ_[p.val])‖ ^ 3

/-- Discard only the local norm factor from a dilation. -/
def pullback (t : ℚ_[p.val]ˣ) : Module.End ℂ (SchwartzBruhat p) where
  toFun f := ⟨fun x => f.1 ((t : ℚ_[p.val]) • x),
    f.2.1.comp_continuous (continuous_const_smul _), f.2.2.comp_smul t.ne_zero⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def dilation (t : ℚ_[p.val]ˣ) : Module.End ℂ (SchwartzBruhat p) :=
  (dilationFactor p t : ℂ) • pullback p t

theorem dilation_apply (t : ℚ_[p.val]ˣ) (f : SchwartzBruhat p) (x : LocalVectors p) :
    (dilation p t f).1 x = (dilationFactor p t : ℂ) * f.1 ((t : ℚ_[p.val]) • x) := rfl

theorem dilationFactor_mul (s t : ℚ_[p.val]ˣ) :
    dilationFactor p (s * t) = dilationFactor p s * dilationFactor p t := by
  simp only [dilationFactor, Units.val_mul, norm_mul, Real.sqrt_mul (norm_nonneg _), mul_pow]

theorem dilation_one : dilation p 1 = 1 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  rw [dilation_apply]
  simp [dilationFactor]

theorem dilation_mul (s t : ℚ_[p.val]ˣ) :
    dilation p s * dilation p t = dilation p (s * t) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change (dilation p s (dilation p t f)).1 x = _
  rw [dilation_apply, dilation_apply, dilation_apply, dilationFactor_mul, Complex.ofReal_mul,
    mul_assoc, smul_smul, ← Units.val_mul, mul_comm t s]

theorem dilation_neg_one (f : SchwartzBruhat p) (x : LocalVectors p) :
    (dilation p (-1) f).1 x = f.1 (-x) := by
  rw [dilation_apply]
  simp [dilationFactor]

theorem quad_scale (t : ℚ_[p.val]) (x : LocalVectors p) :
    quad a (t • x) = t ^ 2 * quad a x := by
  simp only [quad, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The nonsingular diagonal coefficients, viewed over the local field. -/
def localCoefficient [∀ i, NeZero (2 * a i)] (i : Fin 3) : ℚ_[p.val]ˣ :=
  atPrime p (Units.mk0 (a i : ℚ) (Nat.cast_ne_zero.mpr
    (fun h => NeZero.ne (2 * a i) (by simp [h]))))

theorem localCoefficient_val [∀ i, NeZero (2 * a i)] (i : Fin 3) :
    (localCoefficient a p i : ℚ_[p.val]) = (a i : ℚ_[p.val]) := by
  simp [localCoefficient, atPrime]

variable [∀ i, NeZero (2 * a i)]

/-- Index of the form scaled by a local unit (an arbitrary nonzero field element). -/
def scaledIndex (t : ℚ_[p.val]ˣ) : ℂˣ :=
  ∏ i, gaussGamma p (t * localCoefficient a p i)

theorem scaledIndex_one : scaledIndex a p 1 = gaussIndex a p := by
  simp only [scaledIndex, gaussIndex, indexAt, rationalDiagonal, gammaDiag, one_mul,
    List.map_ofFn, localCoefficient, atPrime]
  rfl

/-- This is the full ratio in tex 8738, including the common one-dimensional factor. -/
def diagonalRatio (t : ℚ_[p.val]ˣ) : ℂˣ := scaledIndex a p t / gaussIndex a p

def diagonal (t : ℚ_[p.val]ˣ) : Module.End ℂ (SchwartzBruhat p) :=
  (diagonalRatio a p t : ℂ) • dilation p t

omit [∀ i, NeZero (2 * a i)] in
theorem dilation_upper (t : ℚ_[p.val]ˣ) (b : ℚ_[p.val]) :
    dilation p t * upperUnipotent a p b =
      upperUnipotent a p ((t : ℚ_[p.val]) ^ 2 * b) * dilation p t := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change (dilation p t (upperUnipotent a p b f)).1 x =
    localPhase p (((t : ℚ_[p.val]) ^ 2 * b) * quad a x) * (dilation p t f).1 x
  rw [dilation_apply, dilation_apply]
  change (dilationFactor p t : ℂ) *
    (localPhase p (b * quad a ((t : ℚ_[p.val]) • x)) * f.1 ((t : ℚ_[p.val]) • x)) = _
  rw [quad_scale, ← mul_assoc b, mul_comm b, mul_left_comm]

theorem diagonal_upper (t : ℚ_[p.val]ˣ) (b : ℚ_[p.val]) :
    diagonal a p t * upperUnipotent a p b =
      upperUnipotent a p ((t : ℚ_[p.val]) ^ 2 * b) * diagonal a p t := by
  rw [diagonal, smul_mul_assoc, mul_smul_comm, dilation_upper]

theorem diagonal_one : diagonal a p 1 = 1 := by
  simp [diagonal, diagonalRatio, scaledIndex_one, dilation_one]

/-- The normalized diagonal law with its literal index defect. -/
theorem diagonal_mul (s t : ℚ_[p.val]ˣ) :
    diagonal a p s * diagonal a p t =
      ((diagonalRatio a p s * diagonalRatio a p t / diagonalRatio a p (s * t) : ℂˣ) : ℂ) •
        diagonal a p (s * t) := by
  simp only [diagonal, smul_mul_assoc, mul_smul_comm, dilation_mul, smul_smul,
    Units.val_mul, Units.val_div_eq_div_val]
  rw [div_mul_cancel₀ _ (diagonalRatio a p (s * t)).ne_zero, mul_comm]

/-- An inverse parameter has the same index, since it differs by a square. -/
theorem scaledIndex_inv (t : ℚ_[p.val]ˣ) : scaledIndex a p t⁻¹ = scaledIndex a p t := by
  unfold scaledIndex
  apply Finset.prod_congr rfl
  intro i _
  rw [gaussGamma_eq_finiteGamma, show t⁻¹ * localCoefficient a p i =
    (t * localCoefficient a p i) * (t⁻¹)^2 by
      rw [pow_two]
      symm
      calc
        _ = (t * t⁻¹) * (t⁻¹ * localCoefficient a p i) := by ac_rfl
        _ = _ := by simp,
    finiteGamma_mul_sq]


end ZInQ.Manuscript.RC.Metaplectic2
