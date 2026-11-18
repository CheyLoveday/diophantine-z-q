import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Basic
import ZInQKernel.Contrib.CloudB3RC53.Basic

/-!
# Lane RC18-twist: models of quadratic twists

The twist dictionary `a_n(E^{(D)}) = χ_D(n) a_n(E)` (lane RC8's GLUE `TwistDictionary`) is a
statement about Mathlib's `WeierstrassCurve.LFunction`, which is computed place by place from a
minimal model over the completion. This file supplies the two models of a quadratic twist used
for that computation.

* `twistK W d` over a field: `y² = x³ + d b₂/4 x² + d² b₄/2 x + d³ b₆/4`, the model of the shared
  blueprint's `qtwist` (`qtwist_eq_twistK`, `rfl`); it commutes with base change
  (`twistK_map`), it is compatible with changes of variables (`twistK_smul`:
  `(C • W)^{(d)} = (u, d r, 0, 0) • W^{(d)}`), `twistK (twistK W d) e = twistK W (d e)`,
  `twistK W 1` is the completed-square model of `W` (`twistK_one`) and
  `twistK W (d e²) = (e⁻¹, 0, 0, 0) • twistK W d` (`twistK_mul_sq`).
* `twistInt W D c` over any commutative ring, for `D = 1 + 4c`:
  `[a₁, D a₂ + c a₁², D a₃, D² a₄ + 2cD a₁a₃, D³ a₆ + cD² a₃²]`. It has no denominators, its
  `b`-invariants are `(D b₂, D² b₄, D³ b₆, D⁴ b₈)` (`twistInt_b₂`, …), so
  `c₄ ↦ D² c₄`, `c₆ ↦ D³ c₆`, `Δ ↦ D⁶ Δ`; it commutes with ring homomorphisms (`twistInt_map`),
  and over a field with `2 ≠ 0` it is a change of variables of `twistK W D`
  (`twistInt_eq_smul_twistK`). Over `ℤ_p` it is an integral model of the twist by a `p`-adic
  unit `D` (for `p = 2` this needs `D ≡ 1 (mod 4)`), whose reduction is `twistInt` of the
  reduction.

All results here are `PROVED`.
-/

namespace ZInQ.Manuscript.RC.TwistDictionary

open WeierstrassCurve

section Ring

variable {R : Type*} [CommRing R]

/-- **The integral model of the quadratic twist by `D = 1 + 4c`**:
`[a₁, D a₂ + c a₁², D a₃, D² a₄ + 2cD a₁a₃, D³ a₆ + cD² a₃²]`. -/
def twistInt (W : WeierstrassCurve R) (D c : R) : WeierstrassCurve R :=
  ⟨W.a₁, D * W.a₂ + c * W.a₁ ^ 2, D * W.a₃, D ^ 2 * W.a₄ + 2 * c * D * W.a₁ * W.a₃,
    D ^ 3 * W.a₆ + c * D ^ 2 * W.a₃ ^ 2⟩

variable (W : WeierstrassCurve R) {D c : R}

/-- `b₂` of the integral twist is `D b₂` (PROVED). -/
theorem twistInt_b₂ (h : D = 1 + 4 * c) : (twistInt W D c).b₂ = D * W.b₂ := by
  subst h; simp only [twistInt, b₂]; ring

/-- `b₄` of the integral twist is `D² b₄` (PROVED). -/
theorem twistInt_b₄ (h : D = 1 + 4 * c) : (twistInt W D c).b₄ = D ^ 2 * W.b₄ := by
  subst h; simp only [twistInt, b₄]; ring

/-- `b₆` of the integral twist is `D³ b₆` (PROVED). -/
theorem twistInt_b₆ (h : D = 1 + 4 * c) : (twistInt W D c).b₆ = D ^ 3 * W.b₆ := by
  subst h; simp only [twistInt, b₆]; ring

/-- `b₈` of the integral twist is `D⁴ b₈` (PROVED). -/
theorem twistInt_b₈ (h : D = 1 + 4 * c) : (twistInt W D c).b₈ = D ^ 4 * W.b₈ := by
  subst h; simp only [twistInt, b₈]; ring

/-- `c₄` of the integral twist is `D² c₄` (PROVED). -/
theorem twistInt_c₄ (h : D = 1 + 4 * c) : (twistInt W D c).c₄ = D ^ 2 * W.c₄ := by
  simp only [c₄, twistInt_b₂ W h, twistInt_b₄ W h]; ring

/-- `c₆` of the integral twist is `D³ c₆` (PROVED). -/
theorem twistInt_c₆ (h : D = 1 + 4 * c) : (twistInt W D c).c₆ = D ^ 3 * W.c₆ := by
  simp only [c₆, twistInt_b₂ W h, twistInt_b₄ W h, twistInt_b₆ W h]; ring

/-- The discriminant of the integral twist is `D⁶ Δ` (PROVED). -/
theorem twistInt_Δ (h : D = 1 + 4 * c) : (twistInt W D c).Δ = D ^ 6 * W.Δ := by
  simp only [Δ, twistInt_b₂ W h, twistInt_b₄ W h, twistInt_b₆ W h, twistInt_b₈ W h]; ring

/-- `a₁` of the integral twist (PROVED, `rfl`). -/
theorem twistInt_a₁ : (twistInt W D c).a₁ = W.a₁ := rfl

/-- `a₂` of the integral twist (PROVED, `rfl`). -/
theorem twistInt_a₂ : (twistInt W D c).a₂ = D * W.a₂ + c * W.a₁ ^ 2 := rfl

/-- `twistInt` commutes with ring homomorphisms. -/
theorem twistInt_map {S : Type*} [CommRing S] (φ : R →+* S) (D c : R) :
    (twistInt W D c).map φ = twistInt (W.map φ) (φ D) (φ c) := by
  ext <;> simp [twistInt, map_ofNat]

open Polynomial in
/-- **The splitting polynomial** `c₄ T² + a₁c₄ T − (54 b₆ − 3 b₂ b₄ + a₂ c₄)`: Mathlib's
`HasSplitMultiplicativeReduction` asks that its image over the residue field splits (the slopes of
the two tangent lines at the node are its roots). -/
noncomputable def splitPoly (V : WeierstrassCurve R) : R[X] :=
  C V.c₄ * X ^ 2 + C (V.a₁ * V.c₄) * X - C (54 * V.b₆ - 3 * V.b₂ * V.b₄ + V.a₂ * V.c₄)

/-- `splitPoly` commutes with ring homomorphisms. -/
theorem splitPoly_map {S : Type*} [CommRing S] (φ : R →+* S) :
    (splitPoly W).map φ = splitPoly (W.map φ) := by
  simp [splitPoly, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, map_ofNat]

/-- The twist of an elliptic curve by a unit is elliptic. -/
theorem twistInt_isElliptic [W.IsElliptic] (h : D = 1 + 4 * c) (hD : IsUnit D) :
    (twistInt W D c).IsElliptic :=
  ⟨by rw [twistInt_Δ W h]; exact (hD.pow 6).mul W.isUnit_Δ⟩

end Ring

section Field

variable {K : Type*} [Field K]

/-- **The quadratic twist over a field**: `y² = x³ + d b₂/4 x² + d² b₄/2 x + d³ b₆/4`, the model
of the shared blueprint's `qtwist`. -/
def twistK (W : WeierstrassCurve K) (d : K) : WeierstrassCurve K :=
  ⟨0, d * W.b₂ / 4, 0, d ^ 2 * W.b₄ / 2, d ^ 3 * W.b₆ / 4⟩

/-- The blueprint's `qtwist` is `twistK` over `ℚ`. -/
theorem qtwist_eq_twistK (E : WeierstrassCurve ℚ) (d : ℚ) :
    ZInQ.Contrib.CloudB3RC53.qtwist E d = twistK E d := rfl

variable (W : WeierstrassCurve K)

/-- `twistK` commutes with field homomorphisms. -/
theorem twistK_map {L : Type*} [Field L] (φ : K →+* L) (d : K) :
    (twistK W d).map φ = twistK (W.map φ) (φ d) := by
  ext <;> simp [twistK, map_ofNat]

/-- `twistK` depends only on `(b₂, b₄, b₆)`. -/
theorem twistK_congr {W' : WeierstrassCurve K} (h₂ : W'.b₂ = W.b₂) (h₄ : W'.b₄ = W.b₄)
    (h₆ : W'.b₆ = W.b₆) (d : K) : twistK W' d = twistK W d := by
  simp only [twistK, h₂, h₄, h₆]

variable (h2 : (2 : K) ≠ 0)
include h2

omit W in
/-- `4 ≠ 0` when `2 ≠ 0` (PROVED). -/
theorem four_ne_zero_of_two : (4 : K) ≠ 0 := by
  have : (4 : K) = 2 * 2 := by norm_num
  rw [this]; exact mul_ne_zero h2 h2

/-- `b₂` of `twistK W d` is `d b₂` (PROVED). -/
theorem twistK_b₂ (d : K) : (twistK W d).b₂ = d * W.b₂ := by
  have h4 := four_ne_zero_of_two h2
  simp only [twistK, b₂]; field_simp; ring

/-- `b₄` of `twistK W d` is `d² b₄` (PROVED). -/
theorem twistK_b₄ (d : K) : (twistK W d).b₄ = d ^ 2 * W.b₄ := by
  have h4 := four_ne_zero_of_two h2
  simp only [twistK, b₄]; field_simp; ring

/-- `b₆` of `twistK W d` is `d³ b₆` (PROVED). -/
theorem twistK_b₆ (d : K) : (twistK W d).b₆ = d ^ 3 * W.b₆ := by
  have h4 := four_ne_zero_of_two h2
  simp only [twistK, b₆]; field_simp; ring

/-- `c₄` of `twistK W d` is `d² c₄` (PROVED). -/
theorem twistK_c₄ (d : K) : (twistK W d).c₄ = d ^ 2 * W.c₄ := by
  simp only [c₄, twistK_b₂ W h2, twistK_b₄ W h2]; ring

/-- `c₆` of `twistK W d` is `d³ c₆` (PROVED). -/
theorem twistK_c₆ (d : K) : (twistK W d).c₆ = d ^ 3 * W.c₆ := by
  simp only [c₆, twistK_b₂ W h2, twistK_b₄ W h2, twistK_b₆ W h2]; ring

/-- The discriminant of `twistK W d` is `d⁶ Δ` (PROVED). -/
theorem twistK_Δ (d : K) : (twistK W d).Δ = d ^ 6 * W.Δ := by
  have h4 := four_ne_zero_of_two h2
  simp only [Δ, b₈, twistK, b₂, b₄, b₆]; field_simp; ring

/-- Twisting twice: `(W^{(d)})^{(e)} = W^{(de)}`. -/
theorem twistK_twistK (d e : K) : twistK (twistK W d) e = twistK W (d * e) := by
  show (⟨0, e * (twistK W d).b₂ / 4, 0, e ^ 2 * (twistK W d).b₄ / 2, e ^ 3 * (twistK W d).b₆ / 4⟩ :
    WeierstrassCurve K) = _
  rw [twistK_b₂ W h2, twistK_b₄ W h2, twistK_b₆ W h2]
  simp only [twistK]
  ext <;> simp only <;> ring

/-- **Changes of variables and twists**: `(C • W)^{(d)} = (u, d r, 0, 0) • W^{(d)}`. -/
theorem twistK_smul (C : VariableChange K) (d : K) :
    twistK (C • W) d = (⟨C.u, d * C.r, 0, 0⟩ : VariableChange K) • twistK W d := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have h4 := four_ne_zero_of_two h2
  ext
  · simp [twistK, variableChange_a₁]
  · simp only [twistK, variableChange_a₂, variableChange_b₂, Units.val_inv_eq_inv_val]
    field_simp; ring
  · simp [twistK, variableChange_a₃]
  · simp only [twistK, variableChange_a₄, variableChange_b₄, variableChange_b₂,
      Units.val_inv_eq_inv_val]
    field_simp; ring
  · simp only [twistK, variableChange_a₆, variableChange_b₆, variableChange_b₄,
      variableChange_b₂, Units.val_inv_eq_inv_val]
    field_simp; ring

/-- Completing the square: the change of variables `(1, 0, -a₁/2, -a₃/2)`. -/
def sqChange : VariableChange K := ⟨1, 0, -W.a₁ / 2, -W.a₃ / 2⟩

/-- `twistK W 1` is the completed-square model of `W`. -/
theorem twistK_one : twistK W 1 = sqChange W • W := by
  have h4 := four_ne_zero_of_two h2
  ext
  · simp only [twistK, sqChange, variableChange_a₁, inv_one, Units.val_one, one_mul]
    field_simp; ring
  · simp only [twistK, sqChange, variableChange_a₂, b₂, inv_one, Units.val_one, one_pow, one_mul]
    field_simp; ring
  · simp only [twistK, sqChange, variableChange_a₃, inv_one, Units.val_one, one_pow, one_mul]
    field_simp; ring
  · simp only [twistK, sqChange, variableChange_a₄, b₄, inv_one, Units.val_one, one_pow, one_mul]
    field_simp; ring
  · simp only [twistK, sqChange, variableChange_a₆, b₆, inv_one, Units.val_one, one_pow, one_mul]
    field_simp; ring

/-- Twisting by a square times `d`: `W^{(d e²)} = (e⁻¹, 0, 0, 0) • W^{(d)}`. -/
theorem twistK_mul_sq (d : K) {e : K} (he : e ≠ 0) :
    twistK W (d * e ^ 2) = (⟨Units.mk0 e⁻¹ (inv_ne_zero he), 0, 0, 0⟩ : VariableChange K) •
      twistK W d := by
  have h4 := four_ne_zero_of_two h2
  ext <;> simp [twistK, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆] <;> field_simp

/-- Over a field with `2 ≠ 0`, `twistInt W D c` is a change of variables of `twistK W D`. -/
theorem twistInt_eq_smul_twistK {D c : K} (h : D = 1 + 4 * c) :
    twistInt W D c = (sqChange (twistInt W D c))⁻¹ • twistK W D := by
  rw [eq_inv_smul_iff, ← twistK_one _ h2]
  simp only [twistK, twistInt_b₂ W h, twistInt_b₄ W h, twistInt_b₆ W h, one_mul, one_pow]

end Field

end ZInQ.Manuscript.RC.TwistDictionary
