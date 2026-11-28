import Mathlib

/-!
# Weierstrass normalization over a discrete valuation ring

Pure algebra (Mathlib only). Let `R` be a discrete valuation ring, `Ω` a field containing `R`
and `w` a valuation on `Ω` centred on the maximal ideal of `R` (`w ≤ 1` on `R`, `w < 1` on the
maximal ideal), so that `w` extends the valuation of `R` up to equivalence.

**Part 1 (normalization).** If `x, y ∈ Ω` satisfy an `R`-linear relation among
`1, x, y, x², xy, y², x³` whose `y²`- and `x³`-coefficients are units (so the relation is
primitive), then for the unit `e = -c₆ / c₅` the pair `(e x, e y)` lies on an explicit
`WeierstrassCurve R` (`exists_weierstrassCurve_of_relation`). The cubic relation is not monic in
`x³`, so this unit rescaling is the normalization step; any further change of variables
`C : WeierstrassCurve.VariableChange R` keeps the model `R`-integral and moves the point
accordingly (`equation_variableChange_map`).

**Part 2 (singular reduction).** If the reduction `W̄` of `W` is singular (`W.Δ` is not a unit)
and the residue field `k` of `R` is perfect, then `W̄` has a singular `k`-point `(x₀, y₀)`
(`exists_singular_point_of_Δ_eq_zero`). For a point `(X, Y)` of `W` with `w(X), w(Y) ≤ 1` whose
residue `X̄` is not a constant, the slope `t = (Ȳ - y₀) / (X̄ - x₀)` in the residue field `κ_w`
of `w` satisfies `X̄ = t² + a₁ t - a₂ - 2 x₀` and `Ȳ = y₀ + t (X̄ - x₀)`. Hence
`k(X̄, Ȳ) = k(t)` (a rational function field) and, for every valuation `ν` on `κ_w` that is
`≤ 1` on `k`, `t` has a pole exactly where `X̄` has one, with `ν(X̄) = ν(t)²`: if `X̄` has a
double pole at a place, `t` has a simple pole there and nowhere else
(`exists_param_of_not_isUnit_Δ`). This is the nodal/cuspidal parametrization.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

universe u

open WeierstrassCurve IsLocalRing

/-! ### Equations under ring homomorphisms and changes of variables -/

/-- A point of `W` maps to a point of `W.map f` under any ring homomorphism. -/
theorem weierstrass_equation_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (W : WeierstrassCurve A) {x y : A} (h : W.toAffine.Equation x y) :
    (W.map f).toAffine.Equation (f x) (f y) := by
  rw [Affine.equation_iff] at h ⊢
  have := congrArg f h
  simp only [map_add, map_mul, map_pow] at this
  simpa only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] using this

section VariableChange

variable {k : Type*} [Field k]

/-- The Weierstrass polynomial of `W` at the transformed point is `u⁶` times that of `C • W`. -/
theorem weierstrass_poly_variableChange (W : WeierstrassCurve k) (C : VariableChange k)
    (x y : k) :
    (C.u ^ 3 * y + C.s * C.u ^ 2 * x + C.t) ^ 2
        + W.a₁ * (C.u ^ 2 * x + C.r) * (C.u ^ 3 * y + C.s * C.u ^ 2 * x + C.t)
        + W.a₃ * (C.u ^ 3 * y + C.s * C.u ^ 2 * x + C.t)
        - ((C.u ^ 2 * x + C.r) ^ 3 + W.a₂ * (C.u ^ 2 * x + C.r) ^ 2
          + W.a₄ * (C.u ^ 2 * x + C.r) + W.a₆)
      = (C.u : k) ^ 6 * (y ^ 2 + (C • W).a₁ * x * y + (C • W).a₃ * y
          - (x ^ 3 + (C • W).a₂ * x ^ 2 + (C • W).a₄ * x + (C • W).a₆)) := by
  have hu : (C.u : k) ≠ 0 := C.u.ne_zero
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, Units.val_inv_eq_inv_val]
  field_simp
  ring

/-- The `y`-partial of `W` at the transformed point is `u³` times that of `C • W`. -/
theorem weierstrass_polyY_variableChange (W : WeierstrassCurve k) (C : VariableChange k)
    (x y : k) :
    2 * (C.u ^ 3 * y + C.s * C.u ^ 2 * x + C.t) + W.a₁ * (C.u ^ 2 * x + C.r) + W.a₃
      = (C.u : k) ^ 3 * (2 * y + (C • W).a₁ * x + (C • W).a₃) := by
  have hu : (C.u : k) ≠ 0 := C.u.ne_zero
  simp only [variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

/-- The `x`-partial of `W` at the transformed point, in terms of the partials of `C • W`. -/
theorem weierstrass_polyX_variableChange (W : WeierstrassCurve k) (C : VariableChange k)
    (x y : k) :
    W.a₁ * (C.u ^ 3 * y + C.s * C.u ^ 2 * x + C.t)
        - (3 * (C.u ^ 2 * x + C.r) ^ 2 + 2 * W.a₂ * (C.u ^ 2 * x + C.r) + W.a₄)
      = (C.u : k) ^ 4 * ((C • W).a₁ * y - (3 * x ^ 2 + 2 * (C • W).a₂ * x + (C • W).a₄))
        - C.s * C.u ^ 3 * (2 * y + (C • W).a₁ * x + (C • W).a₃) := by
  have hu : (C.u : k) ≠ 0 := C.u.ne_zero
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

/-- A singular point of `C • W` gives a singular point of `W`. -/
theorem singular_of_variableChange (W : WeierstrassCurve k) (C : VariableChange k) {x y : k}
    (h : (C • W).toAffine.Equation x y) (hs : ¬ (C • W).toAffine.Nonsingular x y) :
    W.toAffine.Equation (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.s * C.u ^ 2 * x + C.t) ∧
      ¬ W.toAffine.Nonsingular (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.s * C.u ^ 2 * x + C.t) := by
  rw [Affine.nonsingular_iff'] at hs
  have h' := h
  rw [Affine.equation_iff] at h'
  have hpd : (C • W).a₁ * y - (3 * x ^ 2 + 2 * (C • W).a₂ * x + (C • W).a₄) = 0 ∧
      2 * y + (C • W).a₁ * x + (C • W).a₃ = 0 := by
    by_contra hc
    exact hs ⟨h, by tauto⟩
  have hE : W.toAffine.Equation (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.s * C.u ^ 2 * x + C.t) := by
    rw [Affine.equation_iff, ← sub_eq_zero, weierstrass_poly_variableChange]
    simp only [toAffine] at h'
    rw [h', sub_self, mul_zero]
  refine ⟨hE, ?_⟩
  rw [Affine.nonsingular_iff']
  rintro ⟨-, hn⟩
  simp only [toAffine] at hn
  rw [weierstrass_polyX_variableChange, weierstrass_polyY_variableChange, hpd.1, hpd.2] at hn
  simp at hn

/-- Changes of variables move points: if `(X, Y)` lies on `W.map φ`, then the transformed point
lies on `(C • W).map φ`. With `C` defined over `R`, the new model stays `R`-integral. -/
theorem equation_variableChange_map {R : Type*} [CommRing R] (φ : R →+* k)
    (W : WeierstrassCurve R) (C : VariableChange R) {X Y : k}
    (h : (W.map φ).toAffine.Equation X Y) :
    ((C • W).map φ).toAffine.Equation (φ ↑C.u⁻¹ ^ 2 * (X - φ C.r))
      (φ ↑C.u⁻¹ ^ 3 * (Y - φ C.s * (X - φ C.r) - φ C.t)) := by
  rw [← map_variableChange]
  set C' := C.map φ with hC'
  have hu : (C'.u : k) = φ C.u := rfl
  have hr : C'.r = φ C.r := rfl
  have hs : C'.s = φ C.s := rfl
  have ht : C'.t = φ C.t := rfl
  have hu0 : (C'.u : k) ≠ 0 := C'.u.ne_zero
  have hinv : φ ↑C.u⁻¹ = (C'.u : k)⁻¹ := by
    rw [hu]
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  rw [Affine.equation_iff, ← sub_eq_zero]
  have key := weierstrass_poly_variableChange (W.map φ) C' (φ ↑C.u⁻¹ ^ 2 * (X - φ C.r))
    (φ ↑C.u⁻¹ ^ 3 * (Y - φ C.s * (X - φ C.r) - φ C.t))
  have hX : (C'.u : k) ^ 2 * (φ ↑C.u⁻¹ ^ 2 * (X - φ C.r)) + C'.r = X := by
    rw [hinv, hr]; field_simp; ring
  have hY : (C'.u : k) ^ 3 * (φ ↑C.u⁻¹ ^ 3 * (Y - φ C.s * (X - φ C.r) - φ C.t))
      + C'.s * C'.u ^ 2 * (φ ↑C.u⁻¹ ^ 2 * (X - φ C.r)) + C'.t = Y := by
    rw [hinv, hs, ht]; field_simp; ring
  rw [hX, hY] at key
  rw [Affine.equation_iff] at h
  have h0 : (C'.u : k) ^ 6 ≠ 0 := pow_ne_zero 6 hu0
  have := key.symm
  rw [h, sub_self] at this
  exact (mul_eq_zero.mp this).resolve_left h0

end VariableChange

/-! ### Part 1: normalization of the cubic relation -/

/-- **Normalization.** A relation `c₀ + c₁x + c₂y + c₃x² + c₄xy + c₅y² + c₆x³ = 0` over `R`
with unit `y²`- and `x³`-coefficients gives an `R`-integral Weierstrass curve through
`(e x, e y)`, `e = -c₆ c₅⁻¹`. -/
theorem exists_weierstrassCurve_of_relation {R Ω : Type*} [CommRing R] [CommRing Ω]
    [Algebra R Ω] {x y : Ω} {c₀ c₁ c₂ c₃ c₄ c₅ c₆ : R} (h₅ : IsUnit c₅) (h₆ : IsUnit c₆)
    (hrel : algebraMap R Ω c₀ + algebraMap R Ω c₁ * x + algebraMap R Ω c₂ * y
      + algebraMap R Ω c₃ * x ^ 2 + algebraMap R Ω c₄ * (x * y) + algebraMap R Ω c₅ * y ^ 2
      + algebraMap R Ω c₆ * x ^ 3 = 0) :
    ∃ (W : WeierstrassCurve R) (e : Rˣ),
      (W.map (algebraMap R Ω)).toAffine.Equation (algebraMap R Ω e * x) (algebraMap R Ω e * y) := by
  set d : R := ↑h₅.unit⁻¹ with hd
  let e : Rˣ := -(h₆.unit * h₅.unit⁻¹)
  have he : (e : R) = -(c₆ * d) := by simp [e, hd]
  have hcd : c₅ * d = 1 := h₅.mul_val_inv
  refine ⟨⟨c₄ * d, -(c₃ * d), c₂ * d * e, -(c₁ * d * e), -(c₀ * d * e ^ 2)⟩, e, ?_⟩
  rw [Affine.equation_iff]
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  have hcd' : algebraMap R Ω c₅ * algebraMap R Ω d = 1 := by rw [← map_mul, hcd, map_one]
  rw [he]
  simp only [map_neg, map_mul, map_pow]
  linear_combination (algebraMap R Ω c₆ * algebraMap R Ω d) ^ 2 * algebraMap R Ω d * hrel
    - (algebraMap R Ω c₆ * algebraMap R Ω d) ^ 2 * y ^ 2 * hcd'

/-- **Normalization**, for a relation `∑ cᵢ vᵢ = 0` on `v = (1, x, y, x², xy, y², x³)` whose
`y²`- and `x³`-coefficients are units. -/
theorem exists_weierstrassCurve_of_fin_relation {R Ω : Type*} [CommRing R] [CommRing Ω]
    [Algebra R Ω] {x y : Ω} (c : Fin 7 → R) (h₅ : IsUnit (c 5)) (h₆ : IsUnit (c 6))
    (hrel : ∑ i, c i • ![1, x, y, x ^ 2, x * y, y ^ 2, x ^ 3] i = 0) :
    ∃ (W : WeierstrassCurve R) (e : Rˣ),
      (W.map (algebraMap R Ω)).toAffine.Equation (algebraMap R Ω e * x) (algebraMap R Ω e * y) := by
  refine exists_weierstrassCurve_of_relation (c₀ := c 0) (c₁ := c 1) (c₂ := c 2) (c₃ := c 3)
    (c₄ := c 4) h₅ h₆ ?_
  rw [Fin.sum_univ_seven] at hrel
  simpa [Algebra.smul_def] using hrel

/-! ### Part 2a: a singular Weierstrass curve has a rational singular point -/

section Singular

variable {k : Type*} [Field k]

theorem exists_singular_of_partials (W : WeierstrassCurve k) {x y : k}
    (hE : W.toAffine.Equation x y)
    (hX : W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 0)
    (hY : 2 * y + W.a₁ * x + W.a₃ = 0) :
    ∃ x y : k, W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
  refine ⟨x, y, hE, ?_⟩
  rw [Affine.nonsingular_iff']
  rintro ⟨-, h | h⟩
  · exact h hX
  · exact h hY

/-- Singular point in characteristic different from `2` and `3` (short normal form). -/
theorem exists_singular_point_short (W : WeierstrassCurve k) [W.IsShortNF]
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (hΔ : W.Δ = 0) :
    ∃ x y : k, W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
  have ha₁ : W.a₁ = 0 := IsShortNF.a₁
  have ha₂ : W.a₂ = 0 := IsShortNF.a₂
  have ha₃ : W.a₃ = 0 := IsShortNF.a₃
  rw [Δ_of_isShortNF] at hΔ
  have h16 : (16 : k) ≠ 0 := by
    have : (16 : k) = 2 ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero 4 h2
  have hrel : 4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2 = 0 := by
    have := mul_eq_zero.mp (neg_eq_zero.mp (by rw [neg_mul] at hΔ; exact hΔ))
    exact this.resolve_left h16
  by_cases h4 : W.a₄ = 0
  · have h27 : (27 : k) ≠ 0 := by
      have : (27 : k) = 3 ^ 3 := by norm_num
      rw [this]; exact pow_ne_zero 3 h3
    have ha₆ : W.a₆ = 0 := by
      rw [h4] at hrel
      have : 27 * W.a₆ ^ 2 = 0 := by linear_combination hrel
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp this).resolve_left h27)
    refine exists_singular_of_partials W (x := 0) (y := 0) ?_ ?_ ?_
    · rw [Affine.equation_iff]; simp [h4, ha₆]
    · simp [h4]
    · simp
  · have h8 : (8 : k) ≠ 0 := by
      have : (8 : k) = 2 ^ 3 := by norm_num
      rw [this]; exact pow_ne_zero 3 h2
    have h4' : (4 : k) ≠ 0 := by
      have : (4 : k) = 2 ^ 2 := by norm_num
      rw [this]; exact pow_ne_zero 2 h2
    refine exists_singular_of_partials W (x := -3 * W.a₆ / (2 * W.a₄)) (y := 0) ?_ ?_ ?_
    · rw [Affine.equation_iff]
      simp only [ha₁, ha₂, ha₃]
      have : (-3 * W.a₆ / (2 * W.a₄)) ^ 3 + W.a₄ * (-3 * W.a₆ / (2 * W.a₄)) + W.a₆
          = -W.a₆ * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) / (8 * W.a₄ ^ 3) := by
        field_simp; ring
      rw [hrel, mul_zero, zero_div] at this
      linear_combination -this
    · simp only [ha₁, ha₂]
      have : 3 * (-3 * W.a₆ / (2 * W.a₄)) ^ 2 + W.a₄
          = (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) / (4 * W.a₄ ^ 2) := by
        field_simp; ring
      rw [hrel, zero_div] at this
      linear_combination -this
    · simp

/-- Singular point in characteristic `3`. -/
theorem exists_singular_point_char_three [PerfectField k] [CharP k 3] (W : WeierstrassCurve k)
    (hNF : W.IsCharThreeNF) (hΔ : W.Δ = 0) :
    ∃ x y : k, W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
  have h3 : (3 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 3
  -- the cuspidal case `y² = x³ + a₆`, through a cube root of `-a₆`
  have cusp : W.a₁ = 0 → W.a₂ = 0 → W.a₃ = 0 → W.a₄ = 0 →
      ∃ x y : k, W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
    intro ha₁ ha₂ ha₃ ha₄
    obtain ⟨c, hc⟩ := surjective_frobenius k 3 (-W.a₆)
    rw [frobenius_def] at hc
    refine exists_singular_of_partials W (x := c) (y := 0) ?_ ?_ ?_
    · rw [Affine.equation_iff]; simp only [ha₁, ha₂, ha₃, ha₄]; linear_combination -hc
    · simp only [ha₁, ha₂, ha₄]; linear_combination (-c ^ 2) * h3
    · rw [ha₁, ha₃]; ring
  cases hNF with
  | of_j_ne_zero =>
    have ha₁ : W.a₁ = 0 := IsCharThreeJNeZeroNF.a₁
    have ha₃ : W.a₃ = 0 := IsCharThreeJNeZeroNF.a₃
    have ha₄ : W.a₄ = 0 := IsCharThreeJNeZeroNF.a₄
    rw [Δ_of_isCharThreeJNeZeroNF] at hΔ
    have h0 : W.a₂ ^ 3 * W.a₆ = 0 := by
      linear_combination -hΔ + (-21 * W.a₂ ^ 3 * W.a₆ - 144 * W.a₆ ^ 2) * h3
    rcases mul_eq_zero.mp h0 with h | h
    · exact cusp ha₁ (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h) ha₃ ha₄
    · refine exists_singular_of_partials W (x := 0) (y := 0) ?_ ?_ ?_
      · rw [Affine.equation_iff]; simp [h]
      · simp
      · simp
  | of_j_eq_zero =>
    have ha₁ : W.a₁ = 0 := IsShortNF.a₁
    have ha₂ : W.a₂ = 0 := IsShortNF.a₂
    have ha₃ : W.a₃ = 0 := IsShortNF.a₃
    rw [Δ_of_isShortNF_of_char_three] at hΔ
    have ha₄ : W.a₄ = 0 := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp (neg_eq_zero.mp hΔ)
    exact cusp ha₁ ha₂ ha₃ ha₄

/-- Singular point in characteristic `2`. -/
theorem exists_singular_point_char_two [PerfectField k] [CharP k 2] (W : WeierstrassCurve k)
    (hNF : W.IsCharTwoNF) (hΔ : W.Δ = 0) :
    ∃ x y : k, W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
  have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  cases hNF with
  | of_j_ne_zero =>
    have ha₁ : W.a₁ = 1 := IsCharTwoJNeZeroNF.a₁
    have ha₃ : W.a₃ = 0 := IsCharTwoJNeZeroNF.a₃
    have ha₄ : W.a₄ = 0 := IsCharTwoJNeZeroNF.a₄
    have hΔ' : W.Δ = -W.a₆ + 2 * (-W.a₆ * (6 * W.a₂ + 24 * W.a₂ ^ 2 + 32 * W.a₂ ^ 3)
        - 216 * W.a₆ ^ 2) := by
      simp only [Δ, b₂, b₄, b₆, b₈, ha₁, ha₃, ha₄]; ring
    have ha₆ : W.a₆ = 0 := by
      rw [hΔ'] at hΔ
      linear_combination -hΔ
        + (-W.a₆ * (6 * W.a₂ + 24 * W.a₂ ^ 2 + 32 * W.a₂ ^ 3) - 216 * W.a₆ ^ 2) * h2
    refine exists_singular_of_partials W (x := 0) (y := 0) ?_ ?_ ?_
    · rw [Affine.equation_iff]; simp [ha₆]
    · simp
    · simp
  | of_j_eq_zero =>
    have ha₁ : W.a₁ = 0 := IsCharTwoJEqZeroNF.a₁
    have ha₂ : W.a₂ = 0 := IsCharTwoJEqZeroNF.a₂
    have hΔ' : W.Δ = -W.a₃ ^ 4 + 2 * (-32 * W.a₄ ^ 3 - 13 * W.a₃ ^ 4
        - 108 * W.a₃ ^ 2 * W.a₆ - 216 * W.a₆ ^ 2) := by
      rw [Δ_of_isCharTwoJEqZeroNF]; simp only [b₆]; ring
    have ha₃ : W.a₃ = 0 := by
      rw [hΔ'] at hΔ
      have : W.a₃ ^ 4 = 0 := by
        linear_combination -hΔ + (-32 * W.a₄ ^ 3 - 13 * W.a₃ ^ 4
          - 108 * W.a₃ ^ 2 * W.a₆ - 216 * W.a₆ ^ 2) * h2
      exact pow_eq_zero_iff (n := 4) (by norm_num) |>.mp this
    obtain ⟨c, hc⟩ := surjective_frobenius k 2 W.a₄
    obtain ⟨d, hd⟩ := surjective_frobenius k 2 W.a₆
    rw [frobenius_def] at hc hd
    refine exists_singular_of_partials W (x := c) (y := d) ?_ ?_ ?_
    · rw [Affine.equation_iff]; simp only [ha₁, ha₂, ha₃]
      linear_combination hd - c * hc + (- W.a₄ * c) * h2
    · simp only [ha₁, ha₂]; linear_combination (-3) * hc + (-2 * W.a₄) * h2
    · simp only [ha₁, ha₃]; linear_combination d * h2

/-- **Singular reduction has a rational singular point.** Over a perfect field, a Weierstrass
curve with `Δ = 0` has a singular point with coordinates in the field. -/
theorem exists_singular_point_of_Δ_eq_zero [PerfectField k] (W : WeierstrassCurve k)
    (hΔ : W.Δ = 0) : ∃ x y : k, W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
  -- reduce to a normal form `C • W`, find a singular point there and move it back
  suffices h : ∃ C : VariableChange k, ∃ x y : k,
      (C • W).toAffine.Equation x y ∧ ¬ (C • W).toAffine.Nonsingular x y by
    obtain ⟨C, x, y, hE, hs⟩ := h
    exact ⟨_, _, singular_of_variableChange W C hE hs⟩
  have hΔC : ∀ C : VariableChange k, (C • W).Δ = 0 := fun C => by
    rw [variableChange_Δ, hΔ, mul_zero]
  by_cases h2 : (2 : k) = 0
  · have : CharP k 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by exact_mod_cast h2)
    obtain ⟨C, hC⟩ := exists_variableChange_isCharTwoNF W
    exact ⟨C, exists_singular_point_char_two (C • W) hC (hΔC C)⟩
  by_cases h3 : (3 : k) = 0
  · have : CharP k 3 :=
      (CharP.charP_iff_prime_eq_zero Nat.prime_three).mpr (by exact_mod_cast h3)
    obtain ⟨C, hC⟩ := exists_variableChange_isCharThreeNF W
    exact ⟨C, exists_singular_point_char_three (C • W) hC (hΔC C)⟩
  have : Invertible (2 : k) := invertibleOfNonzero h2
  have : Invertible (3 : k) := invertibleOfNonzero h3
  obtain ⟨C, hC⟩ := exists_variableChange_isShortNF W
  exact ⟨C, exists_singular_point_short (C • W) h2 h3 (hΔC C)⟩

end Singular

/-! ### Part 2b: the parametrization through a singular point -/

section Param

variable {k K : Type*} [Field k] [Field K]

/-- **Parametrization through a singular point.** If `(x₀, y₀)` is a singular point of `W` over
`k` and `(X, Y)` is a point of `W.map φ` with `X ≠ x₀`, the slope `t = (Y - y₀) / (X - x₀)`
satisfies `X = t² + a₁ t - a₂ - 2 x₀` and `Y = y₀ + t (X - x₀)`. -/
theorem param_of_singular (φ : k →+* K) (W : WeierstrassCurve k) {x₀ y₀ : k}
    (h₀ : W.toAffine.Equation x₀ y₀) (hs : ¬ W.toAffine.Nonsingular x₀ y₀) {X Y : K}
    (hE : (W.map φ).toAffine.Equation X Y) (hX : X ≠ φ x₀) :
    X = ((Y - φ y₀) / (X - φ x₀)) ^ 2 + φ W.a₁ * ((Y - φ y₀) / (X - φ x₀)) - φ W.a₂
        - 2 * φ x₀ ∧
      Y = φ y₀ + (Y - φ y₀) / (X - φ x₀) * (X - φ x₀) := by
  have hX0 : X - φ x₀ ≠ 0 := sub_ne_zero.mpr hX
  set t := (Y - φ y₀) / (X - φ x₀) with htdef
  have ht : Y = φ y₀ + t * (X - φ x₀) := by rw [htdef]; field_simp; ring
  refine ⟨?_, ht⟩
  rw [Affine.nonsingular_iff'] at hs
  have hpd : W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) = 0 ∧
      2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    by_contra hc
    exact hs ⟨h₀, by tauto⟩
  rw [Affine.equation_iff] at h₀ hE
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at hE
  have h₀' := congrArg φ h₀
  have hFx := congrArg φ hpd.1
  have hFy := congrArg φ hpd.2
  simp only [map_add, map_mul, map_pow, map_sub, map_ofNat, map_zero] at h₀' hFx hFy
  have key : (X - φ x₀) ^ 2 * (X - (t ^ 2 + φ W.a₁ * t - φ W.a₂ - 2 * φ x₀)) = 0 := by
    linear_combination h₀' - hE + (X - φ x₀) * hFx + t * (X - φ x₀) * hFy
      + (Y + φ y₀ + t * (X - φ x₀) + φ W.a₁ * X + φ W.a₃) * ht
  have := (mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 hX0)
  exact sub_eq_zero.mp this

/-- **Pole orders of the parameter.** If `X = t² + a t + b` with `ν(a), ν(b) ≤ 1`, then `X` has
a pole exactly where `t` has one, and there `ν(X) = ν(t)²`. -/
theorem valuation_of_eq_sq_add {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (ν : Valuation K Γ)
    {X t a b : K} (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hX : X = t ^ 2 + a * t + b) :
    (1 < ν t ↔ 1 < ν X) ∧ (1 < ν t → ν X = ν t ^ 2) := by
  have hpole : 1 < ν t → ν X = ν t ^ 2 := by
    intro ht
    have h1 : ν (a * t) < ν (t ^ 2) := by
      rw [map_mul, map_pow]
      calc ν a * ν t ≤ 1 * ν t := by gcongr
        _ = ν t ^ 1 := by rw [one_mul, pow_one]
        _ < ν t ^ 2 := pow_lt_pow_right₀ ht (by norm_num)
    have h2 : ν (t ^ 2 + a * t) = ν t ^ 2 := by
      rw [Valuation.map_add_eq_of_lt_left _ h1, map_pow]
    have h3 : ν b < ν (t ^ 2 + a * t) := by
      rw [h2]; exact hb.trans_lt (one_lt_pow₀ ht (by norm_num))
    rw [hX, Valuation.map_add_eq_of_lt_left _ h3, h2]
  refine ⟨⟨fun ht => ?_, fun hX1 => ?_⟩, hpole⟩
  · rw [hpole ht]; exact one_lt_pow₀ ht (by norm_num)
  · by_contra ht
    have ht' : ν t ≤ 1 := not_lt.mp ht
    have : ν X ≤ 1 := by
      rw [hX]
      refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) hb
      · rw [map_pow]; exact pow_le_one₀ zero_le ht'
      · rw [map_mul]; exact mul_le_one' ha ht'
    exact absurd hX1 (not_lt.mpr this)

/-- A double pole of `X` gives a simple pole of `t`: `ν(X) = δ²`, `1 < δ` imply `ν(t) = δ`. -/
theorem valuation_eq_of_sq_eq {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (ν : Valuation K Γ) {X t a b : K} (ha : ν a ≤ 1) (hb : ν b ≤ 1)
    (hX : X = t ^ 2 + a * t + b) {δ : Γ} (hδ : 1 < δ) (hXδ : ν X = δ ^ 2) : ν t = δ := by
  obtain ⟨hiff, hsq⟩ := valuation_of_eq_sq_add ν ha hb hX
  have ht : 1 < ν t := hiff.mpr (hXδ ▸ one_lt_pow₀ hδ (by norm_num))
  have h := (hsq ht).symm.trans hXδ
  exact le_antisymm ((pow_le_pow_iff_left₀ zero_le zero_le two_ne_zero).mp h.le)
    ((pow_le_pow_iff_left₀ zero_le zero_le two_ne_zero).mp h.ge)

/-- The field generated by `X, Y` over the image of `k` is generated by `t` alone. -/
theorem closure_eq_closure_param (φ : k →+* K) {X Y t : K} (c₁ c₂ x₀ y₀ : k)
    (hX : X = t ^ 2 + φ c₁ * t - φ c₂ - 2 * φ x₀) (hY : Y = φ y₀ + t * (X - φ x₀))
    (ht : t = (Y - φ y₀) / (X - φ x₀)) :
    Subfield.closure (Set.range φ ∪ {X, Y}) = Subfield.closure (Set.range φ ∪ {t}) := by
  have h2 : (2 : K) * φ x₀ = φ (2 * x₀) := by rw [map_mul, map_ofNat]
  apply le_antisymm
  · rw [Subfield.closure_le]
    set S := Subfield.closure (Set.range φ ∪ {t})
    have hφ : ∀ c, φ c ∈ S := fun c => Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
    have htS : t ∈ S := Subfield.subset_closure (Or.inr rfl)
    have hXS : X ∈ S := by
      rw [hX, h2]
      exact sub_mem (sub_mem (add_mem (pow_mem htS 2) (mul_mem (hφ _) htS)) (hφ _)) (hφ _)
    have hYS : Y ∈ S := by
      rw [hY]; exact add_mem (hφ _) (mul_mem htS (sub_mem hXS (hφ _)))
    rintro z (⟨c, rfl⟩ | hz)
    · exact hφ c
    · rcases hz with rfl | rfl
      · exact hXS
      · exact hYS
  · rw [Subfield.closure_le]
    set S := Subfield.closure (Set.range φ ∪ {X, Y})
    have hφ : ∀ c, φ c ∈ S := fun c => Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
    have hXS : X ∈ S := Subfield.subset_closure (Or.inr (Or.inl rfl))
    have hYS : Y ∈ S := Subfield.subset_closure (Or.inr (Or.inr rfl))
    rintro z (⟨c, rfl⟩ | hz)
    · exact hφ c
    · rw [Set.mem_singleton_iff] at hz
      rw [hz, ht]
      exact div_mem (sub_mem hYS (hφ _)) (sub_mem hXS (hφ _))

/-- The conclusion of the singular case: a singular `k`-point `(x₀, y₀)` of `W` and the slope
`t = (Y - y₀) / (X - x₀)`, which parametrizes `(X, Y)` (`X = t² + a₁ t - a₂ - 2 x₀`,
`Y = y₀ + t (X - x₀)`), generates `k(X, Y)` and has a pole exactly where `X` has one, with
`ν(X) = ν(t)²` there (an element of pole degree `1` relative to `X`). -/
def IsSingularParam (φ : k →+* K) (W : WeierstrassCurve k) (X Y : K) : Prop :=
  ∃ (x₀ y₀ : k) (t : K), W.toAffine.Equation x₀ y₀ ∧ ¬ W.toAffine.Nonsingular x₀ y₀ ∧
    t = (Y - φ y₀) / (X - φ x₀) ∧
    X = t ^ 2 + φ W.a₁ * t - φ W.a₂ - 2 * φ x₀ ∧ Y = φ y₀ + t * (X - φ x₀) ∧
    Subfield.closure (Set.range φ ∪ {X, Y}) = Subfield.closure (Set.range φ ∪ {t}) ∧
    ∀ (Γ : Type u) [LinearOrderedCommGroupWithZero Γ] (ν : Valuation K Γ),
      (∀ c, ν (φ c) ≤ 1) → (1 < ν t ↔ 1 < ν X) ∧ (1 < ν t → ν X = ν t ^ 2)

/-- **Singular Weierstrass curves are parametrized.** Over a perfect field `k`, if `Δ_W = 0` and
`(X, Y)` lies on `W.map φ` with `X` not a constant, then `IsSingularParam φ W X Y`. -/
theorem isSingularParam_of_Δ_eq_zero [PerfectField k] (φ : k →+* K) (W : WeierstrassCurve k)
    (hΔ : W.Δ = 0) {X Y : K} (hE : (W.map φ).toAffine.Equation X Y) (hX : ∀ c, φ c ≠ X) :
    IsSingularParam.{u} φ W X Y := by
  obtain ⟨x₀, y₀, h₀, hs⟩ := exists_singular_point_of_Δ_eq_zero W hΔ
  obtain ⟨hXt, hYt⟩ := param_of_singular φ W h₀ hs hE (fun h => hX x₀ h.symm)
  set t := (Y - φ y₀) / (X - φ x₀) with htdef
  refine ⟨x₀, y₀, t, h₀, hs, rfl, hXt, hYt,
    closure_eq_closure_param φ W.a₁ W.a₂ x₀ y₀ hXt hYt rfl, ?_⟩
  intro Γ _ ν hν
  have hb : ν (φ (-W.a₂ - 2 * x₀)) ≤ 1 := hν _
  refine valuation_of_eq_sq_add ν (hν W.a₁) hb ?_
  rw [hXt]; simp only [map_sub, map_neg, map_mul, map_ofNat]; ring

end Param

/-! ### Part 2c: reduction modulo the valuation `w` -/

section Residue

variable {R : Type*} [CommRing R] [IsLocalRing R] {Ω : Type*} [Field Ω] [Algebra R Ω]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation Ω Γ₀)

/-- `R → 𝒪_w`, for `w ≤ 1` on `R`. -/
def toIntegers (hR : ∀ r : R, w (algebraMap R Ω r) ≤ 1) : R →+* w.valuationSubring :=
  (algebraMap R Ω).codRestrict w.valuationSubring
    fun r => (w.mem_valuationSubring_iff _).2 (hR r)

omit [IsLocalRing R] in
theorem coe_toIntegers (hR : ∀ r : R, w (algebraMap R Ω r) ≤ 1) (r : R) :
    (toIntegers w hR r : Ω) = algebraMap R Ω r := rfl

/-- `R → 𝒪_w` is local when `w < 1` on the maximal ideal of `R`. -/
theorem isLocalHom_toIntegers (hR : ∀ r : R, w (algebraMap R Ω r) ≤ 1)
    (hm : ∀ r ∈ maximalIdeal R, w (algebraMap R Ω r) < 1) : IsLocalHom (toIntegers w hR) := by
  constructor
  intro r hr
  by_contra hnu
  have hlt := hm r ((mem_maximalIdeal r).2 (mem_nonunits_iff.2 hnu))
  obtain ⟨b, hb⟩ := hr.exists_right_inv
  have h1 : w (algebraMap R Ω r) * w (b : Ω) = 1 := by
    rw [← map_mul, ← coe_toIntegers w hR r]
    have : (toIntegers w hR r : Ω) * b = 1 := by exact_mod_cast congrArg Subtype.val hb
    rw [this, map_one]
  have hb1 : w (b : Ω) ≤ 1 := (w.mem_valuationSubring_iff _).1 b.2
  have h2 : w (algebraMap R Ω r) * w (b : Ω) < 1 :=
    calc w (algebraMap R Ω r) * w (b : Ω) ≤ w (algebraMap R Ω r) * 1 := by gcongr
      _ < 1 := by rwa [mul_one]
  rw [h1] at h2
  exact lt_irrefl _ h2

/-- The induced map of residue fields `κ_R → κ_w`. -/
def residueHom (hR : ∀ r : R, w (algebraMap R Ω r) ≤ 1)
    (hm : ∀ r ∈ maximalIdeal R, w (algebraMap R Ω r) < 1) :
    ResidueField R →+* ResidueField w.valuationSubring :=
  haveI := isLocalHom_toIntegers w hR hm
  ResidueField.map (toIntegers w hR)

/-- The residue in `κ_w` of an element with `w ≤ 1`. -/
def reduce (x : Ω) (hx : w x ≤ 1) : ResidueField w.valuationSubring :=
  residue w.valuationSubring ⟨x, (w.mem_valuationSubring_iff x).2 hx⟩

omit [IsLocalRing R] in
theorem valuation_algebraMap_mul_le (hR : ∀ r : R, w (algebraMap R Ω r) ≤ 1) (r : R) {x : Ω}
    (hx : w x ≤ 1) : w (algebraMap R Ω r * x) ≤ 1 := by
  rw [map_mul]; exact mul_le_one' (hR r) hx

theorem reduce_algebraMap_mul (hR : ∀ r : R, w (algebraMap R Ω r) ≤ 1)
    (hm : ∀ r ∈ maximalIdeal R, w (algebraMap R Ω r) < 1) (r : R) {x : Ω} (hx : w x ≤ 1) :
    reduce w (algebraMap R Ω r * x) (valuation_algebraMap_mul_le w hR r hx)
      = residueHom w hR hm (residue R r) * reduce w x hx := by
  have := isLocalHom_toIntegers w hR hm
  rw [residueHom, ResidueField.map_residue, reduce, reduce, ← map_mul]
  rfl

/-- **Reduction of a point.** A point `(X, Y)` of `W` over `Ω` with `w(X), w(Y) ≤ 1` reduces to a
point of the reduction `W̄` over `κ_w`. -/
theorem reduce_equation (hR : ∀ r : R, w (algebraMap R Ω r) ≤ 1)
    (hm : ∀ r ∈ maximalIdeal R, w (algebraMap R Ω r) < 1) (W : WeierstrassCurve R) {X Y : Ω}
    (hX : w X ≤ 1) (hY : w Y ≤ 1) (hE : (W.map (algebraMap R Ω)).toAffine.Equation X Y) :
    ((W.map (residue R)).map (residueHom w hR hm)).toAffine.Equation (reduce w X hX)
      (reduce w Y hY) := by
  have := isLocalHom_toIntegers w hR hm
  have h1 : (W.map (toIntegers w hR)).toAffine.Equation
      ⟨X, (w.mem_valuationSubring_iff X).2 hX⟩ ⟨Y, (w.mem_valuationSubring_iff Y).2 hY⟩ := by
    rw [Affine.equation_iff] at hE ⊢
    apply Subtype.ext
    simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at hE ⊢
    push_cast
    simpa only [coe_toIntegers] using hE
  have h2 := weierstrass_equation_map (residue w.valuationSubring) _ h1
  rw [map_map, ← ResidueField.map_comp_residue, ← map_map] at h2
  exact h2

/-- **Singular reduction (Part 2).** Let `W` be a Weierstrass curve over `R` whose reduction is
singular (`Δ_W` not a unit), with perfect residue field `k`, and `(X, Y)` a point of `W` over `Ω`
with `w(X), w(Y) ≤ 1` and non-constant residue `X̄`. Then `W̄` has a singular `k`-point
`(x₀, y₀)`, and `t = (Ȳ - y₀) / (X̄ - x₀) ∈ κ_w` satisfies `k(X̄, Ȳ) = k(t)`,
`X̄ = t² + a₁ t - a₂ - 2 x₀`, `Ȳ = y₀ + t (X̄ - x₀)`, and `t` has a pole exactly where `X̄` has
one, of half its order. -/
theorem isSingularParam_reduce [PerfectField (ResidueField R)]
    (hR : ∀ r : R, w (algebraMap R Ω r) ≤ 1)
    (hm : ∀ r ∈ maximalIdeal R, w (algebraMap R Ω r) < 1) (W : WeierstrassCurve R) {X Y : Ω}
    (hX : w X ≤ 1) (hY : w Y ≤ 1) (hE : (W.map (algebraMap R Ω)).toAffine.Equation X Y)
    (hΔ : ¬ IsUnit W.Δ) (hnc : ∀ c, residueHom w hR hm c ≠ reduce w X hX) :
    IsSingularParam.{u} (residueHom w hR hm) (W.map (residue R)) (reduce w X hX)
      (reduce w Y hY) := by
  have hΔ' : (W.map (residue R)).Δ = 0 := by
    rw [map_Δ]
    by_contra h
    exact hΔ ((residue_ne_zero_iff_isUnit _).mp h)
  exact isSingularParam_of_Δ_eq_zero _ _ hΔ' (reduce_equation w hR hm W hX hY hE) hnc

end Residue

/-! ### N10a: normalization over a discrete valuation ring -/

/-- **Weierstrass normalization over a DVR (N10a).** Let `R` be a discrete valuation ring with
perfect residue field, `Ω` a field over `R` and `w` a valuation on `Ω` with `w ≤ 1` on `R` and
`w < 1` on its maximal ideal. Let `x, y ∈ Ω` with `w(x), w(y) ≤ 1` satisfy a relation
`c₀ + c₁x + c₂y + c₃x² + c₄xy + c₅y² + c₆x³ = 0` over `R` with `c₅, c₆` units. Then there are a
Weierstrass curve `W` over `R` and a unit `e` with `(e x, e y)` on `W`; and if the reduction of
`W` is singular and `x̄` is not a constant, the reduced point is parametrized by an element
`t ∈ κ_w` of pole degree one relative to `x̄` (`IsSingularParam`). -/
theorem weierstrass_normalization_dvr {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] {Ω : Type*} [Field Ω]
    [Algebra R Ω] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation Ω Γ₀)
    (hR : ∀ r : R, w (algebraMap R Ω r) ≤ 1)
    (hm : ∀ r ∈ maximalIdeal R, w (algebraMap R Ω r) < 1) {x y : Ω} (hx : w x ≤ 1)
    (hy : w y ≤ 1) {c₀ c₁ c₂ c₃ c₄ c₅ c₆ : R} (h₅ : IsUnit c₅) (h₆ : IsUnit c₆)
    (hrel : algebraMap R Ω c₀ + algebraMap R Ω c₁ * x + algebraMap R Ω c₂ * y
      + algebraMap R Ω c₃ * x ^ 2 + algebraMap R Ω c₄ * (x * y) + algebraMap R Ω c₅ * y ^ 2
      + algebraMap R Ω c₆ * x ^ 3 = 0) :
    ∃ (W : WeierstrassCurve R) (e : Rˣ),
      (W.map (algebraMap R Ω)).toAffine.Equation (algebraMap R Ω e * x)
        (algebraMap R Ω e * y) ∧
      (¬ IsUnit W.Δ → (∀ c, residueHom w hR hm c ≠ reduce w x hx) →
        IsSingularParam.{u} (residueHom w hR hm) (W.map (residue R))
          (reduce w (algebraMap R Ω e * x) (valuation_algebraMap_mul_le w hR e hx))
          (reduce w (algebraMap R Ω e * y) (valuation_algebraMap_mul_le w hR e hy))) := by
  obtain ⟨W, e, hE⟩ := exists_weierstrassCurve_of_relation h₅ h₆ hrel
  refine ⟨W, e, hE, fun hΔ hnc => isSingularParam_reduce w hR hm W _ _ hE hΔ ?_⟩
  intro c hc
  rw [reduce_algebraMap_mul w hR hm _ hx] at hc
  have he : residueHom w hR hm (residue R e) ≠ 0 := by
    rw [map_ne_zero]
    exact (residue_ne_zero_iff_isUnit _).mpr e.isUnit
  apply hnc (c * (residue R e)⁻¹)
  rw [map_mul, map_inv₀, hc]
  field_simp

end ZInQ.Contrib.CMHeight62Full
