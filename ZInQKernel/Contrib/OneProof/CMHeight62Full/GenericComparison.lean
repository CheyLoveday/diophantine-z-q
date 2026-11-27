import Mathlib

/-!
# Step 7, generic comparison: two Weierstrass equations at the same origin

Field-level comparison of Weierstrass equations on the generic fibre (Mathlib only).

Let `Ω ⊇ L` be fields (in the application, `Ω` is the function field of the elliptic curve over
`L`) and let `w` be a valuation on `Ω` that is trivial on `L` (the origin place). Let `(x, y)` and
`(x₀, y₀)` satisfy the Weierstrass equations of `W` and `W₀ : WeierstrassCurve L`, both with
poles of orders `2` and `3` at the origin (`w x = w x₀ = δ ^ 2`, `w y = w y₀ = δ ^ 3`, `1 < δ`).
If the pole spaces are spanned by `1, x` and `1, x, y`, then
`x₀ = u²x + r` and `y₀ = u³y + su²x + t` for one `C = (u, r, s, t)`, and `C • W₀ = W`, that is,
`C⁻¹ • W = W₀` (Mathlib's convention: `C • W₀` is the curve in the coordinates `(x, y)`).

* `exists_variableChange_of_mem_span`: the algebraic core, from `x₀ ∈ ⟨1, x⟩` and
  `y₀ ∈ ⟨1, x, y⟩`.
* `exists_variableChange_of_poleSpaces`: the valuation form. A set `S` stands for the functions
  regular away from the origin (in a function field) or for all of `Ω`; the hypotheses say
  `{f ∈ S : w f ≤ δ ^ 2} = ⟨1, x⟩` and `{f ∈ S : w f ≤ δ ^ 3} = ⟨1, x, y⟩`.

The proof compares coefficients: by the valuations, `1, x, y, x², xy, x³` are linearly
independent over `L`. The `x³`-coefficient of `F₀(x₀, y₀) - c² F(x, y)` gives `c² = a³` for
`x₀ = a x + b`, `y₀ = c y + d x + e`, so `u = c / a`; then `u⁶ F_{C • W₀}(x, y) = F₀(x₀, y₀)` and
the remaining coefficients of `F_{C • W₀}(x, y) - F(x, y)` give `C • W₀ = W`.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open WeierstrassCurve

/-- The Weierstrass equation of `C • V` at `(x, y)` follows from that of `V` at the transformed
point `(u²x + r, u³y + su²x + t)`. -/
theorem genCmp_equation_smul {Ω : Type*} [Field Ω] (V : WeierstrassCurve Ω)
    (C : VariableChange Ω) {x y : Ω}
    (h : V.toAffine.Equation (↑C.u ^ 2 * x + C.r) (↑C.u ^ 3 * y + C.s * ↑C.u ^ 2 * x + C.t)) :
    (C • V).toAffine.Equation x y := by
  rw [Affine.equation_iff] at h ⊢
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, Units.val_inv_eq_inv_val]
  have hu : (C.u : Ω) ≠ 0 := C.u.ne_zero
  field_simp
  linear_combination h

variable {L Ω : Type*} [Field L] [Field Ω] [Algebra L Ω]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The Weierstrass equation of `W.baseChange Ω`, with the coefficients pushed to `Ω`. -/
theorem genCmp_equation_baseChange_iff (W : WeierstrassCurve L) (x y : Ω) :
    (W.baseChange Ω).toAffine.Equation x y ↔
      y ^ 2 + algebraMap L Ω W.a₁ * x * y + algebraMap L Ω W.a₃ * y =
        x ^ 3 + algebraMap L Ω W.a₂ * x ^ 2 + algebraMap L Ω W.a₄ * x + algebraMap L Ω W.a₆ := by
  rw [Affine.equation_iff]
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]

section Valuation

variable (w : Valuation Ω Γ₀) (hL : ∀ c : L, c ≠ 0 → w (algebraMap L Ω c) = 1)
include hL

theorem genCmp_val_smul_le (c : L) (f : Ω) : w (algebraMap L Ω c * f) ≤ w f := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [map_mul, hL c hc, one_mul]

theorem genCmp_coeff_eq_zero {c : L} {f g : Ω} (h : algebraMap L Ω c * f + g = 0)
    (hg : w g < w f) : c = 0 := by
  by_contra hc
  have h2 := congrArg w (eq_neg_of_add_eq_zero_left h)
  rw [map_mul, hL c hc, one_mul, Valuation.map_neg] at h2
  exact hg.ne' h2

/-- With `w x = δ ^ 2` and `w y = δ ^ 3`, the functions `x³, xy, x², y, x, 1` are linearly
independent over `L` (their valuations are distinct). -/
theorem genCmp_coeffs_eq_zero {δ : Γ₀} (hδ : 1 < δ) {x y : Ω} (hx : w x = δ ^ 2)
    (hy : w y = δ ^ 3) {a b c d e f : L}
    (h : algebraMap L Ω a * x ^ 3 + (algebraMap L Ω b * (x * y) + (algebraMap L Ω c * x ^ 2 +
      (algebraMap L Ω d * y + (algebraMap L Ω e * x + algebraMap L Ω f)))) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 := by
  have h1 : (1 : Γ₀) ≤ δ := hδ.le
  have hb : ∀ (c : L) {g g' : Ω} {k : ℕ}, w g ≤ δ ^ k → w g' ≤ δ ^ k →
      w (algebraMap L Ω c * g + g') ≤ δ ^ k := fun c _ _ _ hg hg' =>
    Valuation.map_add_le _ ((genCmp_val_smul_le w hL c _).trans hg) hg'
  have hle : ∀ {i j : ℕ}, i ≤ j → δ ^ i ≤ δ ^ j := fun hij => pow_le_pow_right₀ h1 hij
  have hlt : ∀ {i j : ℕ}, i < j → δ ^ i < δ ^ j := fun hij => pow_lt_pow_right₀ hδ hij
  have v5 : w (algebraMap L Ω f) ≤ 1 := by
    simpa using genCmp_val_smul_le w hL f 1
  have v4 : w (algebraMap L Ω e * x + algebraMap L Ω f) ≤ δ ^ 2 :=
    hb e hx.le (v5.trans (one_le_pow₀ h1))
  have v3 := hb d hy.le (v4.trans (hle (by norm_num : 2 ≤ 3)))
  have wx2 : w (x ^ 2) = δ ^ 4 := by rw [map_pow, hx, ← pow_mul]
  have v2 := hb c wx2.le (v3.trans (hle (by norm_num : 3 ≤ 4)))
  have wxy : w (x * y) = δ ^ 5 := by rw [map_mul, hx, hy, ← pow_add]
  have v1 := hb b wxy.le (v2.trans (hle (by norm_num : 4 ≤ 5)))
  have wx3 : w (x ^ 3) = δ ^ 6 := by rw [map_pow, hx, ← pow_mul]
  have ha : a = 0 := genCmp_coeff_eq_zero w hL h (v1.trans_lt (wx3 ▸ hlt (by norm_num)))
  rw [ha, map_zero, zero_mul, zero_add] at h
  have hb' : b = 0 := genCmp_coeff_eq_zero w hL h (v2.trans_lt (wxy ▸ hlt (by norm_num)))
  rw [hb', map_zero, zero_mul, zero_add] at h
  have hc : c = 0 := genCmp_coeff_eq_zero w hL h (v3.trans_lt (wx2 ▸ hlt (by norm_num)))
  rw [hc, map_zero, zero_mul, zero_add] at h
  have hd : d = 0 := genCmp_coeff_eq_zero w hL h (v4.trans_lt (hy ▸ hlt (by norm_num)))
  rw [hd, map_zero, zero_mul, zero_add] at h
  have he : e = 0 :=
    genCmp_coeff_eq_zero w hL h (v5.trans_lt (hx ▸ one_lt_pow₀ hδ (by norm_num)))
  rw [he, map_zero, zero_mul, zero_add] at h
  exact ⟨ha, hb', hc, hd, he, (algebraMap L Ω).injective (h.trans (map_zero _).symm)⟩

/-- **Generic comparison, algebraic core.** If `x₀ ∈ ⟨1, x⟩` and `y₀ ∈ ⟨1, x, y⟩`, then
`x₀ = u²x + r`, `y₀ = u³y + su²x + t` for some `C = (u, r, s, t)`, and `C • W₀ = W`. -/
theorem exists_variableChange_of_mem_span {δ : Γ₀} (hδ : 1 < δ) (W W₀ : WeierstrassCurve L)
    {x y x₀ y₀ : Ω} (hW : (W.baseChange Ω).toAffine.Equation x y)
    (hW₀ : (W₀.baseChange Ω).toAffine.Equation x₀ y₀) (hx : w x = δ ^ 2) (hy : w y = δ ^ 3)
    (hx₀ : w x₀ = δ ^ 2) (hy₀ : w y₀ = δ ^ 3) (h2 : x₀ ∈ Submodule.span L {1, x})
    (h3 : y₀ ∈ Submodule.span L {1, x, y}) :
    ∃ C : VariableChange L, C • W₀ = W ∧ C⁻¹ • W = W₀ ∧
      x₀ = algebraMap L Ω (↑C.u ^ 2) * x + algebraMap L Ω C.r ∧
      y₀ = algebraMap L Ω (↑C.u ^ 3) * y + algebraMap L Ω (C.s * ↑C.u ^ 2) * x +
        algebraMap L Ω C.t := by
  set φ := algebraMap L Ω
  obtain ⟨B, A, hAB⟩ := Submodule.mem_span_pair.mp h2
  obtain ⟨E, z, hz, hz'⟩ := Submodule.mem_span_insert.mp h3
  obtain ⟨D, Cc, hDC⟩ := Submodule.mem_span_pair.mp hz
  have ex₀ : x₀ = φ A * x + φ B := by
    rw [← hAB, Algebra.smul_def, Algebra.smul_def, mul_one, add_comm]
  have ey₀ : y₀ = φ Cc * y + φ D * x + φ E := by
    rw [hz', ← hDC, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, mul_one]
    ring
  have h1δ : (1 : Γ₀) ≤ δ := hδ.le
  have hA : A ≠ 0 := by
    intro hA
    rw [hA, map_zero, zero_mul, zero_add] at ex₀
    have := genCmp_val_smul_le w hL B 1
    rw [mul_one, ← ex₀, hx₀, map_one] at this
    exact (one_lt_pow₀ hδ (by norm_num : 2 ≠ 0)).not_ge this
  have hC : Cc ≠ 0 := by
    intro hC
    rw [hC, map_zero, zero_mul, zero_add] at ey₀
    have hE : w (φ E) ≤ δ ^ 2 := by
      have := genCmp_val_smul_le w hL E 1
      rw [mul_one, map_one] at this
      exact this.trans (one_le_pow₀ h1δ)
    have := Valuation.map_add_le w ((genCmp_val_smul_le w hL D x).trans hx.le) hE
    rw [← ey₀, hy₀] at this
    exact (pow_lt_pow_right₀ hδ (by norm_num : 2 < 3)).not_ge this
  rw [genCmp_equation_baseChange_iff] at hW hW₀
  -- the `x³`-coefficient: `Cc² = A³`
  have hrel := genCmp_coeffs_eq_zero w hL hδ hx hy
    (a := Cc ^ 2 - A ^ 3) (b := 2 * Cc * D + W₀.a₁ * A * Cc - Cc ^ 2 * W.a₁)
    (c := D ^ 2 + W₀.a₁ * A * D - 3 * A ^ 2 * B - W₀.a₂ * A ^ 2 + Cc ^ 2 * W.a₂)
    (d := 2 * Cc * E + W₀.a₁ * B * Cc + W₀.a₃ * Cc - Cc ^ 2 * W.a₃)
    (e := 2 * D * E + W₀.a₁ * (A * E + B * D) + W₀.a₃ * D - 3 * A * B ^ 2
      - 2 * W₀.a₂ * A * B - W₀.a₄ * A + Cc ^ 2 * W.a₄)
    (f := E ^ 2 + W₀.a₁ * B * E + W₀.a₃ * E - B ^ 3 - W₀.a₂ * B ^ 2 - W₀.a₄ * B - W₀.a₆
      + Cc ^ 2 * W.a₆) (by
      rw [ex₀, ey₀] at hW₀
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
      linear_combination hW₀ - φ Cc ^ 2 * hW)
  have hCA : Cc ^ 2 = A ^ 3 := sub_eq_zero.mp hrel.1
  set u := Cc / A with hu_def
  have hu : u ≠ 0 := div_ne_zero hC hA
  have hu2 : u ^ 2 = A := by
    rw [hu_def, div_pow, hCA]
    field_simp
  have hu3 : u ^ 3 = Cc := by
    rw [pow_succ, hu2, hu_def]
    field_simp
  let C : VariableChange L := ⟨Units.mk0 u hu, B, D / u ^ 2, E⟩
  have hCu : (↑C.u : L) = u := rfl
  have hx₀' : x₀ = φ (↑C.u ^ 2) * x + φ C.r := by rw [hCu, hu2, ex₀]
  have hy₀' : y₀ = φ (↑C.u ^ 3) * y + φ (C.s * ↑C.u ^ 2) * x + φ C.t := by
    have : C.s * ↑C.u ^ 2 = D := by
      change D / u ^ 2 * u ^ 2 = D
      exact div_mul_cancel₀ D (pow_ne_zero 2 hu)
    rw [this, hCu, hu3, ey₀]
  -- the equation of `C • W₀` at `(x, y)`
  have hW' : ((C • W₀).baseChange Ω).toAffine.Equation x y := by
    rw [WeierstrassCurve.baseChange, ← map_variableChange]
    apply genCmp_equation_smul
    change (W₀.baseChange Ω).toAffine.Equation _ _
    rw [genCmp_equation_baseChange_iff]
    convert hW₀ using 2 <;> simp only [VariableChange.map, Units.coe_map, hx₀', hy₀'] <;>
      simp only [map_mul, map_pow] <;> rfl
  rw [genCmp_equation_baseChange_iff] at hW'
  have hrel' := genCmp_coeffs_eq_zero w hL hδ hx hy (a := 0) (b := (C • W₀).a₁ - W.a₁)
    (c := -((C • W₀).a₂ - W.a₂)) (d := (C • W₀).a₃ - W.a₃) (e := -((C • W₀).a₄ - W.a₄))
    (f := -((C • W₀).a₆ - W.a₆)) (by
      simp only [map_sub, map_neg, map_zero]
      linear_combination hW' - hW)
  obtain ⟨-, h₁, h₂, h₃, h₄, h₆⟩ := hrel'
  have hCW : C • W₀ = W := WeierstrassCurve.ext (sub_eq_zero.mp h₁)
    (sub_eq_zero.mp (neg_eq_zero.mp h₂)) (sub_eq_zero.mp h₃)
    (sub_eq_zero.mp (neg_eq_zero.mp h₄)) (sub_eq_zero.mp (neg_eq_zero.mp h₆))
  exact ⟨C, hCW, by rw [← hCW, inv_smul_smul], hx₀', hy₀'⟩

/-- **Generic comparison, valuation form.** Let `S` be the functions regular away from the
origin place `w` (or all of `Ω`). If `{f ∈ S : w f ≤ δ ^ 2} = ⟨1, x⟩` and
`{f ∈ S : w f ≤ δ ^ 3} = ⟨1, x, y⟩`, then a second Weierstrass pair `(x₀, y₀)` in `S` with the
same pole orders differs from `(x, y)` by a change of variables `C`, and `C⁻¹ • W = W₀`. -/
theorem exists_variableChange_of_poleSpaces {δ : Γ₀} (hδ : 1 < δ) (W W₀ : WeierstrassCurve L)
    (S : Set Ω) {x y x₀ y₀ : Ω} (hW : (W.baseChange Ω).toAffine.Equation x y)
    (hW₀ : (W₀.baseChange Ω).toAffine.Equation x₀ y₀) (hx : w x = δ ^ 2) (hy : w y = δ ^ 3)
    (hx₀ : w x₀ = δ ^ 2) (hy₀ : w y₀ = δ ^ 3) (hx₀S : x₀ ∈ S) (hy₀S : y₀ ∈ S)
    (h2 : {f | f ∈ S ∧ w f ≤ δ ^ 2} = (Submodule.span L {1, x} : Set Ω))
    (h3 : {f | f ∈ S ∧ w f ≤ δ ^ 3} = (Submodule.span L {1, x, y} : Set Ω)) :
    ∃ C : VariableChange L, C • W₀ = W ∧ C⁻¹ • W = W₀ ∧
      x₀ = algebraMap L Ω (↑C.u ^ 2) * x + algebraMap L Ω C.r ∧
      y₀ = algebraMap L Ω (↑C.u ^ 3) * y + algebraMap L Ω (C.s * ↑C.u ^ 2) * x +
        algebraMap L Ω C.t := by
  have m2 : x₀ ∈ (Submodule.span L {1, x} : Set Ω) := h2 ▸ ⟨hx₀S, hx₀.le⟩
  have m3 : y₀ ∈ (Submodule.span L {1, x, y} : Set Ω) := h3 ▸ ⟨hy₀S, hy₀.le⟩
  exact exists_variableChange_of_mem_span w hL hδ W W₀ hW hW₀ hx hy hx₀ hy₀ m2 m3

end Valuation

end ZInQ.Contrib.CMHeight62Full
