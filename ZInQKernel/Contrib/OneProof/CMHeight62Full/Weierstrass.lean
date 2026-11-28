import Mathlib

/-!
# Step 7, Weierstrass algebra: weight 12 and the first-order change of the parameter `−x/y`

Two leaves of the finite-place inequality, over an arbitrary field with an arbitrary valuation
(Mathlib only).

* `valuation_pow_le_of_variableChange` (weight 12): if `W' = C • W` (Mathlib's change of variables
  `x = u²x' + r`, `y = u³y' + u²sx' + t`) has `v(Δ_{W'}) = 1`, then every `a` with
  `v(a · u⁻¹) ≤ 1` satisfies `v(a) ^ 12 ≤ v(Δ_W)`. Read with `a · η_W ∈ 𝒪_v · ω_{W'}` and
  `η_W = u⁻¹ ω_{W'}`, this is the local bound of the global assembly.
* `valuation_param_sub_le` (first order): at a place of a function field where `x'` and `y'` have
  poles of orders `2` and `3` (`v(x') = δ²`, `v(y') = δ³`, `1 < δ`) and with constants of valuation
  `≤ 1` (`v(u) = 1`), the parameters `z = −x/y` and `z' = −x'/y'` satisfy
  `v(z − u⁻¹ z') ≤ δ⁻²`, while `v(z') = δ⁻¹`. So `dz = u⁻¹ dz'` in `𝔪/𝔪²`: the differential
  `d(−x/y)` scales by `u⁻¹`, the companion of `Δ_{W'} = u⁻¹² Δ_W`.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Weight 12.** If `v(Δ_{C • W}) = 1` and `v(a · u⁻¹) ≤ 1`, then `v(a) ^ 12 ≤ v(Δ_W)`. -/
theorem valuation_pow_le_of_variableChange (v : Valuation F Γ₀) (W : WeierstrassCurve F)
    (C : WeierstrassCurve.VariableChange F) (h0 : v (C • W).Δ = 1) {a : F}
    (ha : v (a * ↑C.u⁻¹) ≤ 1) : v a ^ 12 ≤ v W.Δ := by
  rw [WeierstrassCurve.variableChange_Δ, map_mul, map_pow] at h0
  have hu : v (↑C.u⁻¹ : F) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact Units.ne_zero _
  have hΔ : v W.Δ = (v (↑C.u⁻¹ : F) ^ 12)⁻¹ := eq_inv_of_mul_eq_one_right h0
  have hau : v a ≤ (v (↑C.u⁻¹ : F))⁻¹ := by
    rw [map_mul] at ha
    calc v a = v a * v (↑C.u⁻¹ : F) * (v (↑C.u⁻¹ : F))⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hu, mul_one]
      _ ≤ 1 * (v (↑C.u⁻¹ : F))⁻¹ := by gcongr
      _ = (v (↑C.u⁻¹ : F))⁻¹ := one_mul _
  rw [hΔ, ← inv_pow]
  exact pow_le_pow_left₀ zero_le hau 12

/-- `v(D) = δ³` for the denominator `D = u³y' + u²sx' + t` of `−x/y`. -/
theorem valuation_denom_eq (v : Valuation F Γ₀) {δ : Γ₀} (hδ : 1 < δ) {x' y' u s t : F}
    (hx : v x' = δ ^ 2) (hy : v y' = δ ^ 3) (hu : v u = 1) (hs : v s ≤ 1) (ht : v t ≤ 1) :
    v (u ^ 3 * y' + s * u ^ 2 * x' + t) = δ ^ 3 := by
  have h1 : v (u ^ 3 * y') = δ ^ 3 := by rw [map_mul, map_pow, hu, one_pow, one_mul, hy]
  have hδ1 : (1 : Γ₀) ≤ δ := hδ.le
  have h2 : v (s * u ^ 2 * x' + t) ≤ δ ^ 2 := by
    apply Valuation.map_add_le
    · rw [map_mul, map_mul, map_pow, hu, one_pow, mul_one, hx]
      calc v s * δ ^ 2 ≤ 1 * δ ^ 2 := by gcongr
        _ = δ ^ 2 := one_mul _
    · exact ht.trans (one_le_pow₀ hδ1)
  have h3 : δ ^ 2 < δ ^ 3 := pow_lt_pow_right₀ hδ (by norm_num)
  rw [add_assoc, Valuation.map_add_eq_of_lt_left _ ((h2.trans_lt h3).trans_eq h1.symm), h1]

/-- **First order change of the parameter.** With `z = −x/y`, `x = u²x' + r`,
`y = u³y' + u²sx' + t` and `z' = −x'/y'`: `v(z − u⁻¹ z') · δ² ≤ 1`. -/
theorem valuation_param_sub_le (v : Valuation F Γ₀) {δ : Γ₀} (hδ : 1 < δ) {x' y' u r s t : F}
    (hx : v x' = δ ^ 2) (hy : v y' = δ ^ 3) (hu : v u = 1) (hr : v r ≤ 1) (hs : v s ≤ 1)
    (ht : v t ≤ 1) :
    v (-(u ^ 2 * x' + r) / (u ^ 3 * y' + s * u ^ 2 * x' + t) - u⁻¹ * (-x' / y')) * δ ^ 2 ≤ 1 := by
  have hδ0 : δ ≠ 0 := (zero_lt_one.trans hδ).ne'
  have hδ1 : (1 : Γ₀) ≤ δ := hδ.le
  have hD := valuation_denom_eq v hδ hx hy hu hs ht
  set D := u ^ 3 * y' + s * u ^ 2 * x' + t with hDdef
  have hD0 : D ≠ 0 := by
    intro h; rw [h, map_zero] at hD; exact pow_ne_zero 3 hδ0 hD.symm
  have hy0 : y' ≠ 0 := by
    intro h; rw [h, map_zero] at hy; exact pow_ne_zero 3 hδ0 hy.symm
  have hu0 : u ≠ 0 := by
    intro h; rw [h, map_zero] at hu; exact zero_ne_one hu
  set E := -(u ^ 2 * x' + r) / D - u⁻¹ * (-x' / y') with hEdef
  have hkey : E * (u * y' * D) = -(r * u * y') + s * u ^ 2 * x' ^ 2 + t * x' := by
    rw [hEdef]
    field_simp
    rw [hDdef]
    ring
  have hnum : v (-(r * u * y') + s * u ^ 2 * x' ^ 2 + t * x') ≤ δ ^ 4 := by
    apply Valuation.map_add_le
    · apply Valuation.map_add_le
      · rw [Valuation.map_neg, map_mul, map_mul, hu, mul_one, hy]
        calc v r * δ ^ 3 ≤ 1 * δ ^ 3 := by gcongr
          _ = δ ^ 3 := one_mul _
          _ ≤ δ ^ 4 := pow_le_pow_right₀ hδ1 (by norm_num)
      · rw [map_mul, map_mul, map_pow, map_pow, hu, one_pow, mul_one, hx, ← pow_mul]
        calc v s * δ ^ (2 * 2) ≤ 1 * δ ^ (2 * 2) := by gcongr
          _ = δ ^ 4 := by rw [one_mul]
    · rw [map_mul, hx]
      calc v t * δ ^ 2 ≤ 1 * δ ^ 2 := by gcongr
        _ = δ ^ 2 := one_mul _
        _ ≤ δ ^ 4 := pow_le_pow_right₀ hδ1 (by norm_num)
  have hden : v (u * y' * D) = δ ^ 6 := by
    rw [map_mul, map_mul, hu, one_mul, hy, hD, ← pow_add]
  have h6 : v E * δ ^ 6 ≤ δ ^ 4 := by
    rw [← hden, ← map_mul, hkey]
    exact hnum
  have h4 : (0 : Γ₀) < δ ^ 4 := zero_lt_iff.mpr (pow_ne_zero 4 hδ0)
  have h6' : v E * δ ^ 2 * δ ^ 4 ≤ 1 * δ ^ 4 := by
    rw [mul_assoc, ← pow_add, one_mul]
    exact h6
  exact le_of_mul_le_mul_right h6' h4

/-- The parameter `z' = −x'/y'` has `v(z') = δ⁻¹`. -/
theorem valuation_param_eq (v : Valuation F Γ₀) {δ : Γ₀} (hδ0 : δ ≠ 0) {x' y' : F}
    (hx : v x' = δ ^ 2) (hy : v y' = δ ^ 3) : v (-x' / y') = δ⁻¹ := by
  rw [map_div₀, Valuation.map_neg, hx, hy, show δ ^ 3 = δ ^ 2 * δ from pow_succ δ 2, ← div_div,
    div_self (pow_ne_zero 2 hδ0), one_div]

end ZInQ.Contrib.CMHeight62Full
