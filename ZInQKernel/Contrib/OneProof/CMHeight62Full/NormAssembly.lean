import Mathlib

/-!
# Step 7, global assembly: from local exponent bounds to the norm inequality

For a number field `L`, a nonzero `Δ ∈ L` and a nonzero fractional ideal `J` of `𝓞_L`:

* `abs_norm_le_absNorm_pow_of_pow_le`: if `J ^ n ≤ (Δ)`, then `|N_{L/ℚ}(Δ)| ≤ N(J) ^ n`;
* `pow_le_spanSingleton_of_valuation`: if `v(a) ^ n ≤ v(Δ)` for every finite place `v` and every
  `a ∈ J` (multiplicative valuations, so this reads `n · ord_v(a) ≥ ord_v(Δ)`), then
  `J ^ n ≤ (Δ)`;
* `abs_norm_le_absNorm_pow_of_valuation`: the two together.

With `n = 12`, `Δ = Δ_W` and `J = Jη` this is the global half of the finite-place inequality
`|N_{L/ℚ}(Δ_W)| ≤ N(Jη)¹²`: it reduces that inequality to one bound per prime and per element of
`Jη`. Only Mathlib is used.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open NumberField IsDedekindDomain

variable {L : Type} [Field L] [NumberField L]

/-- If `J ^ n ≤ (Δ)` with `Δ ≠ 0` and `J ≠ 0`, then `|N_{L/ℚ}(Δ)| ≤ N(J) ^ n`. -/
theorem abs_norm_le_absNorm_pow_of_pow_le {Δ : L} (hΔ : Δ ≠ 0)
    {J : FractionalIdeal (nonZeroDivisors (𝓞 L)) L} (hJ : J ≠ 0) (n : ℕ)
    (h : J ^ n ≤ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 L)) Δ) :
    |Algebra.norm ℚ Δ| ≤ FractionalIdeal.absNorm J ^ n := by
  set S := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 L)) Δ with hSdef
  have hS : S ≠ 0 := by
    rw [hSdef, Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact hΔ
  set I := S⁻¹ * J ^ n with hIdef
  have hI : I ≤ 1 := by
    calc I = S⁻¹ * J ^ n := rfl
      _ ≤ S⁻¹ * S := mul_le_mul_right h _
      _ = 1 := inv_mul_cancel₀ hS
  have hJn : J ^ n = S * I := by
    rw [hIdef, ← mul_assoc, mul_inv_cancel₀ hS, one_mul]
  have hI0 : I ≠ 0 := by
    rw [hIdef]
    exact mul_ne_zero (inv_ne_zero hS) (pow_ne_zero n hJ)
  obtain ⟨I₀, hI₀⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hI
  have hI₀ne : I₀ ≠ ⊥ := by
    rintro rfl
    apply hI0
    rw [← hI₀]
    simp
  have hnorm : (1 : ℚ) ≤ (Ideal.absNorm I₀ : ℚ) := by
    have : Ideal.absNorm I₀ ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact hI₀ne
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  rw [← map_pow, hJn, map_mul, hSdef, FractionalIdeal.absNorm_span_singleton, ← hI₀,
    FractionalIdeal.coeIdeal_absNorm]
  calc |Algebra.norm ℚ Δ| = |Algebra.norm ℚ Δ| * 1 := (mul_one _).symm
    _ ≤ |Algebra.norm ℚ Δ| * (Ideal.absNorm I₀ : ℚ) :=
        mul_le_mul_of_nonneg_left hnorm (abs_nonneg _)

/-- The `𝓞_L`-submodule `{x : v(x) ^ n ≤ v(Δ) ^ k for every finite place v}` (`0 < n`). -/
def boundSubmodule (Δ : L) (n : ℕ) (hn : 0 < n) (k : ℕ) : Submodule (𝓞 L) L where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 L), v.valuation L x ^ n ≤ v.valuation L Δ ^ k}
  zero_mem' := by
    intro v
    simp [zero_pow hn.ne']
  add_mem' := by
    intro x y hx hy v
    have h := pow_le_pow_left₀ zero_le (Valuation.map_add (v.valuation L) x y) n
    rcases le_total (v.valuation L x) (v.valuation L y) with hxy | hxy
    · rw [max_eq_right hxy] at h
      exact h.trans (hy v)
    · rw [max_eq_left hxy] at h
      exact h.trans (hx v)
  smul_mem' := by
    intro r x hx v
    rw [Algebra.smul_def, map_mul, mul_pow]
    calc v.valuation L (algebraMap (𝓞 L) L r) ^ n * v.valuation L x ^ n
        ≤ 1 * v.valuation L x ^ n := by
          gcongr
          exact pow_le_one₀ zero_le (v.valuation_le_one r)
      _ = v.valuation L x ^ n := one_mul _
      _ ≤ v.valuation L Δ ^ k := hx v

theorem mem_boundSubmodule {Δ : L} {n : ℕ} (hn : 0 < n) {k : ℕ} {x : L} :
    x ∈ boundSubmodule Δ n hn k ↔
      ∀ v : HeightOneSpectrum (𝓞 L), v.valuation L x ^ n ≤ v.valuation L Δ ^ k :=
  Iff.rfl

theorem boundSubmodule_mul_le (Δ : L) {n : ℕ} (hn : 0 < n) (j k : ℕ) :
    boundSubmodule Δ n hn j * boundSubmodule Δ n hn k ≤ boundSubmodule Δ n hn (j + k) := by
  rw [Submodule.mul_le]
  intro x hx y hy v
  rw [map_mul, mul_pow, pow_add]
  exact mul_le_mul' (hx v) (hy v)

theorem one_le_boundSubmodule (Δ : L) {n : ℕ} (hn : 0 < n) :
    (1 : Submodule (𝓞 L) L) ≤ boundSubmodule Δ n hn 0 := by
  intro x hx v
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
  rw [pow_zero]
  exact pow_le_one₀ zero_le (v.valuation_le_one r)

theorem pow_le_boundSubmodule {Δ : L} {n : ℕ} (hn : 0 < n) {M : Submodule (𝓞 L) L}
    (hM : M ≤ boundSubmodule Δ n hn 1) (k : ℕ) : M ^ k ≤ boundSubmodule Δ n hn k := by
  induction k with
  | zero => rw [pow_zero]; exact one_le_boundSubmodule Δ hn
  | succ k ih =>
    rw [pow_succ]
    exact (mul_le_mul' ih hM).trans (boundSubmodule_mul_le Δ hn k 1)

theorem boundSubmodule_self_le {Δ : L} (hΔ : Δ ≠ 0) {n : ℕ} (hn : 0 < n) :
    boundSubmodule Δ n hn n ≤
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 L)) Δ : Submodule (𝓞 L) L) := by
  intro x hx
  have hle : ∀ v : HeightOneSpectrum (𝓞 L), v.valuation L (x / Δ) ≤ 1 := by
    intro v
    have h1 : v.valuation L x ≤ v.valuation L Δ := (pow_le_pow_iff_left₀ zero_le zero_le
      hn.ne').mp (hx v)
    have hv : v.valuation L Δ ≠ 0 := (Valuation.ne_zero_iff _).mpr hΔ
    rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr hv)]
    exact h1
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one L (x / Δ) hle
  rw [FractionalIdeal.coe_spanSingleton, Submodule.mem_span_singleton]
  refine ⟨z, ?_⟩
  rw [Algebra.smul_def, hz, div_mul_cancel₀ x hΔ]

/-- If `v(a) ^ n ≤ v(Δ)` for every finite place `v` and every `a ∈ J`, then `J ^ n ≤ (Δ)`. -/
theorem pow_le_spanSingleton_of_valuation {Δ : L} (hΔ : Δ ≠ 0)
    (J : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) {n : ℕ} (hn : 0 < n)
    (h : ∀ (v : HeightOneSpectrum (𝓞 L)) (a : L), a ∈ J →
      v.valuation L a ^ n ≤ v.valuation L Δ) :
    J ^ n ≤ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 L)) Δ := by
  rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_pow]
  have hJ : (J : Submodule (𝓞 L) L) ≤ boundSubmodule Δ n hn 1 := by
    intro a ha v
    rw [pow_one]
    exact h v a ha
  exact (pow_le_boundSubmodule hn hJ n).trans (boundSubmodule_self_le hΔ hn)

/-- **Global assembly.** Local bounds `v(a) ^ n ≤ v(Δ)` for all finite places `v` and all
`a ∈ J` give `|N_{L/ℚ}(Δ)| ≤ N(J) ^ n`. -/
theorem abs_norm_le_absNorm_pow_of_valuation {Δ : L} (hΔ : Δ ≠ 0)
    {J : FractionalIdeal (nonZeroDivisors (𝓞 L)) L} (hJ : J ≠ 0) {n : ℕ} (hn : 0 < n)
    (h : ∀ (v : HeightOneSpectrum (𝓞 L)) (a : L), a ∈ J →
      v.valuation L a ^ n ≤ v.valuation L Δ) :
    |Algebra.norm ℚ Δ| ≤ FractionalIdeal.absNorm J ^ n :=
  abs_norm_le_absNorm_pow_of_pow_le hΔ hJ n (pow_le_spanSingleton_of_valuation hΔ J hn h)

end ZInQ.Contrib.CMHeight62Full
