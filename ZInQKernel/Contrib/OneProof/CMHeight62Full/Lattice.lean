import Mathlib

/-!
# Lattice reduction along a valuation (Riemann–Roch-lite, algebraic core)

Let `w` be a valuation on a field `Ω` and `F → Ω` a field extension. A family `f : ι → Ω` is
*residually independent* if every `f i` is `w`-integral and every combination `Σ cᵢ fᵢ` with
`w`-integral coefficients `cᵢ ∈ F`, one of them a `w`-unit, is a `w`-unit. (With `κ_w` the residue
field, this says that the residues `f̄ᵢ` are linearly independent over the residue field of `F`.)

* `exists_valuation_sum_eq`: for such a family, `w(Σ cᵢ fᵢ) = maxᵢ w(cᵢ)` (Gauss-norm identity);
* `linearIndependent_of_residuallyIndependent`: the family is `F`-linearly independent, so it has at
  most `dim_F V` members inside an `F`-subspace `V`;
* `sum_integral_iff`: `Σ cᵢ fᵢ` is `w`-integral iff every `cᵢ` is, so the `w`-integral part of the
  span is the free module on `f` over the `w`-integers of `F`;
* `div_mem_integral_of_lt_one`: if `w` is discrete with uniformizer `ϖ ∈ F` and `g` is in the
  `F`-span with `w(g) < 1`, then `g / ϖ` is again `w`-integral and in the span. So the kernel of
  reduction on the lattice `V ∩ 𝒪_w` is `ϖ (V ∩ 𝒪_w)`.

These are the algebraic core of node N8 of the blueprint: the lattices `L(n·O) ∩ 𝒪_w` of the generic
pole spaces, reduced into the function field of the special fibre. Only Mathlib is used.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- Residual independence of a family with respect to a valuation `w` on `Ω`. -/
def ResiduallyIndependent (w : Valuation Ω Γ₀) {ι : Type*} [Fintype ι] (f : ι → Ω) : Prop :=
  (∀ i, w (f i) ≤ 1) ∧
    ∀ c : ι → F, (∀ i, w (algebraMap F Ω (c i)) ≤ 1) → (∃ i, w (algebraMap F Ω (c i)) = 1) →
      w (∑ i, algebraMap F Ω (c i) * f i) = 1

variable (w : Valuation Ω Γ₀) {ι : Type*} [Fintype ι] [Nonempty ι] {f : ι → Ω}

/-- **Gauss-norm identity.** For a residually independent family, `w(Σ cᵢ fᵢ)` is the largest
`w(cᵢ)`. -/
theorem exists_valuation_sum_eq (hf : ResiduallyIndependent (F := F) w f) (c : ι → F) :
    ∃ i₀, (∀ i, w (algebraMap F Ω (c i)) ≤ w (algebraMap F Ω (c i₀))) ∧
      w (∑ i, algebraMap F Ω (c i) * f i) = w (algebraMap F Ω (c i₀)) := by
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => w (algebraMap F Ω (c i))
  refine ⟨i₀, hi₀, ?_⟩
  by_cases hc : c i₀ = 0
  · have hall : ∀ i, c i = 0 := by
      intro i
      have h := hi₀ i
      rw [hc, map_zero, map_zero] at h
      have h0 : w (algebraMap F Ω (c i)) = 0 := le_antisymm h zero_le
      rwa [Valuation.zero_iff, map_eq_zero_iff _ (algebraMap F Ω).injective] at h0
    simp [hall]
  · set d := c i₀ with hd
    have hd0 : algebraMap F Ω d ≠ 0 := (map_ne_zero _).mpr hc
    have hwd : w (algebraMap F Ω d) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd0
    set c' : ι → F := fun i => c i / d with hc'
    have hle : ∀ i, w (algebraMap F Ω (c' i)) ≤ 1 := by
      intro i
      rw [hc', map_div₀, map_div₀, div_le_one₀ (zero_lt_iff.mpr hwd)]
      exact hi₀ i
    have hone : ∃ i, w (algebraMap F Ω (c' i)) = 1 :=
      ⟨i₀, by
        show w (algebraMap F Ω (c i₀ / d)) = 1
        rw [← hd, div_self hc, map_one, map_one]⟩
    have hsum : ∑ i, algebraMap F Ω (c i) * f i =
        algebraMap F Ω d * ∑ i, algebraMap F Ω (c' i) * f i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc', map_div₀, ← mul_assoc, mul_div_cancel₀ _ hd0]
    rw [hsum, map_mul, hf.2 c' hle hone, mul_one]

/-- A residually independent family is `F`-linearly independent. -/
theorem linearIndependent_of_residuallyIndependent (hf : ResiduallyIndependent (F := F) w f) :
    LinearIndependent F f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  obtain ⟨i₀, hmax, hval⟩ := exists_valuation_sum_eq w hf g
  have hsum : ∑ j, algebraMap F Ω (g j) * f j = 0 := by
    rw [← hg]
    exact Finset.sum_congr rfl fun j _ => (Algebra.smul_def (g j) (f j)).symm
  rw [hsum, map_zero] at hval
  have h := hmax i
  rw [← hval] at h
  have h0 : w (algebraMap F Ω (g i)) = 0 := le_antisymm h zero_le
  rwa [Valuation.zero_iff, map_eq_zero_iff _ (algebraMap F Ω).injective] at h0

/-- `Σ cᵢ fᵢ` is `w`-integral iff every coefficient is. -/
theorem sum_integral_iff (hf : ResiduallyIndependent (F := F) w f) (c : ι → F) :
    w (∑ i, algebraMap F Ω (c i) * f i) ≤ 1 ↔ ∀ i, w (algebraMap F Ω (c i)) ≤ 1 := by
  obtain ⟨i₀, hmax, hval⟩ := exists_valuation_sum_eq w hf c
  rw [hval]
  exact ⟨fun h i => (hmax i).trans h, fun h => h i₀⟩

omit [Nonempty ι] in
/-- **Kernel of reduction.** If every `w(g) < 1` value is at most `w(ϖ)` (discreteness, with
uniformizer `ϖ ∈ F`) and `g = Σ cᵢ fᵢ` has `w(g) < 1`, then `g / ϖ` is `w`-integral and equals
`Σ (cᵢ/ϖ) fᵢ`. -/
theorem div_mem_integral_of_lt_one {ϖ : F} (hϖ : ϖ ≠ 0)
    (hdisc : ∀ x : Ω, w x < 1 → w x ≤ w (algebraMap F Ω ϖ)) (c : ι → F)
    (hg : w (∑ i, algebraMap F Ω (c i) * f i) < 1) :
    w ((∑ i, algebraMap F Ω (c i) * f i) / algebraMap F Ω ϖ) ≤ 1 ∧
      (∑ i, algebraMap F Ω (c i) * f i) / algebraMap F Ω ϖ =
        ∑ i, algebraMap F Ω (c i / ϖ) * f i := by
  have hϖ' : algebraMap F Ω ϖ ≠ 0 := (map_ne_zero _).mpr hϖ
  have hwϖ : w (algebraMap F Ω ϖ) ≠ 0 := (Valuation.ne_zero_iff _).mpr hϖ'
  refine ⟨?_, ?_⟩
  · rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr hwϖ)]
    exact hdisc _ hg
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_div₀, div_mul_eq_mul_div]

end ZInQ.Contrib.CMHeight62Full
