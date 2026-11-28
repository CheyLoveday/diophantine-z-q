import ZInQKernel.Contrib.OneProof.CMHeight62Full.NormAssembly
import ZInQKernel.Contrib.OneProof.CMHeight62Full.Weierstrass

/-!
# Step 7 reduced to one local model per prime

`abs_norm_le_absNorm_pow_twelve_of_models`: let `W` be a Weierstrass curve over a number field
`L` with `Δ_W ≠ 0` and `J` a nonzero fractional ideal. Suppose that at every finite place `v`
there is a change of variables `C_v` (over `L`) with `v(Δ_{C_v • W}) = 1` such that
`v(a · u_v⁻¹) ≤ 1` for every `a ∈ J`. Then `|N_{L/ℚ}(Δ_W)| ≤ N(J)¹²`.

`abs_norm_algebraMap_le_of_models` is the same statement for `W` over a subfield `K`, in the
shape `|N_{L/ℚ}(algebraMap K L Δ_W)| ≤ N(J)¹²` of the finite-place inequality.

For the finite-place inequality, `W` is the short model of the elliptic curve, `J = Jη`
(`a · η_W ∈ ω_𝒢`), `C_v • W` is a `v`-integral model with unit discriminant, and the hypothesis
`v(a · u_v⁻¹) ≤ 1` is `(ω_𝒢)_v ⊆ 𝒪_v · ω_{C_v • W}` together with `η_W = u_v⁻¹ · ω_{C_v • W}`
(`valuation_param_sub_le`). Those two geometric inputs are the open part.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open NumberField IsDedekindDomain

variable {L : Type} [Field L] [NumberField L]

/-- **Step 7 from local unit-discriminant models.** -/
theorem abs_norm_le_absNorm_pow_twelve_of_models (W : WeierstrassCurve L) (hΔ : W.Δ ≠ 0)
    {J : FractionalIdeal (nonZeroDivisors (𝓞 L)) L} (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 L), ∃ C : WeierstrassCurve.VariableChange L,
      v.valuation L (C • W).Δ = 1 ∧ ∀ a ∈ J, v.valuation L (a * ↑C.u⁻¹) ≤ 1) :
    |Algebra.norm ℚ W.Δ| ≤ FractionalIdeal.absNorm J ^ 12 := by
  refine abs_norm_le_absNorm_pow_of_valuation hΔ hJ (by norm_num) ?_
  intro v a ha
  obtain ⟨C, hC, hJC⟩ := h v
  exact valuation_pow_le_of_variableChange (v.valuation L) W C hC (hJC a ha)

/-- **Step 7 from local unit-discriminant models**, for `W` defined over a subfield `K`. -/
theorem abs_norm_algebraMap_le_of_models {K : Type} [Field K] [Algebra K L]
    (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0)
    {J : FractionalIdeal (nonZeroDivisors (𝓞 L)) L} (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 L), ∃ C : WeierstrassCurve.VariableChange L,
      v.valuation L (C • W.map (algebraMap K L)).Δ = 1 ∧
        ∀ a ∈ J, v.valuation L (a * ↑C.u⁻¹) ≤ 1) :
    |Algebra.norm ℚ (algebraMap K L W.Δ)| ≤ FractionalIdeal.absNorm J ^ 12 := by
  have hΔ' : (W.map (algebraMap K L)).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]
    exact (map_ne_zero (algebraMap K L)).mpr hΔ
  have := abs_norm_le_absNorm_pow_twelve_of_models (W.map (algebraMap K L)) hΔ' hJ h
  rwa [WeierstrassCurve.map_Δ] at this

end ZInQ.Contrib.CMHeight62Full
