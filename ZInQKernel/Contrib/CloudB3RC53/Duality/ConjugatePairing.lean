import Mathlib

/-!
# Duality area: the conjugate pairing `τ*M_i ≃ M_i*(1)` (abstract core)

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`, tex L2761–2830, paragraph
"The dual coefficient system" (tex L2779–2805).

Fix an involution `τ` (an actual complex conjugation, `τ² = 1`) of a group `Γ` (`G_ℚ`), a
subgroup `H` normalized by `τ` (`G_K`), a commutative coefficient ring `R` (`A_i` or `A_i[G]`) and
an `R`-module `M₀` (`T₂E ⊗ R`) with an `R`-linear `Γ`-action and an equivariant bilinear pairing
`e : M₀ × M₀ → L` into an `R`-module `L` with a `Γ`-action (`R(1)`, the Weil pairing `e₂`
extended `R`-bilinearly: `e₂(σ v, σ w) = σ e₂(v, w)`). Twist by a character `α : H → Rˣ`
(`α = χ_h Ψ_i` or `χ₀ ε Ψ_i`) with `α(τ σ τ⁻¹) = α(σ)⁻¹`: `M = M₀(α)` has `σ ⋆ v = α(σ) σ v`, and
the pullback `τ*M` has `σ ⋆_τ w = α(τστ⁻¹) (τστ⁻¹) w`.

* `conjPairing_equivariant`: `P(v, w) = e(v, ρ(τ) w)` is `H`-equivariant from `M ⊗_R τ*M` to
  `L`: `P(σ ⋆ v, σ ⋆_τ w) = σ P(v, w)` (tex L2797–2803: "`ρ_T(τ)² = 1`, the two scalar
  characters multiply to one, and `e₂` transforms by the cyclotomic character").
* `conjPairing_perfect`: if `e` is perfect (both adjoints bijective) so is `P`; together with
  equivariance this is the `R`-linear identification `τ*M ≃ M*(1) = Hom_R(M, R(1))`.
* `conj_inv_of_rational_quadratic`, `conj_inv_mul`: the inversion `α^τ = α⁻¹` of
  `α = χ_h Ψ_i` (resp. `χ₀ ε Ψ_i`) from `Ψ_i^τ = Ψ_i⁻¹` and the rational quadratic factors
  (tex L2792–2796).

**Classification.** `ConjugatePairingNode` is PROVED (`conjugatePairingNode_proof`). The
hypothesis `Ψ(τ g τ⁻¹) = Ψ(g)⁻¹` ("conjugation acts on this ring-class group by inversion",
tex L2786–2788) is an input of the node (the ring-class field statement is classical and is not
proved by Elliot either).
-/

namespace ZInQ.Contrib.CloudB3RC53.Duality

section Abstract

variable {Γ : Type*} [Group Γ] {R : Type*} [CommRing R]
  {M L : Type*} [AddCommGroup M] [Module R M] [AddCommGroup L] [Module R L]

/-- The pairing `P(v, w) = e(v, ρ(τ) w)` of tex L2797–2799. -/
def conjPairing (act : Γ →* Module.End R M) (e : M →ₗ[R] M →ₗ[R] L) (τ : Γ) :
    M →ₗ[R] M →ₗ[R] L :=
  e.compl₂ (act τ)

/-- **The conjugate pairing is `H`-equivariant** (tex L2797–2803). -/
theorem conjPairing_equivariant (act : Γ →* Module.End R M) (actL : Γ →* Module.End R L)
    (e : M →ₗ[R] M →ₗ[R] L) (he : ∀ σ v w, e (act σ v) (act σ w) = actL σ (e v w))
    (H : Subgroup Γ) (τ : Γ) (hτ : τ * τ = 1) (hH : ∀ σ ∈ H, τ * σ * τ⁻¹ ∈ H)
    (α : H →* Rˣ) (hα : ∀ (σ : Γ) (hσ : σ ∈ H), α ⟨τ * σ * τ⁻¹, hH σ hσ⟩ = (α ⟨σ, hσ⟩)⁻¹)
    (σ : Γ) (hσ : σ ∈ H) (v w : M) :
    conjPairing act e τ (((α ⟨σ, hσ⟩ : Rˣ) : R) • act σ v)
        (((α ⟨τ * σ * τ⁻¹, hH σ hσ⟩ : Rˣ) : R) • act (τ * σ * τ⁻¹) w) =
      actL σ (conjPairing act e τ v w) := by
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hcomp : act τ (act (τ * σ * τ⁻¹) w) = act σ (act τ w) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hτinv]
    congr 2
    calc τ * (τ * σ * τ) = (τ * τ) * σ * τ := by group
      _ = σ * τ := by rw [hτ, one_mul]
  simp only [conjPairing, LinearMap.compl₂_apply, map_smul, LinearMap.smul_apply, hcomp,
    he, smul_smul]
  rw [hα σ hσ, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

/-- The precomposition map `f ↦ f ∘ g` on `Hom_R(M, L)`. -/
theorem bijective_precomp_of_involution (g : M →ₗ[R] M) (hg : g ∘ₗ g = LinearMap.id) :
    Function.Bijective (fun f : M →ₗ[R] L => f ∘ₗ g) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun f => f ∘ₗ g, fun f => ?_, fun f => ?_⟩ <;>
    simp [LinearMap.comp_assoc, hg]

/-- **The conjugate pairing is perfect** when `e` is: `ρ(τ)` is an involution. -/
theorem conjPairing_perfect (act : Γ →* Module.End R M) (e : M →ₗ[R] M →ₗ[R] L) (τ : Γ)
    (hτ : τ * τ = 1) (he₁ : Function.Bijective e) (he₂ : Function.Bijective e.flip) :
    Function.Bijective (conjPairing act e τ) ∧ Function.Bijective (conjPairing act e τ).flip := by
  have hinv : act τ ∘ₗ act τ = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, hτ, map_one]; rfl
  constructor
  · have : (conjPairing act e τ : M → M →ₗ[R] L) = (fun f => f ∘ₗ act τ) ∘ e := by
      funext v; rfl
    rw [this]
    exact (bijective_precomp_of_involution _ hinv).comp he₁
  · have : ((conjPairing act e τ).flip : M → M →ₗ[R] L) = e.flip ∘ act τ := by
      funext w; rfl
    rw [this]
    refine he₂.comp ?_
    refine Function.bijective_iff_has_inverse.mpr ⟨act τ, fun x => ?_, fun x => ?_⟩ <;>
      simpa using congrArg (fun f : M →ₗ[R] M => f x) hinv

end Abstract

section Characters

variable {Γ : Type*} [Group Γ] {R : Type*} [CommRing R]

/-- A character of `Γ = G_ℚ` with values in `Rˣ` (a rational character restricted to `G_K`, such
as `χ_h` or the universal `ε`) is invariant under conjugation by `τ`; if it is quadratic it is
also its own inverse, so `χ^τ = χ = χ⁻¹` (tex L2792–2795). -/
theorem conj_inv_of_rational_quadratic (χ : Γ →* Rˣ) (hχ : ∀ g, χ g * χ g = 1) (τ g : Γ) :
    χ (τ * g * τ⁻¹) = (χ g)⁻¹ := by
  rw [map_mul, map_mul, map_inv, mul_comm (χ τ), mul_assoc, mul_inv_cancel, mul_one]
  exact eq_inv_of_mul_eq_one_left (hχ g)

/-- Products of characters inverted by conjugation are inverted by conjugation (tex L2794–2796:
`α^τ = α⁻¹` for `α = χ_h Ψ_i`, `χ₀ ε Ψ_i`). -/
theorem conj_inv_mul (H : Subgroup Γ) (τ : Γ) (hH : ∀ σ ∈ H, τ * σ * τ⁻¹ ∈ H)
    (α β : H →* Rˣ)
    (hα : ∀ (σ : Γ) (hσ : σ ∈ H), α ⟨τ * σ * τ⁻¹, hH σ hσ⟩ = (α ⟨σ, hσ⟩)⁻¹)
    (hβ : ∀ (σ : Γ) (hσ : σ ∈ H), β ⟨τ * σ * τ⁻¹, hH σ hσ⟩ = (β ⟨σ, hσ⟩)⁻¹)
    (σ : Γ) (hσ : σ ∈ H) :
    (α * β) ⟨τ * σ * τ⁻¹, hH σ hσ⟩ = ((α * β) ⟨σ, hσ⟩)⁻¹ := by
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, hα σ hσ, hβ σ hσ, mul_inv]

end Characters

/-- **The conjugate pairing (abstract core of `ex:arith-conjugate-duality`, tex L2779–2805).**
For an `R`-linear action `act` of `Γ` on `M₀`, an action `actL` on `L`, an equivariant
`R`-bilinear `e : M₀ × M₀ → L`, an involution `τ` normalizing `H ≤ Γ`, and characters
`α = α₁ α₂` of `H` with `α₁` inverted by `τ`-conjugation (`Ψ_i`) and `α₂` the restriction of a
quadratic character `χ` of `Γ` (`χ_h`, resp. `χ₀ ε`): the pairing `P(v, w) = e(v, ρ(τ) w)`
satisfies `P(α(σ) σ v, α(τστ⁻¹) (τστ⁻¹) w) = σ P(v, w)` for `σ ∈ H` (an `H`-equivariant pairing
`M₀(α) ⊗ τ*M₀(α) → L`), and `P` is perfect whenever `e` is. -/
def ConjugatePairingNode : Prop :=
  ∀ (Γ : Type) [Group Γ] (R : Type) [CommRing R] (M L : Type) [AddCommGroup M] [Module R M]
    [AddCommGroup L] [Module R L] (act : Γ →* Module.End R M) (actL : Γ →* Module.End R L)
    (e : M →ₗ[R] M →ₗ[R] L), (∀ σ v w, e (act σ v) (act σ w) = actL σ (e v w)) →
    ∀ (H : Subgroup Γ) (τ : Γ), τ * τ = 1 → ∀ (hH : ∀ σ ∈ H, τ * σ * τ⁻¹ ∈ H)
      (α₁ : H →* Rˣ) (χ : Γ →* Rˣ),
      (∀ (σ : Γ) (hσ : σ ∈ H), α₁ ⟨τ * σ * τ⁻¹, hH σ hσ⟩ = (α₁ ⟨σ, hσ⟩)⁻¹) →
      (∀ g, χ g * χ g = 1) →
      let α : H →* Rˣ := α₁ * χ.comp H.subtype
      (∀ (σ : Γ) (hσ : σ ∈ H) (v w : M),
        conjPairing act e τ (((α ⟨σ, hσ⟩ : Rˣ) : R) • act σ v)
          (((α ⟨τ * σ * τ⁻¹, hH σ hσ⟩ : Rˣ) : R) • act (τ * σ * τ⁻¹) w) =
        actL σ (conjPairing act e τ v w)) ∧
      (Function.Bijective e → Function.Bijective e.flip →
        Function.Bijective (conjPairing act e τ) ∧
          Function.Bijective (conjPairing act e τ).flip)

theorem conjugatePairingNode_proof : ConjugatePairingNode := by
  intro Γ _ R _ M L _ _ _ _ act actL e he H τ hτ hH α₁ χ hα₁ hχ
  refine ⟨fun σ hσ v w => ?_, fun h₁ h₂ => conjPairing_perfect act e τ hτ h₁ h₂⟩
  refine conjPairing_equivariant act actL e he H τ hτ hH _ (fun σ' hσ' => ?_) σ hσ v w
  refine conj_inv_mul H τ hH α₁ (χ.comp H.subtype) hα₁ (fun σ'' hσ'' => ?_) σ' hσ'
  exact conj_inv_of_rational_quadratic χ hχ τ σ''

end ZInQ.Contrib.CloudB3RC53.Duality
