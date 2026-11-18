import ZInQKernel.Contrib.CloudB3RC53.Duality.ConjugatePairing
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing

/-!
# Duality area: the conjugate pairing on `M_i = E[2^i] ⊗ R` through the Weil pairing

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`, tex L2761–2805: the
`R_i`-linear perfect pairing
```
M_i ⊗_{R_i} τ*M_i → R_i(1),   (v, w) ↦ e₂(v, ρ_T(τ) w),
```
for `M_i = (T₂E ⊗ A_i)(α)` and `R_i = A_i` or `A_i[G]`. Here the untwisted module is
`R ⊗_ℤ E[m]` with `m = 2^i` (`T₂E ⊗ A_i = E[2^i] ⊗ A_i` since `2^i A_i = 0`), with `G_K` acting
through `E[m]` (`WeierstrassCurve.TorsionCoeff`), and `R(1) = R ⊗_ℤ μ_m`
(`TauCeti.KummerCoeff`). The pairing `e₂` is the genuine Weil pairing
`WeierstrassCurve.torsionCoeffWeilPairing`, extended `R`-bilinearly (`weilBaseChange`).

* `torsionAct`, `kummerAct`: the `R`-linear Galois actions on `R ⊗ E[m]` and `R ⊗ μ_m`;
* `weilBaseChange_equivariant`: `e₂(σ v, σ w) = σ e₂(v, w)` after base change;
* `ConjugateWeilPairingNode` (PROVED): for an involution `τ` normalizing a subgroup `H` of the
  absolute Galois group and a twisting character `α = Ψ · χ` with `Ψ^τ = Ψ⁻¹` and `χ` the
  restriction of a quadratic character, the pairing `(v, w) ↦ e₂(v, ρ(τ) w)` is an `H`-equivariant
  pairing `M ⊗_R τ*M → R(1)`; it is perfect when the base-changed Weil pairing is.

**Classification.** PROVED (from the genuine Weil pairing). The perfectness of the base change of
`e₂` to `R` (from `E[m] ≅ (ℤ/m)²` and perfectness of `e_m`) is kept as the hypothesis of the
perfectness clause: OPEN (not needed for equivariance).
-/

namespace ZInQ.Contrib.CloudB3RC53.Duality

open TauCeti TensorProduct

section BaseChange

variable {Γ : Type*} [Group Γ] (R : Type*) [CommRing R] (T : Type*) [AddCommGroup T]
  [DistribMulAction Γ T]

/-- The `R`-linear action of `Γ` on `R ⊗_ℤ T` induced by its action on `T`. -/
noncomputable def baseChangeAct : Γ →* Module.End R (R ⊗[ℤ] T) :=
  (Module.End.baseChangeHom ℤ R T).toMonoidHom.comp
    ((addMonoidEndRingEquivInt T).toMonoidHom.comp (DistribMulAction.toAddMonoidEnd Γ T))

@[simp]
theorem baseChangeAct_tmul (σ : Γ) (r : R) (t : T) :
    baseChangeAct R T σ (r ⊗ₜ t) = r ⊗ₜ (σ • t) :=
  rfl

variable {R T} {μ : Type*} [AddCommGroup μ] [DistribMulAction Γ μ]

/-- An additive pairing as a `ℤ`-bilinear map. -/
def toIntBilin (e : T →+ T →+ μ) : T →ₗ[ℤ] T →ₗ[ℤ] μ :=
  (addMonoidHomLequivInt ℤ).toLinearMap ∘ₗ e.toIntLinearMap

/-- The `R`-bilinear extension of an additive pairing `T × T → μ` to `R ⊗ T`. -/
noncomputable def pairingBaseChange (e : T →+ T →+ μ) :
    R ⊗[ℤ] T →ₗ[R] R ⊗[ℤ] T →ₗ[R] R ⊗[ℤ] μ :=
  LinearMap.BilinMap.baseChange R (toIntBilin e)

@[simp]
theorem pairingBaseChange_tmul (e : T →+ T →+ μ) (r r' : R) (t t' : T) :
    pairingBaseChange e (r ⊗ₜ t) (r' ⊗ₜ t') = (r * r') ⊗ₜ e t t' :=
  rfl

/-- An equivariant pairing stays equivariant after base change. -/
theorem pairingBaseChange_equivariant (e : T →+ T →+ μ)
    (he : ∀ (σ : Γ) (t t' : T), e (σ • t) (σ • t') = σ • e t t') (σ : Γ)
    (v w : R ⊗[ℤ] T) :
    pairingBaseChange e (baseChangeAct R T σ v) (baseChangeAct R T σ w) =
      baseChangeAct R μ σ (pairingBaseChange e v w) := by
  induction v using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul r t =>
    induction w using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r' t' => simp [he]

end BaseChange

section Weil

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] (m : ℕ)
  (hm : IsUnit (m : K)) (R : Type*) [CommRing R]

/-- The Weil pairing `e_m` extended `R`-bilinearly:
`(R ⊗ E[m]) × (R ⊗ E[m]) → R ⊗ μ_m = R(1)`. -/
noncomputable def weilBaseChange :
    R ⊗[ℤ] W.TorsionCoeff m →ₗ[R] R ⊗[ℤ] W.TorsionCoeff m →ₗ[R] R ⊗[ℤ] KummerCoeff K m :=
  pairingBaseChange (W.torsionCoeffWeilPairing m hm)

theorem weilBaseChange_equivariant (σ : AbsoluteGaloisGroup K)
    (v w : R ⊗[ℤ] W.TorsionCoeff m) :
    weilBaseChange W m hm R (baseChangeAct R _ σ v) (baseChangeAct R _ σ w) =
      baseChangeAct R _ σ (weilBaseChange W m hm R v w) :=
  pairingBaseChange_equivariant _ (fun σ P Q => W.torsionCoeffWeilPairing_smul m hm σ P Q) σ v w

end Weil

/-- **The conjugate pairing through the Weil pairing** (`ex:arith-conjugate-duality`, tex
L2779–2805). Let `W` be an elliptic curve over a field `K` (for the manuscript `K = ℚ`, with `G_ℚ`
acting on `E[2^i]`), `m` invertible in `K`, `R` a commutative coefficient ring, `τ` an involution
of `G_K` (an actual complex conjugation) normalizing a subgroup `H` (`G_K` for the imaginary
quadratic field), `Ψ : H → Rˣ` inverted by `τ`-conjugation and `χ` a quadratic character of the
whole group (`χ_h`, resp. `χ₀ ε`). For `α = Ψ · χ|_H`, the pairing
`P(v, w) = e_m(v, ρ(τ) w)` on `R ⊗ E[m]` with values in `R ⊗ μ_m = R(1)` satisfies
`P(α(σ) σ v, α(τστ⁻¹) (τστ⁻¹) w) = σ P(v, w)` for all `σ ∈ H`: it is an `H`-equivariant
`R`-bilinear pairing `M(α) ⊗_R τ*M(α) → R(1)`, which fixes `R` (in particular `t` and the
group-ring basis); and it is perfect whenever the `R`-bilinear Weil pairing is. -/
def ConjugateWeilPairingNode : Prop :=
  ∀ (K : Type) [Field K] (W : WeierstrassCurve K) [W.IsElliptic] (m : ℕ) (hm : IsUnit (m : K))
    (R : Type) [CommRing R] (H : Subgroup (AbsoluteGaloisGroup K)) (τ : AbsoluteGaloisGroup K),
    τ * τ = 1 → ∀ (hH : ∀ σ ∈ H, τ * σ * τ⁻¹ ∈ H) (Ψ : H →* Rˣ) (χ : AbsoluteGaloisGroup K →* Rˣ),
      (∀ (σ : AbsoluteGaloisGroup K) (hσ : σ ∈ H), Ψ ⟨τ * σ * τ⁻¹, hH σ hσ⟩ = (Ψ ⟨σ, hσ⟩)⁻¹) →
      (∀ g, χ g * χ g = 1) →
      let α : H →* Rˣ := Ψ * χ.comp H.subtype
      let act := baseChangeAct (Γ := AbsoluteGaloisGroup K) R (W.TorsionCoeff m)
      (∀ (σ : AbsoluteGaloisGroup K) (hσ : σ ∈ H) (v w : R ⊗[ℤ] W.TorsionCoeff m),
        conjPairing act (weilBaseChange W m hm R) τ (((α ⟨σ, hσ⟩ : Rˣ) : R) • act σ v)
          (((α ⟨τ * σ * τ⁻¹, hH σ hσ⟩ : Rˣ) : R) • act (τ * σ * τ⁻¹) w) =
        baseChangeAct R (KummerCoeff K m) σ (conjPairing act (weilBaseChange W m hm R) τ v w)) ∧
      (Function.Bijective (weilBaseChange W m hm R) →
        Function.Bijective (weilBaseChange W m hm R).flip →
        Function.Bijective (conjPairing act (weilBaseChange W m hm R) τ) ∧
          Function.Bijective (conjPairing act (weilBaseChange W m hm R) τ).flip)

theorem conjugateWeilPairingNode_proof : ConjugateWeilPairingNode := by
  intro K _ W _ m hm R _ H τ hτ hH Ψ χ hΨ hχ
  exact conjugatePairingNode_proof (AbsoluteGaloisGroup K) R _ _
    (baseChangeAct R (W.TorsionCoeff m)) (baseChangeAct R (KummerCoeff K m))
    (weilBaseChange W m hm R) (weilBaseChange_equivariant W m hm R) H τ hτ hH Ψ χ hΨ hχ

end ZInQ.Contrib.CloudB3RC53.Duality
