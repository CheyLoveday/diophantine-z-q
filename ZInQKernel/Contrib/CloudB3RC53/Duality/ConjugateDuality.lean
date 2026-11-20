import ZInQKernel.Contrib.CloudB3RC53.Duality.BaseChangePerfect
import ZInQKernel.Contrib.CloudB3RC53.Duality.WeilPerfect
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure

/-!
# Duality area: `τ*M_i ≃ M_i*(1)` — the conjugate pairing is perfect over `R`

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality`, tex L2761–2805. This file
removes the perfectness hypothesis of `ConjugateWeilPairingNode`:

* `torsionCoeff_addEquiv_prod`: `E[m] ≃ (ℤ/m)²` (from the vendored torsion structure theorem
  over the separable closure);
* `weilBaseChange_perfect`: the `R`-bilinear Weil pairing `(R ⊗ E[m])² → R ⊗ μ_m` is perfect for
  every commutative ring `R` (`weilPairing_perfect`, `pairingBaseChange_perfect`);
* `ConjugateDualityNode` (PROVED): the pairing `(v, w) ↦ e_m(v, ρ(τ) w)` is an `H`-equivariant
  perfect `R`-bilinear pairing `M(α) ⊗_R τ*M(α) → R(1)`; in particular `w ↦ P(·, w)` is an
  `R`-linear bijection `τ*M ≃ Hom_R(M, R(1)) = M*(1)` intertwining the `H`-actions.

This is the coefficient part of the lemma ("Pullback of the Galois action gives an `R_i`-linear
identification `τ*M_i ≃ M_i*(1)` through `(v, w) ↦ e₂(v, ρ_T(τ) w)`; it fixes `t` and the
group-ring basis"). The Selmer-complex part
(`C_U(M_i) ≃ RHom_{R_i}(C_{U⊥}(M_i*(1)), R_i)[-3]`, tex L2763–2768, L2825–2829) needs Selmer
complexes, which are not available (see the lane notes): STATED-DEFS.
-/

namespace ZInQ.Contrib.CloudB3RC53.Duality

open TauCeti TensorProduct

section

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] (m : ℕ)
  (hm : IsUnit (m : K))

include hm in
/-- `E(Kˢ)[m] ≃ (ℤ/m)²` for `m` invertible in `K` (from the vendored basis theorem for the torsion
over a separably closed field). -/
theorem torsionCoeff_addEquiv_prod [NeZero m] :
    Nonempty (W.TorsionCoeff m ≃+ ZMod m × ZMod m) := by
  have hm' : (m : SeparableClosure K) ≠ 0 := hm.natCast_ne_zero_of_algebra
  let : DecidableEq (AlgebraicClosure K) := fun a b => Classical.propDecidable (a = b)
  obtain ⟨b⟩ := (W.baseChange (SeparableClosure K)).nonempty_basis_torsionBy m hm'
  exact ⟨(AddEquiv.torsionByCongr W.pointCoeffEquiv m).symm.trans
    (b.equivFun.toAddEquiv.trans (LinearEquiv.piFinTwo (ZMod m) (fun _ => ZMod m)).toAddEquiv)⟩

/-- **The `R`-bilinear Weil pairing is perfect.** -/
theorem weilBaseChange_perfect (R : Type*) [CommRing R] :
    Function.Bijective (weilBaseChange W m hm R) ∧
      Function.Bijective (weilBaseChange W m hm R).flip := by
  have : NeZero (m : K) := ⟨hm.ne_zero⟩
  have : NeZero m := NeZero.of_neZero_natCast K
  obtain ⟨φ⟩ := torsionCoeff_addEquiv_prod W m hm
  obtain ⟨he, he'⟩ := weilPairing_perfect W m hm
  exact pairingBaseChange_perfect φ (kummerCoeffAddEquivZMod hm) _ he he' R

end

/-- **Conjugate coefficients and the conjugate duality of coefficients**
(`ex:arith-conjugate-duality`, tex L2761–2805). For an elliptic curve `W` over a field `K`
(`E/ℚ`), `m` invertible in `K` (`m = 2^i`), a commutative coefficient ring `R` (`A_i`, `A_i[G]`),
an involution `τ` of `G_K` (an actual complex conjugation) normalizing a subgroup `H` (`G_K` of
the imaginary quadratic field), a character `Ψ : H → Rˣ` with `Ψ(τστ⁻¹) = Ψ(σ)⁻¹` (`Ψ_i`:
conjugation acts by inversion on the ring-class group) and a quadratic character `χ` of the whole
group (`χ_h`, resp. `χ₀ ε`), put `α = Ψ · χ|_H`, `M = (R ⊗ E[m])(α)` and
`P(v, w) = e_m(v, ρ(τ) w) ∈ R ⊗ μ_m = R(1)`. Then
1. `P(α(σ) σ v, α(τστ⁻¹) (τστ⁻¹) w) = σ P(v, w)` for `σ ∈ H` (`P : M ⊗_R τ*M → R(1)` is
   `H`-equivariant), and
2. `P` is perfect: `v ↦ P(v, ·)` and `w ↦ P(·, w)` are bijective, so `τ*M ≃ M*(1)`. -/
def ConjugateDualityNode : Prop :=
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
      Function.Bijective (conjPairing act (weilBaseChange W m hm R) τ) ∧
        Function.Bijective (conjPairing act (weilBaseChange W m hm R) τ).flip

theorem conjugateDualityNode_proof : ConjugateDualityNode := by
  intro K _ W _ m hm R _ H τ hτ hH Ψ χ hΨ hχ
  obtain ⟨h1, h2⟩ := conjugateWeilPairingNode_proof K W m hm R H τ hτ hH Ψ χ hΨ hχ
  obtain ⟨hp1, hp2⟩ := weilBaseChange_perfect W m hm R
  exact ⟨h1, h2 hp1 hp2⟩

end ZInQ.Contrib.CloudB3RC53.Duality
