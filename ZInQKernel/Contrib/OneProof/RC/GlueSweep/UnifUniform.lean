import ZInQKernel.Contrib.OneProof.RC.Uniform.UniformLowerBound
import ZInQKernel.Contrib.OneProof.RC.Uniform.BlueprintBridge
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.Bridges
import ZInQKernel.Contrib.OneProof.RC.Rings.LambdaHalfCoeff

/-!
# Lane RC22 (glue sweep), share `Unif`: lane RC16's terminal estimate and bounded denominators

Manuscript `diophantine_zq.tex` (11/5), Proposition `ex:limits-uniform-lower-bound`
(tex 4909–5205) and its consumer in Proposition `ex:limits-fixed-field-clearing` (tex 5491–5496).

Lane RC16 (`RC/Uniform/`) takes three kinds of inputs: the GLUE `ValuationOfO` (now a theorem of
lane RC20, `Rings.valuationOfO_genuine`, with RC16's Proposition restated without it as
`Rings.exLimitsUniformLowerBound_genuine`; nothing is added here), Elliot's switching steps
(the fields of `OuterSwitchProcess` and `RegularitySwitchProcess`, not proved anywhere in the tree),
and two algebraic hypotheses of its terminal and bridge lemmas that other modules now prove:

* `terminal_lower_bound_of_integralFunctional`: RC16's `terminal_lower_bound` with the hypothesis
  `hβ : v β_j ≥ −a` (gap B2-b, the exponent of the paired functional) discharged by the shared top
  layer's `PairedFunctional.functionalExponentBound_proof`, for `β_j` the generic value of an
  integral functional (exponent `a = 0`, tex 3864–3869);
  `terminalData_of_minimalModels_of_integralFunctional` does the same for RC16's
  `terminalData_of_minimalModels` (hypothesis `hβ` on `λ_j(k₀)`).
* `clearing_boundedDenominators_of_lambdaHalf`: RC16's `clearing_boundedDenominators_of_regular`
  with its hypothesis `∀ x, CoeffsInLambdaHalf (C.u x)` discharged by lane RC20's
  `Rings.coeffsInLambdaHalf_coeffHalf`, when the coordinates are those of genuine elements of
  `Λ[1/2]`.

Every theorem here is a bridge of kind `PROVED` from the hypotheses that remain.
-/

namespace ZInQ.Manuscript.RC.GlueSweep.Unif

open Filter ZInQ.Contrib.CloudB3RC53

/-- **RC16's terminal estimate with the functional exponent bound discharged** (tex 4957–4962,
gap B2-b). Lane RC16's `terminal_lower_bound` (`RC/Uniform/OuterContradiction.lean`) gives
`v u_j ≥ −a − b` on an outer-large set from the Cramer relation `u_j Δ_j = ±α_jβ_j` with `α_j`
integral, `v β_j ≥ −a` (hypothesis `hβ`), `Δ_j` integral and not outer-negligible. Here `β_j` is
the generic value `φ_j(λ_j(x_j))` of an `R_j`-linear functional `λ_j` on an integral ring `R_j`
whose image lies in the valuation ring (`hφ`): the integral representative of the paired functional
of `ex:arith-paired-functional`, whose exponent is `a = 0` (tex 3850–3869). Then `hβ` holds for
every `a`, by the shared top layer's `PairedFunctional.functionalExponentBound_proof`.
The field `K`, the index type and the rings `R_j`, modules `X_j` are taken in `Type`, as in the
discharger.

Kind: PROVED, from `hs`, `hcr` (the Cramer relation with `β_j = φ_j(λ_j(x_j))`), `hα`, `hΔint`, `hΔ`
and the integrality `hφ`. Consumer: `ZInQ.Manuscript.RC.Uniform.terminal_lower_bound`; discharger:
`ZInQ.Contrib.CloudB3RC53.PairedFunctional.functionalExponentBound_proof`. -/
theorem terminal_lower_bound_of_integralFunctional {K : Type} [Field K]
    (v : AddValuation K (WithTop ℤ)) {ι : Type} (𝒰 : Ultrafilter ι) (a : ℕ) (u α Δ s : ι → K)
    (R : ι → Type) [∀ j, CommRing (R j)] (φ : ∀ j, R j →+* K)
    (hφ : ∀ j x, (0 : WithTop ℤ) ≤ v (φ j x))
    (X : ι → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module (R j) (X j)]
    (lam : ∀ j, X j →ₗ[R j] R j) (x : ∀ j, X j)
    (hs : ∀ j, s j = 1 ∨ s j = -1)
    (hcr : ∀ᶠ j in (𝒰 : Filter ι), u j * Δ j = s j * (α j * φ j (lam j (x j))))
    (hα : ∀ᶠ j in (𝒰 : Filter ι), (0 : WithTop ℤ) ≤ v (α j))
    (hΔint : ∀ᶠ j in (𝒰 : Filter ι), (0 : WithTop ℤ) ≤ v (Δ j))
    (hΔ : ¬ Uniform.OuterNegligible v 𝒰 Δ) :
    ∃ b : ℕ, ∀ᶠ j in (𝒰 : Filter ι), (((-a - b : ℤ)) : WithTop ℤ) ≤ v (u j) :=
  Uniform.terminal_lower_bound v 𝒰 a u α (fun j => φ j (lam j (x j))) Δ s hs hcr hα
    (PairedFunctional.functionalExponentBound_proof K v ι 𝒰 R φ hφ X lam x a) hΔint hΔ

/-- **RC16's terminal Cramer data from the minimal models, with the functional exponent bound
discharged** (tex 4957–4961). Lane RC16's `terminalData_of_minimalModels`
(`RC/Uniform/UniformLowerBound.lean`) produces the `terminal` field of `OuterSwitchProcess` from the
inner minimal models; one of its hypotheses is `hβ : v λ_j(k₀) ≥ −a` for the closed functionals
`λ_j`. Here `λ_j(k₀) = φ_j(L_j(x_j))` is the value of an `R_j`-linear functional on an integral ring
(`hβint`, `hφ`; the integral representative of the paired functional, exponent `a = 0`,
tex 3850–3869), and `hβ` is discharged by `PairedFunctional.functionalExponentBound_proof`.

Kind: PROVED, from RC16's remaining hypotheses (`hz`, `hlam`, `hden`, `hΔ0`, `hα`, `hΔint`, `hΔ`)
and `hφ`, `hβint`. Consumer: `ZInQ.Manuscript.RC.Uniform.terminalData_of_minimalModels`;
discharger: `ZInQ.Contrib.CloudB3RC53.PairedFunctional.functionalExponentBound_proof`. -/
theorem terminalData_of_minimalModels_of_integralFunctional {K : Type} [Field K]
    (v : AddValuation K (WithTop ℤ)) {ι : Type} (𝒰 : Ultrafilter ι) (a n : ℕ)
    (D : ι → Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (z lam : ι → Fin (n + 1) → K) (w : ι → Fin n → Fin (n + 1) → K) (y : ι → Fin (n + 1) → K)
    (k0 j0 : Fin (n + 1))
    (hz : ∀ j, (D j).mulVec (z j) = 0) (hlam : ∀ j, Matrix.vecMul (lam j) (D j) = 0)
    (hden : ∀ j, Uniform.detCols (Uniform.colsDWY (D j) (w j) (y j)) ≠ 0)
    (hΔ0 : ∀ j, ((D j).submatrix k0.succAbove j0.succAbove).det ≠ 0)
    (hα : ∀ᶠ j in (𝒰 : Filter ι), (0 : WithTop ℤ) ≤ v (z j j0))
    (R : ι → Type) [∀ j, CommRing (R j)] (φ : ∀ j, R j →+* K)
    (hφ : ∀ j x, (0 : WithTop ℤ) ≤ v (φ j x))
    (X : ι → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module (R j) (X j)]
    (L : ∀ j, X j →ₗ[R j] R j) (x : ∀ j, X j) (hβint : ∀ j, lam j k0 = φ j (L j (x j)))
    (hΔint : ∀ᶠ j in (𝒰 : Filter ι),
      (0 : WithTop ℤ) ≤ v (((D j).submatrix k0.succAbove j0.succAbove).det))
    (hΔ : ¬ Uniform.OuterNegligible v 𝒰
      (fun j => ((D j).submatrix k0.succAbove j0.succAbove).det)) :
    ∃ (α β Δ s : ι → K), (∀ j, s j = 1 ∨ s j = -1) ∧
      (∀ᶠ j in (𝒰 : Filter ι),
        Uniform.classFunctionalCoordWith (D j) (z j) (lam j) (w j) (y j) * Δ j =
          s j * (α j * β j)) ∧
      (∀ᶠ j in (𝒰 : Filter ι), (0 : WithTop ℤ) ≤ v (α j)) ∧
      (∀ᶠ j in (𝒰 : Filter ι), (((-a : ℤ)) : WithTop ℤ) ≤ v (β j)) ∧
      (∀ᶠ j in (𝒰 : Filter ι), (0 : WithTop ℤ) ≤ v (Δ j)) ∧
      ¬ Uniform.OuterNegligible v 𝒰 Δ := by
  have hβ : ∀ᶠ j in (𝒰 : Filter ι), (((-a : ℤ)) : WithTop ℤ) ≤ v (lam j k0) := by
    have h := PairedFunctional.functionalExponentBound_proof K v ι 𝒰 R φ hφ X L x a
    filter_upwards [h] with j hj
    rw [hβint j]
    exact hj
  exact Uniform.terminalData_of_minimalModels v 𝒰 a n D z lam w y k0 j0 hz hlam hden hΔ0 hα hβ
    hΔint hΔ

/-- **RC16's bounded-denominator clause of `ClearingIdentity` for genuine `Λ[1/2]` coordinates**
(tex 5491–5496, 5719–5721; regularity from tex 4976–5195). Lane RC16's
`clearing_boundedDenominators_of_regular` (`RC/Uniform/BlueprintBridge.lean`) proves
`∃ e, ∀ x j, ‖C.u x j‖ ≤ 2^e` from the hypothesis that every coefficient sequence `C.u x` satisfies
`CoeffsInLambdaHalf`. When the coordinates are the `t`-coefficients of genuine elements
`ũ_x ∈ Λ[1/2]` (`hC`; this is the form produced by RC16's regularity and used by lane RC20's
`Rings.clearing_nodes_of_lambdaHalf`), the hypothesis is discharged by lane RC20's
`Rings.coeffsInLambdaHalf_coeffHalf`.

Kind: PROVED, from `hC`. Consumer: `ZInQ.Manuscript.RC.Uniform.clearing_boundedDenominators_of_regular`;
discharger: `ZInQ.Manuscript.RC.Rings.coeffsInLambdaHalf_coeffHalf`. -/
theorem clearing_boundedDenominators_of_lambdaHalf {b : ℕ} (C : CoordData b)
    (ũ : (Fin b → ZMod 2) → Uniform.LambdaHalf) (hC : ∀ x j, C.u x j = Rings.coeffHalf (ũ x) j) :
    ∃ e : ℕ, ∀ x j, ‖C.u x j‖ ≤ (2 : ℝ) ^ e :=
  Uniform.clearing_boundedDenominators_of_regular C fun x => by
    have hx : C.u x = Rings.coeffHalf (ũ x) := funext (hC x)
    rw [hx]
    exact Rings.coeffsInLambdaHalf_coeffHalf (ũ x)

end ZInQ.Manuscript.RC.GlueSweep.Unif
