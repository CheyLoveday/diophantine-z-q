import ZInQKernel.Contrib.CloudB3RC53.NewformS13.FunctionFieldPullback
import ZInQKernel.Contrib.RC53Assist.NewformPeriodsG1.ParametrizationPeriods

/-!
# The analytic normalization `dq/q = 2πi dτ`

Under `q = e^{2πiτ}`, a differential `h(q) · dq/q` is `2πi · h(e^{2πiτ}) · dτ`. For the
`q`-expansion of differentials `qExpDiff` of `QExpDifferential.lean` this reads as follows
(with the peer's convergent expansions `HasQExpansionAbove` and its termwise derivative
`HasQExpansionAbove.hasDerivAt`, `NewformPeriodsG1/ParametrizationPeriods.lean`):

* `qExpDiff_D_analytic`: if `f ∈ F = ℚ(j, j_M)` is the expansion of `H` above height `R`, then the
  `q`-expansion of `df` is the expansion of `(2πi)⁻¹ H'`, i.e. `df = H'(τ) dτ = (2πi)⁻¹ H' · dq/q`;
* **`pullback_omegaA_analytic`**: if the pull-back of `ω_A` along a modular point `(x, y)`
  has `q`-expansion `c · ĝ` (clause (iv), `PullbackIsMultiple A x y ĝ c`), and `x`, `y`, `ĝ` are
  the expansions of `X`, `Y`, `G` above height `R`, then
  `X'(τ) = 2πi · c · G(τ) · (2Y(τ) + a₁X(τ) + a₃)` above `R`: the pull-back of
  `ω_A = dX/(2Y + a₁X + a₃)` is `2πi · c · G(τ) dτ`, the period model `ω_g = 2πi g(τ) dτ`;
* `pullback_omegaA_cuspForm`: the same for a cusp form `g` on `Γ₀(M)` with `ĝ` its
  `q`-expansion (`G(τ) = g(τ)`, height `0`).

All statements are PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.NewformS13

open ZInQ.Contrib.RC53Assist.NewformPeriods
open ZInQ.Contrib.RC53Assist.NewformPeriodsG1

/-- **`d f = (2πi)⁻¹ H' · dq/q`**: the `q`-expansion of the differential of `f ∈ F` is the expansion
of `(2πi)⁻¹ H'` when `f` is the expansion of `H`. -/
theorem qExpDiff_D_analytic {M : ℕ} [NeZero M] (f : FQ M) {H : ℂ → ℂ} {R : ℝ}
    (e : HasQExpansionAbove (toComplexLaurent (f : LaurentSeries ℚ)) H R) :
    HasQExpansionAbove (toComplexLaurent (qExpDiff M (KaehlerDifferential.D ℚ (FQ M) f)))
      (fun τ => deriv H τ / (2 * Real.pi * Complex.I)) R := by
  intro τ hτ
  rw [qExpDiff_D]
  have := (e.hasDerivAt hτ).1
  refine this.congr_fun fun n => ?_
  simp only [toComplexLaurent_coeff, eulerOp_coeff]
  push_cast
  ring

/-- **The pull-back of `ω_A` is `2πi · c · G(τ) dτ`**: clause (iv) in the analytic period model. -/
theorem pullback_omegaA_analytic {A : WeierstrassCurve ℚ} {x y : LaurentSeries ℚ}
    {ĝ : PowerSeries ℂ} {c : ℂ} (hP : PullbackIsMultiple A x y ĝ c) {X Y G : ℂ → ℂ} {R : ℝ}
    (eX : HasQExpansionAbove (toComplexLaurent x) X R)
    (eY : HasQExpansionAbove (toComplexLaurent y) Y R)
    (eG : HasQExpansionAbove (HahnSeries.ofPowerSeries ℤ ℂ ĝ) G R) {τ : ℂ} (hτ : R < τ.im) :
    deriv X τ = 2 * Real.pi * Complex.I * c * G τ * (2 * Y τ + A.a₁ * X τ + A.a₃) := by
  -- the expansion of `2y + a₁x + a₃`
  have eD : HasQExpansionAbove (toComplexLaurent (omegaDenom A x y))
      (fun τ => 2 * Y τ + (A.a₁ : ℂ) * X τ + (A.a₃ : ℂ)) R := by
    have h2 : toComplexLaurent (omegaDenom A x y) =
        (HahnSeries.C (2 : ℂ) * toComplexLaurent y + HahnSeries.C (A.a₁ : ℂ) * toComplexLaurent x) +
          HahnSeries.C (A.a₃ : ℂ) := by
      rw [omegaDenom, toComplexLaurent_add, toComplexLaurent_add, toComplexLaurent_mul,
        toComplexLaurent_mul, toComplexLaurent_cQ, toComplexLaurent_cQ]
      congr 2
      have : (2 : LaurentSeries ℚ) = cQ 2 := by simp [cQ]
      rw [this, toComplexLaurent_cQ]
      norm_num
    rw [h2]
    exact ((eY.const_mul 2).add' (eX.const_mul _)).add' (hasQExpansionAbove_C _ R)
  -- the expansion of `c · ĝ · (2y + a₁x + a₃)`
  have eR : HasQExpansionAbove
      (HahnSeries.C c * (HahnSeries.ofPowerSeries ℤ ℂ ĝ * toComplexLaurent (omegaDenom A x y)))
      (fun τ => c * (G τ * (2 * Y τ + (A.a₁ : ℂ) * X τ + (A.a₃ : ℂ)))) R :=
    (eG.mul' eD).const_mul c
  -- the expansion of `θx`
  have eT : HasQExpansionAbove (toComplexLaurent (eulerOp x))
      (fun τ => deriv X τ / (2 * Real.pi * Complex.I)) R := by
    intro σ hσ
    refine ((eX.hasDerivAt hσ).1).congr_fun fun n => ?_
    simp only [toComplexLaurent_coeff, eulerOp_coeff]
    push_cast
    ring
  have hEq := eT.unique (hP ▸ eR) hτ hτ
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [div_eq_iff h2pi] at hEq
  rw [hEq]
  ring

/-- **The pull-back of `ω_A` along a modular point, for a cusp form `g` on `Γ₀(M)`**:
`X'(τ) = 2πi · c · g(τ) · (2Y(τ) + a₁X(τ) + a₃)` for `Im τ > max(R, 0)`, i.e. the pull-back of
`ω_A` is `2πi · c · g(τ) dτ`. -/
theorem pullback_omegaA_cuspForm {M : ℕ} (g : CuspForm (CongruenceSubgroup.Gamma0 M :
      Subgroup (GL (Fin 2) ℝ)) 2) {A : WeierstrassCurve ℚ} {x y : LaurentSeries ℚ} {c : ℂ}
    (hP : PullbackIsMultiple A x y (UpperHalfPlane.qExpansion 1 g) c) {X Y : ℂ → ℂ} {R : ℝ}
    (eX : HasQExpansionAbove (toComplexLaurent x) X R)
    (eY : HasQExpansionAbove (toComplexLaurent y) Y R) {τ : ℂ} (hτ : max R 0 < τ.im) :
    deriv X τ = 2 * Real.pi * Complex.I * c * g (UpperHalfPlane.ofComplex τ) *
      (2 * Y τ + A.a₁ * X τ + A.a₃) :=
  pullback_omegaA_analytic hP (eX.mono (le_max_left R 0)) (eY.mono (le_max_left R 0))
    ((hasQExpansionAbove_cuspForm g).mono (le_max_right R 0)) hτ

end ZInQ.Contrib.CloudB3RC53.NewformS13
