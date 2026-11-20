/-
The Leibniz calculation in `taylorZero_mul` is adapted from
`UpperHalfPlane.qExpansion_mul` in Mathlib's modular-form q-expansion module.
Original notice for that calculation:
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import ZInQKernel.Contrib.RC53Assist.NewformPeriodsG1.ParametrizationPeriods
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# The formal discriminant product

The Euler product is formed coefficientwise over the integers. Its image over the
complex numbers is the Taylor series of the analytic Euler product on the open
unit disc. The analytic discriminant identity then gives the formal identity over
the rationals, and injectivity of coefficient extension gives the integer identity.

Relevant locators: `Mathlib/NumberTheory/ModularForms/LevelOne/GradedRing.lean`,
`ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`;
`Mathlib/NumberTheory/ModularForms/DedekindEta.lean`,
`ModularForm.multipliableLocallyUniformlyOn_one_sub_pow`;
`Mathlib/RingTheory/PowerSeries/PiTopology.lean`,
`PowerSeries.WithPiTopology.multipliable_one_sub_X_pow`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Filter Topology
open scoped PowerSeries.WithPiTopology

namespace ZInQ.Contrib.RC53Assist.DeltaProduct

open ZInQ.Contrib.RC53Assist.NewformPeriods
open ZInQ.Contrib.RC53Assist.NewformPeriodsG1

/-- Definition: the integral Euler product. Locator: the definition `ModularCurve.etaProd`
in `Definitions/Def_ModularCurve_X0.lean` of the modular-curve library. -/
def etaProductZ : PowerSeries ℤ :=
  ∏' n : ℕ, (1 - PowerSeries.X ^ (n + 1))

/-- Definition: the integral discriminant product. Locator: the product formula in
`NewformS13/QExpDifferential.lean`, paragraph describing S1. -/
def deltaProductZ : PowerSeries ℤ := PowerSeries.X * etaProductZ ^ 24

/-- Definition: rational coefficient extension of the integral discriminant product.
Locator: `deltaProductZ` in this file. -/
def deltaProductQ : PowerSeries ℚ := deltaProductZ.map (Int.castRingHom ℚ)

/-- Definition: Taylor coefficients at zero of a complex function.
Locator: `UpperHalfPlane.qExpansion` in `Mathlib/NumberTheory/ModularForms/QExpansion.lean`. -/
def taylorZero (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0

/-- Theorem: analytic and algebraic iterated derivatives of a polynomial agree.
Locator: `Polynomial.deriv` in `Mathlib/Analysis/Calculus/Deriv/Polynomial.lean`. -/
theorem iteratedDeriv_polynomial (n : ℕ) (p : Polynomial ℂ) :
    iteratedDeriv n (fun q => p.eval q) =
      fun q => ((Polynomial.derivative : Polynomial ℂ → Polynomial ℂ)^[n] p).eval q := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun q => p.eval q) = fun q => p.derivative.eval q := by
      funext q
      exact p.deriv
    rw [hd, ih]
    simp only [Function.iterate_succ_apply]

/-- Theorem: the Taylor series of a polynomial at zero is its formal power series.
Locator: `Polynomial.coeff_iterate_derivative` in
`Mathlib/Algebra/Polynomial/Derivative.lean`. -/
theorem taylorZero_polynomial (p : Polynomial ℂ) :
    taylorZero (fun q => p.eval q) = (p : PowerSeries ℂ) := by
  ext n
  simp only [taylorZero, PowerSeries.coeff_mk, iteratedDeriv_polynomial]
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n), one_mul]
  simp only [Polynomial.coeff_coe]

/-- Theorem: a locally uniform limit of polynomials has convergent Taylor coefficients.
Locator: `TendstoLocallyUniformlyOn.deriv` in
`Mathlib/Analysis/Complex/LocallyUniformLimit.lean`. -/
theorem polynomial_limit_taylor {ι : Type*} {l : Filter ι}
    {p : ι → Polynomial ℂ} {f : ℂ → ℂ} {s : Set ℂ}
    (h : TendstoLocallyUniformlyOn (fun i q => (p i).eval q) f l s)
    (hs : IsOpen s) (h0 : (0 : ℂ) ∈ s) (n : ℕ) :
    Tendsto (fun i => PowerSeries.coeff n (p i : PowerSeries ℂ)) l
      (𝓝 (PowerSeries.coeff n (taylorZero f))) := by
  have hi : ∀ m : ℕ,
      TendstoLocallyUniformlyOn (fun i => iteratedDeriv m (fun q => (p i).eval q))
        (iteratedDeriv m f) l s := by
    intro m
    induction m with
    | zero => simpa using h
    | succ m ih =>
      have hd : ∀ᶠ i in l,
          DifferentiableOn ℂ (iteratedDeriv m (fun q => (p i).eval q)) s :=
        .of_forall fun i => by
          rw [iteratedDeriv_polynomial]
          exact Polynomial.differentiableOn _
      simpa only [iteratedDeriv_succ, Function.comp_def] using ih.deriv hd hs
  have ht := ((hi n).tendsto_at h0).const_mul ((n.factorial : ℂ)⁻¹)
  simpa only [← taylorZero_polynomial, taylorZero, PowerSeries.coeff_mk] using ht

/-- Definition: the finite integral Euler product as a polynomial.
Locator: `etaProductZ` in this file, restricted to a finite index set. -/
def etaPolynomial (s : Finset ℕ) : Polynomial ℤ :=
  ∏ n ∈ s, (1 - Polynomial.X ^ (n + 1))

/-- Theorem: coefficient extension of the integral Euler product is the Taylor series
of the analytic Euler product. Locator: the convergence results cited in the module
header and `polynomial_limit_taylor` in this file. -/
theorem taylorZero_etaProduct :
    taylorZero (fun q : ℂ => ∏' n : ℕ, (1 - q ^ (n + 1))) =
      etaProductZ.map (Int.castRingHom ℂ) := by
  let p : Finset ℕ → Polynomial ℂ := fun s => (etaPolynomial s).map (Int.castRingHom ℂ)
  have heval : (fun s q => (p s).eval q) =
      (fun s q => ∏ n ∈ s, (1 - q ^ (n + 1))) := by
    funext s q
    simp [p, etaPolynomial, Polynomial.map_prod, Polynomial.eval_prod]
  have hlocal : TendstoLocallyUniformlyOn (fun s q => (p s).eval q)
      (fun q : ℂ => ∏' n : ℕ, (1 - q ^ (n + 1))) atTop (Metric.ball 0 1) := by
    rw [heval]
    exact ModularForm.multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn
  have hpoly (s : Finset ℕ) : (etaPolynomial s : PowerSeries ℤ) =
      ∏ n ∈ s, (1 - PowerSeries.X ^ (n + 1)) := by
    rw [etaPolynomial, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    simp
  ext n
  have hcomplex := polynomial_limit_taylor hlocal Metric.isOpen_ball
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)) n
  have hint : Tendsto (fun s : Finset ℕ => PowerSeries.coeff n (etaPolynomial s : PowerSeries ℤ))
      atTop (𝓝 (PowerSeries.coeff n etaProductZ)) := by
    simp_rw [hpoly]
    exact ((PowerSeries.WithPiTopology.continuous_coeff ℤ n).tendsto etaProductZ).comp
      (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).hasProd
  have hcast := (continuous_of_discreteTopology : Continuous (fun a : ℤ => (a : ℂ))).continuousAt.tendsto.comp hint
  have hcoeff (s : Finset ℕ) : PowerSeries.coeff n (p s : PowerSeries ℂ) =
      ((PowerSeries.coeff n (etaPolynomial s : PowerSeries ℤ) : ℤ) : ℂ) := by
    simp [p]
  simp_rw [hcoeff] at hcomplex
  rw [PowerSeries.coeff_map]
  exact tendsto_nhds_unique hcomplex hcast

/-- Theorem: equal germs at zero have equal Taylor series.
Locator: `Filter.EventuallyEq.iteratedDeriv_eq` in
`Mathlib/Analysis/Calculus/IteratedDeriv/Lemmas.lean`. -/
theorem taylorZero_congr {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 (0 : ℂ)] g) :
    taylorZero f = taylorZero g := by
  ext n
  simp only [taylorZero, PowerSeries.coeff_mk, h.iteratedDeriv_eq n]

/-- Theorem: Taylor series multiply by the Cauchy product.
Locator: `UpperHalfPlane.qExpansion_mul` in
`Mathlib/NumberTheory/ModularForms/QExpansion.lean`; the same Leibniz calculation at zero. -/
theorem taylorZero_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorZero (f * g) = taylorZero f * taylorZero g := by
  ext n
  simp only [taylorZero, PowerSeries.coeff_mk,
    iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.mul_sum, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.cast_choose _ (by simpa using hi)]
  field_simp [Nat.factorial_ne_zero]

/-- Theorem: the Taylor series of the constant function one is one.
Locator: `iteratedDeriv_const` in `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean`. -/
theorem taylorZero_one : taylorZero (fun _ : ℂ => (1 : ℂ)) = 1 := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [taylorZero]
  · simp [taylorZero, iteratedDeriv_const, hn]

/-- Theorem: the Taylor series of the identity function is the formal parameter.
Locator: `iteratedDeriv_fun_id_zero` in
`Mathlib/Analysis/Calculus/IteratedDeriv/Lemmas.lean`. -/
theorem taylorZero_id : taylorZero (fun q : ℂ => q) = PowerSeries.X := by
  ext n
  by_cases hn : n = 1
  · subst n
    simp [taylorZero, iteratedDeriv_fun_id_zero]
  · simp [taylorZero, iteratedDeriv_fun_id_zero, PowerSeries.coeff_X, hn]

/-- Theorem: Taylor series preserve natural powers of an analytic function.
Locator: `taylorZero_mul` in this file. -/
theorem taylorZero_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    taylorZero (fun q => f q ^ n) = taylorZero f ^ n := by
  induction n with
  | zero => simpa using taylorZero_one
  | succ n ih =>
    have heq : (fun q => f q ^ (n + 1)) = (fun q => f q ^ n) * f := by
      funext q
      exact pow_succ _ _
    have hfn : AnalyticAt ℂ (fun q => f q ^ n) 0 := by
      convert! hf.pow n using 1
    rw [heq, taylorZero_mul (f := fun q => f q ^ n) (g := f) hfn hf, ih, pow_succ]

/-- Theorem: the analytic discriminant has the integral formal Euler product as its
complex q-expansion. Locator: `ModularForm.discriminant_cuspFunction_eqOn` in
`Mathlib/NumberTheory/ModularForms/Discriminant.lean`, and `taylorZero_etaProduct` here. -/
theorem qExpansion_discriminant_product :
    UpperHalfPlane.qExpansion 1 ModularForm.discriminant =
      deltaProductZ.map (Int.castRingHom ℂ) := by
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self one_pos
  have heq : UpperHalfPlane.cuspFunction 1 ModularForm.discriminant =ᶠ[𝓝 (0 : ℂ)]
      (fun q : ℂ => q * (∏' n : ℕ, (1 - q ^ (n + 1))) ^ 24) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds h0] with q hq
    rw [ModularForm.discriminant_cuspFunction_eqOn hq]
    exact congrArg (q * ·)
      ((ModularForm.multipliable_one_sub_pow (by simpa using hq)).tprod_pow 24)
  have ha : AnalyticAt ℂ (fun q : ℂ => ∏' n : ℕ, (1 - q ^ (n + 1))) 0 :=
    (ModularForm.differentiableOn_tprod_one_sub_pow.analyticOnNhd Metric.isOpen_ball) 0 h0
  change taylorZero (UpperHalfPlane.cuspFunction 1 ModularForm.discriminant) = _
  rw [taylorZero_congr heq]
  change taylorZero ((fun q : ℂ => q) *
    (fun q : ℂ => (∏' n : ℕ, (1 - q ^ (n + 1))) ^ 24)) = _
  have hpow : AnalyticAt ℂ
      (fun q : ℂ => (∏' n : ℕ, (1 - q ^ (n + 1))) ^ 24) 0 := by
    convert! ha.pow 24 using 1
  rw [taylorZero_mul (f := fun q : ℂ => q)
      (g := fun q : ℂ => (∏' n : ℕ, (1 - q ^ (n + 1))) ^ 24) analyticAt_id hpow,
    taylorZero_id, taylorZero_pow ha, taylorZero_etaProduct]
  simp only [deltaProductZ, map_mul, map_pow, PowerSeries.map_X]

/-- Theorem: rational Eisenstein coefficients give the complex q-expansion of E₄.
Locator: `qExpansion_E₄_coeff` in `NewformPeriodsG1/ParametrizationPeriods.lean`. -/
theorem qExpansion_E4Q : UpperHalfPlane.qExpansion 1 ModularForm.E₄ =
    eisensteinE4Q.map (algebraMap ℚ ℂ) := by
  ext n
  rw [PowerSeries.coeff_map]
  exact qExpansion_E₄_coeff n

/-- Theorem: rational Eisenstein coefficients give the complex q-expansion of E₆.
Locator: `qExpansion_E₆_coeff` in `NewformPeriodsG1/ParametrizationPeriods.lean`. -/
theorem qExpansion_E6Q : UpperHalfPlane.qExpansion 1 ModularForm.E₆ =
    eisensteinE6Q.map (algebraMap ℚ ℂ) := by
  ext n
  rw [PowerSeries.coeff_map]
  exact qExpansion_E₆_coeff n

/-- Theorem: extension of the discriminant product from integers to rationals to
complex numbers agrees with direct coefficient extension. Locator: `deltaProductQ` here. -/
theorem map_deltaProductQ_complex : deltaProductQ.map (algebraMap ℚ ℂ) =
    deltaProductZ.map (Int.castRingHom ℂ) := by
  ext n
  simp [deltaProductQ]

/-- Theorem: the formal rational discriminant identity, with no additional hypothesis.
Locator: `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq_graded` in
`Mathlib/NumberTheory/ModularForms/LevelOne/GradedRing.lean` and the preceding coefficient
transport. -/
theorem formal_delta_identity_Q : eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2 =
    1728 * deltaProductQ := by
  have h := congrArg (ModularForm.qExpansionAlgHom 1 one_pos one_mem_strictPeriods_SL)
    ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq_graded
  simp only [map_smul, map_sub, map_pow, ModularForm.qExpansionAlgHom_apply] at h
  change UpperHalfPlane.qExpansion 1 ModularForm.discriminant =
    (1 / 1728 : ℂ) • ((UpperHalfPlane.qExpansion 1 ModularForm.E₄) ^ 3 -
      (UpperHalfPlane.qExpansion 1 ModularForm.E₆) ^ 2) at h
  rw [qExpansion_discriminant_product, qExpansion_E4Q, qExpansion_E6Q] at h
  apply (PowerSeries.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective)
  simp only [map_sub, map_pow, map_mul, map_ofNat, map_deltaProductQ_complex]
  have h' : (1728 : ℂ) • deltaProductZ.map (Int.castRingHom ℂ) =
      eisensteinE4Q.map (algebraMap ℚ ℂ) ^ 3 - eisensteinE6Q.map (algebraMap ℚ ℂ) ^ 2 := by
    rw [h, smul_smul]
    norm_num
  have hC : PowerSeries.C (1728 : ℂ) = (1728 : PowerSeries ℂ) := map_ofNat _ _
  simpa [Algebra.smul_def, hC] using h'.symm

/-- Theorem: rational coefficient extension preserves the integral Euler product.
Locator: `PowerSeries.WithPiTopology.multipliable_one_sub_X_pow` in
`Mathlib/RingTheory/PowerSeries/PiTopology.lean`. -/
theorem etaProductZ_map_rat : etaProductZ.map (Int.castRingHom ℚ) =
    ∏' n : ℕ, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)) := by
  have hc : Continuous (PowerSeries.map (Int.castRingHom ℚ)) := by
    rw [continuous_iff_continuousAt]
    intro z
    change Tendsto (PowerSeries.map (Int.castRingHom ℚ)) (𝓝 z) (𝓝 _)
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro n
    simp only [PowerSeries.coeff_map]
    exact (continuous_of_discreteTopology : Continuous (fun a : ℤ => (a : ℚ))).continuousAt.tendsto.comp
      ((PowerSeries.WithPiTopology.continuous_coeff ℤ n).tendsto z)
  simpa only [etaProductZ, map_sub, map_one, map_pow, PowerSeries.map_X] using
    (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).map_tprod
      (PowerSeries.map (Int.castRingHom ℚ)) hc

/-- Theorem: the rational discriminant product is the formal product over the rationals.
Locator: `etaProductZ_map_rat` and `deltaProductQ` in this file. -/
theorem deltaProductQ_eq_product : deltaProductQ = PowerSeries.X *
    (∏' n : ℕ, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (n + 1))) ^ 24 := by
  simp only [deltaProductQ, deltaProductZ, map_mul, map_pow, PowerSeries.map_X,
    etaProductZ_map_rat]

/-- Theorem: E₄³ − E₆² equals 1728 times the formal discriminant Euler product in ℚ⟦q⟧.
Locator: S1 in `NewformS13/QExpDifferential.lean`, and `formal_delta_identity_Q` here. -/
theorem formal_delta_product_identity_Q : eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2 =
    1728 * PowerSeries.X *
      (∏' n : ℕ, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (n + 1))) ^ 24 := by
  rw [formal_delta_identity_Q, deltaProductQ_eq_product]
  ring

/-- Theorem: the normalized formal identity Δ = (E₄³ − E₆²)/1728 over the rationals.
Locator: `formal_delta_product_identity_Q` in this file; division is rational scalar
multiplication, not division by a nonunit formal parameter. -/
theorem formal_delta_normalized_Q :
    PowerSeries.C (1 / 1728 : ℚ) * (eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2) =
      PowerSeries.X * (∏' n : ℕ, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (n + 1))) ^ 24 := by
  rw [formal_delta_identity_Q]
  have hc : PowerSeries.C (1 / 1728 : ℚ) * (1728 : PowerSeries ℚ) = 1 := by
    rw [← map_ofNat (PowerSeries.C (R := ℚ)) 1728, ← map_mul]
    norm_num
  rw [← mul_assoc, hc, one_mul, deltaProductQ_eq_product]

/-- Definition: the integral E₄ expansion, written with divisor sums.
Locator: `ModularCurve.eisenstein4` in `Definitions/Def_ModularCurve_X0.lean` of the
modular-curve library. -/
def eisenstein4Z : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3

/-- Definition: the integral E₆ expansion, written with divisor sums.
Locator: `eisensteinE6Q` in `NewformPeriods/RationalParametrization.lean`. -/
def eisenstein6Z : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5

/-- Theorem: integral and rational E₄ expansions agree under coefficient extension.
Locator: `ArithmeticFunction.sigma_apply` and the definitions of E₄ cited above. -/
theorem map_eisenstein4Z_rat : eisenstein4Z.map (Int.castRingHom ℚ) = eisensteinE4Q := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [eisenstein4Z, eisensteinE4Q]
  · simp only [PowerSeries.coeff_map, eisenstein4Z, eisensteinE4Q,
      PowerSeries.coeff_mk, ite_eq_right hn]
    change ((240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3 : ℤ) : ℚ) =
      240 * (ArithmeticFunction.sigma 3 n : ℚ)
    rw [ArithmeticFunction.sigma_apply]
    push_cast
    all_goals rfl

/-- Theorem: integral and rational E₆ expansions agree under coefficient extension.
Locator: `ArithmeticFunction.sigma_apply` and the definitions of E₆ cited above. -/
theorem map_eisenstein6Z_rat : eisenstein6Z.map (Int.castRingHom ℚ) = eisensteinE6Q := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [eisenstein6Z, eisensteinE6Q]
  · simp only [PowerSeries.coeff_map, eisenstein6Z, eisensteinE6Q,
      PowerSeries.coeff_mk, ite_eq_right hn]
    change ((-504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5 : ℤ) : ℚ) =
      -504 * (ArithmeticFunction.sigma 5 n : ℚ)
    rw [ArithmeticFunction.sigma_apply]
    push_cast
    all_goals rfl

/-- Theorem: the integral formal discriminant identity, without additional hypotheses.
Locator: `formal_delta_identity_Q` in this file and injectivity of ℤ → ℚ. -/
theorem formal_delta_identity_Z : eisenstein4Z ^ 3 - eisenstein6Z ^ 2 =
    1728 * deltaProductZ := by
  apply PowerSeries.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simpa only [map_sub, map_pow, map_mul, map_ofNat, map_eisenstein4Z_rat,
    map_eisenstein6Z_rat, deltaProductQ] using formal_delta_identity_Q

/-- Theorem: the integral identity in its literal Euler-product form.
Locator: `formal_delta_identity_Z` and `deltaProductZ` in this file. -/
theorem formal_delta_product_identity_Z : eisenstein4Z ^ 3 - eisenstein6Z ^ 2 =
    1728 * PowerSeries.X *
      (∏' n : ℕ, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (n + 1))) ^ 24 := by
  rw [formal_delta_identity_Z, deltaProductZ, etaProductZ]
  ring

/-- Theorem: the integral Euler product has constant coefficient one.
Locator: `ModularCurve.constantCoeff_etaProd` in `Definitions/Def_ModularCurve_X0.lean`
and `PowerSeries.WithPiTopology.continuous_constantCoeff`. -/
theorem constantCoeff_etaProductZ : PowerSeries.constantCoeff etaProductZ = 1 := by
  rw [etaProductZ]
  simp [(PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).map_tprod _
    (PowerSeries.WithPiTopology.continuous_constantCoeff ℤ)]

/-- Definition: the integral numerator of the product-defined j-invariant.
Locator: the expanded definitions `ModularCurve.jNum`, `dedekindEtaUnit`, and
`dedekindEtaUnitInv` in `Definitions/Def_ModularCurve_X0.lean`. -/
def jNumeratorZ : PowerSeries ℤ :=
  eisenstein4Z ^ 3 * (etaProductZ ^ 24).invOfUnit 1

/-- Definition: the product-defined j-invariant in ℚ((q)).
Locator: the expanded definitions `ModularCurve.jq` and `jNumQ` in
`Definitions/Def_ModularCurve_X0.lean`. -/
def jProductQ : LaurentSeries ℚ :=
  HahnSeries.single (-1 : ℤ) 1 *
    HahnSeries.ofPowerSeries ℤ ℚ (jNumeratorZ.map (Int.castRingHom ℚ))

/-- Theorem: the Eisenstein and product definitions of j agree as rational Laurent series.
Locator: S1 in `NewformS13/QExpDifferential.lean`; the product expression is the exact
expanded expression defining `ModularCurve.jq`. -/
theorem jInvariantQ_eq_product : jInvariantQ = jProductQ := by
  let u : PowerSeries ℚ := (etaProductZ ^ 24).map (Int.castRingHom ℚ)
  let v : PowerSeries ℚ := ((etaProductZ ^ 24).invOfUnit 1).map (Int.castRingHom ℚ)
  have huv : u * v = 1 := by
    have h0 : PowerSeries.constantCoeff (etaProductZ ^ 24) = (1 : ℤ) := by
      simp [constantCoeff_etaProductZ]
    have h := congrArg (PowerSeries.map (Int.castRingHom ℚ))
      (PowerSeries.mul_invOfUnit (etaProductZ ^ 24) 1 h0)
    simpa only [map_mul, map_one, u, v] using h
  have hj : jProductQ = HahnSeries.single (-1 : ℤ) 1 *
      (HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q ^ 3 * HahnSeries.ofPowerSeries ℤ ℚ v) := by
    simp only [jProductQ, jNumeratorZ, map_mul, map_pow, map_eisenstein4Z_rat, v]
  have hd : HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q ^ 3 -
      HahnSeries.ofPowerSeries ℤ ℚ eisensteinE6Q ^ 2 =
        1728 * (HahnSeries.ofPowerSeries ℤ ℚ PowerSeries.X * HahnSeries.ofPowerSeries ℤ ℚ u) := by
    have h := congrArg (HahnSeries.ofPowerSeries ℤ ℚ) formal_delta_identity_Q
    simpa only [map_sub, map_pow, map_mul, map_ofNat, deltaProductQ, deltaProductZ,
      PowerSeries.map_X, u] using h
  have hdmap : HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q ^ 3 -
      HahnSeries.ofPowerSeries ℤ ℚ eisensteinE6Q ^ 2 =
        HahnSeries.ofPowerSeries ℤ ℚ (eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2) := by
    rw [map_sub, map_pow, map_pow]
  have hd0 : HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q ^ 3 -
      HahnSeries.ofPowerSeries ℤ ℚ eisensteinE6Q ^ 2 ≠ 0 := by
    rw [hdmap]
    intro h0
    have h := congrArg (fun z : LaurentSeries ℚ => z.coeff ((1 : ℕ) : ℤ)) h0
    simp only [HahnSeries.ofPowerSeries_apply_coeff, eisenstein_disc_coeff_one,
      HahnSeries.coeff_zero] at h
    norm_num at h
  have hq : (HahnSeries.single (-1 : ℤ) 1 : LaurentSeries ℚ) *
      HahnSeries.ofPowerSeries ℤ ℚ PowerSeries.X = 1 := by
    rw [HahnSeries.ofPowerSeries_X, HahnSeries.single_mul_single]
    norm_num [← HahnSeries.C_apply]
  have huvL : HahnSeries.ofPowerSeries ℤ ℚ u * HahnSeries.ofPowerSeries ℤ ℚ v = 1 := by
    rw [← map_mul, huv, map_one]
  rw [jInvariantQ, div_eq_iff hd0]
  calc
    1728 * HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q ^ 3 =
        1728 * HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q ^ 3 * 1 * 1 := by ring
    _ = 1728 * HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q ^ 3 *
        (HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ PowerSeries.X) *
        (HahnSeries.ofPowerSeries ℤ ℚ u * HahnSeries.ofPowerSeries ℤ ℚ v) := by rw [hq, huvL]
    _ = jProductQ * (HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q ^ 3 -
        HahnSeries.ofPowerSeries ℤ ℚ eisensteinE6Q ^ 2) := by
      rw [hj, hd]
      ring

/-- Theorem: the rational modular function field agrees with the field generated by
the product-defined j and its level substitution. Locator: `modularFunctionFieldQ` in
`NewformPeriods/RationalParametrization.lean` and the exact expanded definition of
`ModularCurve.modularFunctionField` in `Definitions/Def_ModularCurve_X0.lean`. -/
theorem modularFunctionFieldQ_eq_product_field (M : ℕ) [NeZero M] :
    modularFunctionFieldQ M =
      IntermediateField.adjoin ℚ {jProductQ, qPow M jProductQ} := by
  simp only [modularFunctionFieldQ, jInvariantQ_eq_product]

/-- Theorem: the literal rational product identity with exponent 24 on each factor.
Locator: the formal discriminant identity requested in S1 of
`NewformS13/QExpDifferential.lean`, and `Multipliable.tprod_pow` in Mathlib. -/
theorem formal_delta_product_Q :
    PowerSeries.C (1 / 1728 : ℚ) * (eisensteinE4Q ^ 3 - eisensteinE6Q ^ 2) =
      PowerSeries.X * ∏' n : ℕ, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (n + 1)) ^ 24 := by
  rw [formal_delta_normalized_Q,
    ← (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℚ).tprod_pow 24]

/-- Theorem: the literal integral product identity with exponent 24 on each factor.
Locator: `formal_delta_product_identity_Z` in this file and `Multipliable.tprod_pow`
in Mathlib. -/
theorem formal_delta_product_Z : eisenstein4Z ^ 3 - eisenstein6Z ^ 2 =
    1728 * PowerSeries.X *
      ∏' n : ℕ, (1 - (PowerSeries.X : PowerSeries ℤ) ^ (n + 1)) ^ 24 := by
  rw [formal_delta_product_identity_Z,
    ← (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).tprod_pow 24]

end ZInQ.Contrib.RC53Assist.DeltaProduct
