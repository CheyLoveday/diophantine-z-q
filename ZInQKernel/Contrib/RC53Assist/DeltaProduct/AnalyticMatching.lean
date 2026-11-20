import ZInQKernel.Contrib.CloudB3RC53.NewformS13.AnalyticNormalization

/-!
# Differential normalization and weak Weil parametrizations

For convergent Laurent expansions, the formal pullback identity is equivalent to
its analytic derivative identity with the factor 2πi. A nonconstant rational modular
point with the prescribed elliptic-curve coefficients therefore supplies the exact
rational scalar and period data of `HasWeakWeilParametrization`.

No construction of a scheme X₀(M), and no converse algebraization of arbitrary weak
Weil data, is asserted here.

Locators: `NewformS13/AnalyticNormalization.lean`;
`NewformPeriodsG1/ParametrizationPeriods.lean`, `parametrizationPeriodsGlue_holds`;
`ModularWeil/WeakWeil.lean`, `exists_isLatticeOf`;
`Prints/Kolyvagin.lean`, `HasWeakWeilParametrization`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.DeltaProduct

open ZInQ.Contrib.RC53Assist.NewformPeriods
open ZInQ.Contrib.RC53Assist.NewformPeriodsG1
open ZInQ.Contrib.CloudB3RC53.NewformS13
open ZInQ.Contrib.CloudB3RC53.ModularWeil
open ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Contrib.CloudB3RC53
open CongruenceSubgroup UpperHalfPlane

/-- Theorem: the Euler operator expands the derivative divided by 2πi.
Locator: `HasQExpansionAbove.hasDerivAt` in
`NewformPeriodsG1/ParametrizationPeriods.lean`. -/
theorem hasQExpansionAbove_eulerOp {x : LaurentSeries ℚ} {X : ℂ → ℂ} {R : ℝ}
    (eX : HasQExpansionAbove (toComplexLaurent x) X R) :
    HasQExpansionAbove (toComplexLaurent (eulerOp x))
      (fun τ => deriv X τ / (2 * Real.pi * Complex.I)) R := by
  intro τ hτ
  refine ((eX.hasDerivAt hτ).1).congr_fun fun n => ?_
  simp only [toComplexLaurent_coeff, eulerOp_coeff]
  push_cast
  ring

/-- Theorem: the invariant-differential denominator has the expected analytic expansion.
Locator: `omegaDenom` in `NewformPeriods/RationalParametrization.lean` and
`HasQExpansionAbove.add'`, `.const_mul` in `NewformPeriodsG1/ParametrizationPeriods.lean`. -/
theorem hasQExpansionAbove_omegaDenom {A : WeierstrassCurve ℚ}
    {x y : LaurentSeries ℚ} {X Y : ℂ → ℂ} {R : ℝ}
    (eX : HasQExpansionAbove (toComplexLaurent x) X R)
    (eY : HasQExpansionAbove (toComplexLaurent y) Y R) :
    HasQExpansionAbove (toComplexLaurent (omegaDenom A x y))
      (fun τ => 2 * Y τ + (A.a₁ : ℂ) * X τ + (A.a₃ : ℂ)) R := by
  rw [omegaDenom, two_mul, toComplexLaurent_add, toComplexLaurent_add,
    toComplexLaurent_add, toComplexLaurent_mul, toComplexLaurent_cQ, toComplexLaurent_cQ]
  simpa only [two_mul] using
    (((eY.add' eY).add' (eX.const_mul (A.a₁ : ℂ))).add'
      (hasQExpansionAbove_C (A.a₃ : ℂ) R))

/-- Theorem: the formal pullback identity is equivalent to its analytic derivative
identity above the same height. Locator: `pullback_omegaA_analytic` in
`NewformS13/AnalyticNormalization.lean`; the reverse implication uses uniqueness of
convergent Laurent expansions, not an algebraization hypothesis. -/
theorem pullbackIsMultiple_iff_analytic {A : WeierstrassCurve ℚ}
    {x y : LaurentSeries ℚ} {ĝ : PowerSeries ℂ} {c : ℂ}
    {X Y G : ℂ → ℂ} {R : ℝ}
    (eX : HasQExpansionAbove (toComplexLaurent x) X R)
    (eY : HasQExpansionAbove (toComplexLaurent y) Y R)
    (eG : HasQExpansionAbove (HahnSeries.ofPowerSeries ℤ ℂ ĝ) G R) :
    PullbackIsMultiple A x y ĝ c ↔
      ∀ τ : ℂ, R < τ.im → deriv X τ =
        2 * Real.pi * Complex.I * c * G τ * (2 * Y τ + (A.a₁ : ℂ) * X τ + (A.a₃ : ℂ)) := by
  constructor
  · intro h τ hτ
    exact pullback_omegaA_analytic h eX eY eG hτ
  · intro h
    have eθ := hasQExpansionAbove_eulerOp eX
    have eD := hasQExpansionAbove_omegaDenom (A := A) eX eY
    have eP := (eG.mul' eD).const_mul c
    have hz := (eθ.sub' eP).eq_zero fun τ hτ => by
      apply sub_eq_zero.mpr
      have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      rw [div_eq_iff h2pi, h τ hτ]
      ring
    exact sub_eq_zero.mp hz

/-- Theorem: the equivalence specialized to the q-expansion of a weight-two cusp form.
Locator: `hasQExpansionAbove_cuspForm` in `NewformPeriodsG1/ParametrizationPeriods.lean`
and `pullbackIsMultiple_iff_analytic` in this file. -/
theorem pullbackIsMultiple_cuspForm_iff_analytic {M : ℕ}
    (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2)
    {A : WeierstrassCurve ℚ} {x y : LaurentSeries ℚ} {c : ℂ}
    {X Y : ℂ → ℂ} {R : ℝ}
    (eX : HasQExpansionAbove (toComplexLaurent x) X R)
    (eY : HasQExpansionAbove (toComplexLaurent y) Y R) :
    PullbackIsMultiple A x y (qExpansion 1 g) c ↔
      ∀ τ : ℂ, max R 0 < τ.im → deriv X τ =
        2 * Real.pi * Complex.I * c * g (ofComplex τ) *
          (2 * Y τ + (A.a₁ : ℂ) * X τ + (A.a₃ : ℂ)) :=
  pullbackIsMultiple_iff_analytic
    (eX.mono (le_max_left R 0)) (eY.mono (le_max_left R 0))
    ((hasQExpansionAbove_cuspForm g).mono (le_max_right R 0))

/-- Theorem: rational coefficients force the pullback scalar to be rational for a
nonconstant rational Laurent coordinate. No normalization of a chosen coefficient is
required. Locator: the coefficient comparison in `exists_rat_eq_of_pullbackIsMultiple`
in `NewformPeriods/RationalParametrization.lean`. -/
theorem exists_rat_eq_of_rational_pullback {A : WeierstrassCurve ℚ}
    {x y : LaurentSeries ℚ} (hx : ∃ n : ℤ, n ≠ 0 ∧ x.coeff n ≠ 0)
    {b : ℕ → ℚ} {c : ℂ}
    (h : PullbackIsMultiple A x y ((PowerSeries.mk b).map (algebraMap ℚ ℂ)) c) :
    ∃ r : ℚ, (r : ℂ) = c := by
  set G : LaurentSeries ℚ := HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.mk b) with hG
  set u : LaurentSeries ℚ := G * omegaDenom A x y with hu
  have hmap : toComplexLaurent (eulerOp x) = HahnSeries.C c * toComplexLaurent u := by
    rw [h, hu, toComplexLaurent_mul, hG, toComplexLaurent_ofPowerSeries]
  have hθ : eulerOp x ≠ 0 := by
    intro h0
    obtain ⟨n, hn0, hxn⟩ := hx
    have h1 := congrArg (fun z : LaurentSeries ℚ => z.coeff n) h0
    simp only [eulerOp_coeff, HahnSeries.coeff_zero] at h1
    exact (mul_ne_zero (by exact_mod_cast hn0) hxn) h1
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, toComplexLaurent_zero, mul_zero] at hmap
    exact hθ (toComplexLaurent_injective (hmap.trans toComplexLaurent_zero.symm))
  obtain ⟨n, hn⟩ : ∃ n : ℤ, u.coeff n ≠ 0 := by
    by_contra hno
    apply hu0
    ext n
    by_contra hne
    exact hno ⟨n, hne⟩
  refine ⟨(eulerOp x).coeff n / u.coeff n, ?_⟩
  have h1 := congrArg (fun z : LaurentSeries ℂ => z.coeff n) hmap
  simp only [toComplexLaurent_coeff, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
    smul_eq_mul] at h1
  have hun : ((u.coeff n : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Rat.cast_div, h1]
  field_simp

/-- Theorem: a cusp form with the elliptic-curve coefficients has a rational formal
q-expansion, including its zero constant term. Locator: `HasWeakWeilParametrization`
in `Prints/Kolyvagin.lean` and `CuspFormClass.qExpansion_coeff_zero` in Mathlib. -/
theorem qExpansion_eq_rational_coefficients {M : ℕ} (E : WeierstrassCurve ℚ)
    (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2)
    (hg : ∀ n : ℕ, 0 < n → (qExpansion 1 g).coeff n = (E.LFunction n : ℂ)) :
    qExpansion 1 g =
      (PowerSeries.mk (fun n => if n = 0 then 0 else (E.LFunction n : ℚ))).map
        (algebraMap ℚ ℂ) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · subst n
    simpa using CuspFormClass.qExpansion_coeff_zero g one_pos (one_mem_strictPeriods_Gamma0 M)
  · simp only [ite_eq_right hn]
    simpa using hg n (Nat.pos_of_ne_zero hn)

/-- Theorem: a nonconstant rational modular point at the exact newform level, with
the prescribed differential pullback, gives `HasWeakWeilParametrization` in its exact
definition. The rational scalar is proved by coefficient comparison, and the period
condition is proved by `parametrizationPeriodsGlue_holds`.
Locators: `Prints/Kolyvagin.lean`, `HasWeakWeilParametrization`;
`ModularWeil/WeakWeil.lean`, `exists_isLatticeOf`;
`NewformPeriodsG1/ParametrizationPeriods.lean`, `parametrizationPeriodsGlue_holds`. -/
theorem hasWeakWeilParametrization_of_modularPoint (E : WeierstrassCurve ℚ)
    [E.IsElliptic] [NeZero (newformLevel E)]
    (g : CuspForm (Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hg : ∀ n : ℕ, 0 < n → (qExpansion 1 g).coeff n = (E.LFunction n : ℂ))
    {x y : LaurentSeries ℚ} (hpt : IsModularPointQ (newformLevel E) E x y)
    {c : ℂ} (hp : PullbackIsMultiple E x y (qExpansion 1 g) c) :
    HasWeakWeilParametrization E := by
  have hc : c ≠ 0 := ne_zero_of_pullbackIsMultiple hpt.2.2.2 hp
  have hq := qExpansion_eq_rational_coefficients E g hg
  have hpQ : PullbackIsMultiple E x y
      ((PowerSeries.mk (fun n => if n = 0 then 0 else (E.LFunction n : ℚ))).map
        (algebraMap ℚ ℂ)) c := by
    rwa [← hq]
  obtain ⟨r, hr⟩ := exists_rat_eq_of_rational_pullback hpt.2.2.2 hpQ
  obtain ⟨Lat, hLat⟩ := exists_isLatticeOf E
  have hs := parametrizationPeriodsGlue_holds (newformLevel E) g E inferInstance
    x y hpt c hc hp Lat hLat
  refine ⟨g, Lat, r, hg, hLat, ?_⟩
  rw [hr]
  exact hs

/-- Theorem: the analytic derivative identity of a realized rational modular point
also gives the exact weak Weil parametrization data. Locator:
`pullbackIsMultiple_cuspForm_iff_analytic` and
`hasWeakWeilParametrization_of_modularPoint` in this file. -/
theorem hasWeakWeilParametrization_of_analytic_modularPoint (E : WeierstrassCurve ℚ)
    [E.IsElliptic] [NeZero (newformLevel E)]
    (g : CuspForm (Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hg : ∀ n : ℕ, 0 < n → (qExpansion 1 g).coeff n = (E.LFunction n : ℂ))
    {x y : LaurentSeries ℚ} (hpt : IsModularPointQ (newformLevel E) E x y)
    {c : ℂ} {X Y : ℂ → ℂ} {R : ℝ}
    (eX : HasQExpansionAbove (toComplexLaurent x) X R)
    (eY : HasQExpansionAbove (toComplexLaurent y) Y R)
    (hd : ∀ τ : ℂ, max R 0 < τ.im → deriv X τ =
      2 * Real.pi * Complex.I * c * g (ofComplex τ) *
        (2 * Y τ + (E.a₁ : ℂ) * X τ + (E.a₃ : ℂ))) :
    HasWeakWeilParametrization E :=
  hasWeakWeilParametrization_of_modularPoint E g hg hpt
    ((pullbackIsMultiple_cuspForm_iff_analytic g eX eY).mpr hd)

end ZInQ.Contrib.RC53Assist.DeltaProduct
