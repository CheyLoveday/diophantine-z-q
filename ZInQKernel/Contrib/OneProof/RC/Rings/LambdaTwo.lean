import ZInQKernel.Contrib.OneProof.RC.Rings.Localization
import ZInQKernel.Contrib.OneProof.RC.Rings.DVRValuation
import ZInQKernel.Contrib.OneProof.RC.Uniform.UniformLowerBound

/-!
# Lane RC20: the localization `Λ_{(2)}` and its valuation

Manuscript (`diophantine_zq.tex`, 11/5 version), Definition `ex:arith-data`, tex 2747–2748: "Put
`Λ = ℤ₂[[t]]` and `𝒪 = \widehat{Λ_{(2)}}`"; tex 3728: `𝒪 = \widehat{ℤ₂[[t]]_{(2)}}`. The ring `Λ_{(2)}` is
the localization of `Λ` at its height-one prime `(2)`.

`Λ = Uniform.Lambda = PowerSeries ℤ_[2]` is lane RC16's object (with `prime_two_lambda`, `lambda_ufd`,
`RegularAt`, `RegularAtPrime`). This file proves:

* `LambdaTwo := Localization.AtPrime (Ideal.span {2})` is a discrete valuation ring
  (`instIsDiscreteValuationRingLambdaTwo`) with uniformizer `2` (`irreducible_two_lambdaTwo`) and
  maximal ideal `(2)` (`maximalIdeal_lambdaTwo`);
* `v2 : AddValuation (FractionRing Λ) (WithTop ℤ)`, the valuation of the DVR `Λ_{(2)}` on
  `Frac Λ = Frac Λ_{(2)}`, with `v2_two : v2 2 = 1`;
* its ring of integers is `Λ_{(2)}`: `v2_nonneg_iff_mem_range`, `v2_nonneg_iff_regularAt` (RC16's
  elementwise form `RegularAt 2`), `v2_nonneg_iff_regularAtPrime` (RC16's genuine-localization form);
* on `Λ` it is the Gauss valuation: `two_pow_dvd_iff_forall_coeff` (`2ᵏ ∣ f` iff `2ᵏ` divides every
  coefficient), `le_v2_iff_two_pow_dvd` (`k ≤ v2 f ↔ 2ᵏ ∣ f`), `le_v2_iff_forall_coeff`, and
  `v2_algebraMap_two_pow_mul` (`v2 (2ⁿ b) = n` for `2 ∤ b`).

Everything here is `PROVED`.
-/

namespace ZInQ.Manuscript.RC.Rings

open ZInQ.Manuscript.RC.Uniform

/-- **Tex 2747–2748 (PROVED).** `(2)` is a prime ideal of `Λ = ℤ₂[[t]]` (from RC16's
`prime_two_lambda`). -/
instance isPrime_span_two_lambda : (Ideal.span {(2 : Lambda)}).IsPrime :=
  (Ideal.span_singleton_prime prime_two_lambda.ne_zero).mpr prime_two_lambda

/-- `Λ_{(2)}`, the localization of `Λ = ℤ₂[[t]]` at the height-one prime `(2)` (tex 2747–2748). -/
abbrev LambdaTwo : Type := Localization.AtPrime (Ideal.span {(2 : Lambda)})

/-- **Tex 2747–2748, 4720–4730 (PROVED).** `Λ_{(2)}` is a discrete valuation ring. -/
instance instIsDiscreteValuationRingLambdaTwo : IsDiscreteValuationRing LambdaTwo :=
  isDiscreteValuationRing_of_atPrime LambdaTwo prime_two_lambda.ne_zero

/-- **Tex 2747–2748, 4729 ("uniformizer two") (PROVED).** `2` is a uniformizer of `Λ_{(2)}`. -/
theorem irreducible_two_lambdaTwo : Irreducible (2 : LambdaTwo) := by
  have h := irreducible_algebraMap_of_atPrime LambdaTwo (p := (2 : Lambda)) prime_two_lambda.ne_zero
  rwa [map_ofNat] at h

/-- **Tex 2747–2748 (PROVED).** The maximal ideal of `Λ_{(2)}` is `(2)`. -/
theorem maximalIdeal_lambdaTwo : IsLocalRing.maximalIdeal LambdaTwo = Ideal.span {2} :=
  irreducible_two_lambdaTwo.maximalIdeal_eq

/-- **Tex 2747–2748 (PROVED).** `Λ → Λ_{(2)}` is injective. -/
theorem algebraMap_lambdaTwo_injective : Function.Injective (algebraMap Lambda LambdaTwo) :=
  IsLocalization.injective LambdaTwo (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {(2 : Lambda)}))

/-- **The valuation of `Λ_{(2)}` on `Frac Λ`** (tex 2747–2748; `PROVED` construction). `Frac Λ` is a
fraction field of `Λ_{(2)}` (Mathlib instance), and `v2` is the valuation of the DVR `Λ_{(2)}` with
uniformizer `2` (`dvrAddVal`). -/
noncomputable def v2 : AddValuation (FractionRing Lambda) (WithTop ℤ) :=
  dvrAddVal (R := LambdaTwo) irreducible_two_lambdaTwo

/-- **Tex 2747–2748, 4729 (PROVED).** `v2 2 = 1`. -/
theorem v2_two : v2 (2 : FractionRing Lambda) = 1 := by
  have h := dvrAddVal_uniformizer (K := FractionRing Lambda) irreducible_two_lambdaTwo
  rwa [map_ofNat] at h

/-- **Tex 2747–2748 (PROVED).** The ring of integers of `v2` is `Λ_{(2)}`. -/
theorem v2_nonneg_iff_mem_range (x : FractionRing Lambda) :
    0 ≤ v2 x ↔ x ∈ (algebraMap LambdaTwo (FractionRing Lambda)).range :=
  dvrAddVal_nonneg_iff irreducible_two_lambdaTwo

/-- **Tex 2747–2748 (PROVED).** Membership in `Λ_{(2)} ⊂ Frac Λ` in RC16's elementwise form: `x` lies in
`Λ_{(2)}` iff `x s ∈ Λ` for some `s ∉ (2)`. -/
theorem mem_range_lambdaTwo_iff_regularAt (x : FractionRing Lambda) :
    x ∈ (algebraMap LambdaTwo (FractionRing Lambda)).range ↔ RegularAt 2 x := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨a, s⟩, hy⟩ := IsLocalization.surj (Ideal.span {(2 : Lambda)}).primeCompl y
    refine ⟨a, s, s.2, ?_⟩
    have h := congrArg (algebraMap LambdaTwo (FractionRing Lambda)) hy
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
    exact h
  · rintro ⟨a, s, hs, hxs⟩
    refine ⟨IsLocalization.mk' LambdaTwo a (⟨s, hs⟩ : (Ideal.span {(2 : Lambda)}).primeCompl), ?_⟩
    have hs0 : s ≠ 0 := fun h => hs (h ▸ Ideal.zero_mem _)
    have hsK : algebraMap Lambda (FractionRing Lambda) s ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective Lambda (FractionRing Lambda))).mpr hs0
    apply mul_right_cancel₀ hsK
    rw [hxs, IsScalarTower.algebraMap_apply Lambda LambdaTwo (FractionRing Lambda) s, ← map_mul,
      IsLocalization.mk'_spec, ← IsScalarTower.algebraMap_apply]

/-- **Tex 2747–2748 (PROVED).** `0 ≤ v2 x` iff `x` is regular at `(2)` in RC16's form `RegularAt 2`. -/
theorem v2_nonneg_iff_regularAt (x : FractionRing Lambda) : 0 ≤ v2 x ↔ RegularAt 2 x :=
  (v2_nonneg_iff_mem_range x).trans (mem_range_lambdaTwo_iff_regularAt x)

/-- **Tex 2747–2748, 4977–4978 (PROVED).** `0 ≤ v2 x` iff `x` lies in RC16's genuine localization
`Λ_𝔭`, `𝔭 = (2)` (`RegularAtPrime`). -/
theorem v2_nonneg_iff_regularAtPrime (x : FractionRing Lambda) :
    0 ≤ v2 x ↔ RegularAtPrime (Ideal.span {(2 : Lambda)}) x := by
  rw [v2_nonneg_iff_regularAt, RegularAtPrime, mem_range_atPrime_iff]
  rfl

/-- **Tex 2747–2748, 7607–7609 (PROVED).** `2ᵏ ∣ f` in `Λ = ℤ₂[[t]]` iff `2ᵏ` divides every
coefficient of `f` (generalizes RC16's `two_dvd_iff_forall_coeff`, the case `k = 1`). -/
theorem two_pow_dvd_iff_forall_coeff (k : ℕ) (f : Lambda) :
    (2 : Lambda) ^ k ∣ f ↔ ∀ n : ℕ, (2 : ℤ_[2]) ^ k ∣ PowerSeries.coeff n f := by
  have h2 : (2 : Lambda) ^ k = PowerSeries.C ((2 : ℤ_[2]) ^ k) := by
    rw [map_pow, map_ofNat]
  constructor
  · rintro ⟨g, rfl⟩ n
    exact ⟨PowerSeries.coeff n g, by rw [h2, PowerSeries.coeff_C_mul]⟩
  · intro h
    choose g hg using h
    refine ⟨PowerSeries.mk g, PowerSeries.ext fun n => ?_⟩
    rw [h2, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hg n]

/-- **Tex 2747–2748 (PROVED).** For `f ∈ Λ`, divisibility by `2ᵏ` in `Λ_{(2)}` is divisibility in `Λ`
(`2` is prime in `Λ`). -/
theorem two_pow_dvd_algebraMap_lambdaTwo_iff (k : ℕ) (f : Lambda) :
    (2 : LambdaTwo) ^ k ∣ algebraMap Lambda LambdaTwo f ↔ (2 : Lambda) ^ k ∣ f := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨⟨b, s⟩, hys⟩ := IsLocalization.surj (Ideal.span {(2 : Lambda)}).primeCompl y
    have hfs : f * (s : Lambda) = 2 ^ k * b := by
      apply algebraMap_lambdaTwo_injective
      rw [map_mul, map_mul, map_pow, map_ofNat, hy, mul_assoc, hys]
    have hs2 : ¬ (2 : Lambda) ∣ (s : Lambda) := fun h =>
      s.2 (Ideal.mem_span_singleton.mpr h)
    exact Prime.pow_dvd_of_dvd_mul_right prime_two_lambda k hs2 ⟨b, hfs⟩
  · rintro ⟨g, rfl⟩
    exact ⟨algebraMap Lambda LambdaTwo g, by rw [map_mul, map_pow, map_ofNat]⟩

/-- **Tex 2747–2748 (PROVED).** On `Λ`, `k ≤ v2 f` iff `2ᵏ ∣ f`. -/
theorem le_v2_iff_two_pow_dvd (k : ℕ) (f : Lambda) :
    ((k : ℤ) : WithTop ℤ) ≤ v2 (algebraMap Lambda (FractionRing Lambda) f) ↔ (2 : Lambda) ^ k ∣ f := by
  rw [IsScalarTower.algebraMap_apply Lambda LambdaTwo (FractionRing Lambda), v2,
    ← pow_dvd_iff_le_dvrAddVal irreducible_two_lambdaTwo k, two_pow_dvd_algebraMap_lambdaTwo_iff]

/-- **The Gauss form of `v2` on `Λ`** (tex 2747–2748, 7607–7609; `PROVED`): `k ≤ v2 f` iff `2ᵏ`
divides every power-series coefficient of `f`; i.e. `v2 f = min_n v₂(coeff_n f)`. -/
theorem le_v2_iff_forall_coeff (k : ℕ) (f : Lambda) :
    ((k : ℤ) : WithTop ℤ) ≤ v2 (algebraMap Lambda (FractionRing Lambda) f) ↔
      ∀ n : ℕ, (2 : ℤ_[2]) ^ k ∣ PowerSeries.coeff n f := by
  rw [le_v2_iff_two_pow_dvd, two_pow_dvd_iff_forall_coeff]

/-- **Tex 2747–2748 (PROVED).** `v2 (2ⁿ b) = n` for `b ∈ Λ` with `2 ∤ b`. -/
theorem v2_algebraMap_two_pow_mul (n : ℕ) {b : Lambda} (hb : ¬ (2 : Lambda) ∣ b) :
    v2 (algebraMap Lambda (FractionRing Lambda) (2 ^ n * b)) = (n : ℤ) := by
  have hbP : b ∈ (Ideal.span {(2 : Lambda)}).primeCompl := by
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]
    exact hb
  have hbu : IsUnit (algebraMap Lambda LambdaTwo b) :=
    IsLocalization.map_units LambdaTwo (⟨b, hbP⟩ : (Ideal.span {(2 : Lambda)}).primeCompl)
  have h := dvrAddVal_algebraMap_pow_mul_unit (K := FractionRing Lambda) irreducible_two_lambdaTwo n
    hbu.unit
  have key : algebraMap Lambda (FractionRing Lambda) (2 ^ n * b) =
      algebraMap LambdaTwo (FractionRing Lambda) (2 ^ n * ↑hbu.unit) := by
    rw [IsUnit.unit_spec, IsScalarTower.algebraMap_apply Lambda LambdaTwo (FractionRing Lambda),
      map_mul, map_pow, map_ofNat]
  rw [key]
  exact h

/-- **Tex 2747–2748 (PROVED).** Every nonzero `f ∈ Λ` is `2ⁿ b` with `2 ∤ b`, and then
`v2 f = n`. -/
theorem exists_v2_eq (f : Lambda) (hf : f ≠ 0) :
    ∃ (n : ℕ) (b : Lambda), ¬ (2 : Lambda) ∣ b ∧ f = 2 ^ n * b ∧
      v2 (algebraMap Lambda (FractionRing Lambda) f) = (n : ℤ) := by
  obtain ⟨n, b, hb, rfl⟩ := exists_eq_pow_mul_not_dvd prime_two_lambda hf
  exact ⟨n, b, hb, rfl, v2_algebraMap_two_pow_mul n hb⟩

/-- Non-vacuity: `v2 t = 0` (`t ∉ (2)`) and `v2 (1/2) = -1`. -/
example : v2 (algebraMap Lambda (FractionRing Lambda) PowerSeries.X) = (0 : ℤ) ∧
    v2 ((2 : FractionRing Lambda)⁻¹) = (-1 : ℤ) := by
  constructor
  · have hX : ¬ (2 : Lambda) ∣ PowerSeries.X := by
      intro h
      have h1 := (two_dvd_iff_forall_coeff PowerSeries.X).mp h 1
      simp only [PowerSeries.coeff_X, ↓reduceIte] at h1
      obtain ⟨c, hc⟩ := h1
      have h2 := congrArg (PadicInt.toZMod (p := 2)) hc
      rw [map_one, map_mul, map_ofNat, show (2 : ZMod 2) = 0 from rfl, zero_mul] at h2
      exact one_ne_zero h2
    have h := v2_algebraMap_two_pow_mul 0 hX
    rwa [pow_zero, one_mul] at h
  · rw [AddValuation.map_inv, v2_two]
    rfl

end ZInQ.Manuscript.RC.Rings
