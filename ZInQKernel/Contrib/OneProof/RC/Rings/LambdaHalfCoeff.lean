import ZInQKernel.Contrib.OneProof.RC.Uniform.BlueprintBridge
import ZInQKernel.Contrib.OneProof.RC.Uniform.LambdaHalf
import ZInQKernel.Contrib.OneProof.RC.Determinant.Genuine

/-!
# Coefficients of `Λ[1/2]`, the map `Λ[1/2] → Frac 𝒪`, and `A ∩ 𝒪 = Λ` (Lane RC20)

Manuscript `diophantine_zq.tex` (11/5 version). Put `Λ = ℤ₂[[t]]` and `𝒪 = (Λ_(2))^`
(tex 2747–2748); `A = Λ[1/2]` (tex 6841). Here `Λ[1/2]` is the genuine localization
`Uniform.LambdaHalf = Localization.Away (2 : Λ)` of lane RC16, and `𝒪` is the genuine
`Determinant.OO = lim_n (ℤ/2ⁿ)((t))` of lane RC7.

1. **Coefficients.** `halfToPowerSeries : Λ[1/2] →+* ℚ₂[[t]]` (injective) and
   `coeffHalf u j = [tʲ] u ∈ ℚ₂`. The coefficient sequence of every `u ∈ Λ[1/2]` satisfies RC16's
   `CoeffsInLambdaHalf` and has bounded denominators (tex 5492–5497, 4916), and conversely
   `Λ[1/2]` is exactly the ring of `ℚ₂`-power series with bounded denominators
   (`mem_range_halfToPowerSeries_iff`). The constant coefficient is the central specialization
   (`coeffHalf_zero_eq_centralSpecialization`).
2. **`Λ[1/2] → Frac 𝒪`.** `halfToFracO` (injective), with `halfToFracO u = uK e g` whenever
   `u · 2^e = g`; the wiring lemmas `exists_coeffHalf_uK` and `exists_coeffHalf_uK_family` produce
   exactly lane RC7's hypothesis `hu` of `clearing_nodes_genuine` for `C.u x := coeffHalf (ũ x)`;
   "no negative powers of `t`" (tex 5703–5704).
3. **(E.5)** `A ∩ 𝒪 = Λ` (tex 7600–7609): `halfToFracO_mem_range_iff`, its corollary for
   `2^c u`, and the coefficientwise intersection in the group basis of `A[G]`
   (`exists_map_eq_two_pow_smul`, `map_mem_range_map_iff`).

Everything in this file is `PROVED`; no `GLUE` and no `ELLIOT` statement.

DEPARTURES (form). Exponents of `2` are natural numbers (a larger exponent is always allowed).
In (E.5) the group ring `R[G]` is Mathlib's `MonoidAlgebra R G` for an arbitrary type `G`, and
"`2^{c} u^ev ∈ 𝒪[G]`" is read coefficientwise in the group basis (the manuscript's "coefficientwise
intersection in the original group basis"); the ring-homomorphism form needs a monoid `G`.
-/

namespace ZInQ.Manuscript.RC.Rings

open ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Determinant

/-! ## 1. Coefficient extraction on `Λ[1/2]` -/

/-- The coefficientwise inclusion `Λ = ℤ₂[[t]] → ℚ₂[[t]]`. -/
noncomputable def lambdaToPowerSeries : Lambda →+* PowerSeries ℚ_[2] :=
  PowerSeries.map PadicInt.Coe.ringHom

/-- `2` is a unit of `ℚ₂[[t]]` (`PROVED`; tex 6841: `A = Λ[1/2]` embeds in `ℚ₂[[t]]`). -/
theorem isUnit_lambdaToPowerSeries_two : IsUnit (lambdaToPowerSeries (2 : Lambda)) := by
  rw [map_ofNat, PowerSeries.isUnit_iff_constantCoeff, map_ofNat]
  exact isUnit_iff_ne_zero.mpr two_ne_zero

/-- The coefficient map `Λ[1/2] → ℚ₂[[t]]`: the `IsLocalization.Away.lift` of the coefficientwise
inclusion `ℤ₂[[t]] → ℚ₂[[t]]` (`2` is a unit of `ℚ₂[[t]]`). -/
noncomputable def halfToPowerSeries : LambdaHalf →+* PowerSeries ℚ_[2] :=
  IsLocalization.Away.lift (2 : Lambda) isUnit_lambdaToPowerSeries_two

/-- On `Λ ⊂ Λ[1/2]`, `halfToPowerSeries` is the coefficientwise inclusion (`PROVED`;
tex 2747–2748, 6841). -/
@[simp]
theorem halfToPowerSeries_algebraMap (f : Lambda) :
    halfToPowerSeries (algebraMap Lambda LambdaHalf f) = PowerSeries.map PadicInt.Coe.ringHom f :=
  IsLocalization.Away.lift_eq _ _ f

/-- `Λ → Λ[1/2]` is injective (`PROVED`; tex 6841, 7600): `2` is a nonzero divisor of the domain
`Λ`. -/
theorem algebraMap_lambdaHalf_injective : Function.Injective (algebraMap Lambda LambdaHalf) :=
  IsLocalization.injective LambdaHalf
    (powers_le_nonZeroDivisors_of_noZeroDivisors prime_two_lambda.ne_zero)

/-- `2` is a unit of `Λ[1/2]` (`PROVED`; tex 6841). -/
theorem isUnit_two_lambdaHalf : IsUnit (2 : LambdaHalf) := by
  have := IsLocalization.Away.algebraMap_isUnit (S := LambdaHalf) (2 : Lambda)
  rwa [map_ofNat] at this

/-- **`Λ[1/2] ⊂ ℚ₂[[t]]`** (tex 6841, 7607–7608; `PROVED`): the coefficient map is injective, so an
element of `A = Λ[1/2]` is determined by its power-series coefficients. -/
theorem halfToPowerSeries_injective : Function.Injective halfToPowerSeries := by
  refine (IsLocalization.lift_injective_iff _).mpr fun x y => ⟨fun h => ?_, fun h => ?_⟩
  · rw [algebraMap_lambdaHalf_injective h]
  · exact congrArg _ (PowerSeries.map_injective _ (fun a b hab => PadicInt.ext hab) h)

/-- The `tʲ`-coefficient `[tʲ] u ∈ ℚ₂` of `u ∈ Λ[1/2]` (tex 5492–5497: the top layer records `ũ_x`
by these coefficients). -/
noncomputable def coeffHalf (u : LambdaHalf) (j : ℕ) : ℚ_[2] :=
  PowerSeries.coeff j (halfToPowerSeries u)

/-- On `Λ ⊂ Λ[1/2]` the coefficients are the `ℤ₂`-coefficients (`PROVED`; tex 2747–2748). -/
@[simp]
theorem coeffHalf_algebraMap (f : Lambda) (j : ℕ) :
    coeffHalf (algebraMap Lambda LambdaHalf f) j = ((PowerSeries.coeff j f : ℤ_[2]) : ℚ_[2]) := by
  rw [coeffHalf, halfToPowerSeries_algebraMap, PowerSeries.coeff_map]
  rfl

/-- Coefficients of `u` and `u · 2^e = g` (`PROVED`; tex 5492–5497): `[tʲ]u · 2^e = [tʲ]g`. -/
theorem coeffHalf_mul_two_pow_of_mul {u : LambdaHalf} {e : ℕ} {g : Lambda}
    (h : u * algebraMap Lambda LambdaHalf (2 ^ e) = algebraMap Lambda LambdaHalf g) (j : ℕ) :
    coeffHalf u j * (2 : ℚ_[2]) ^ e = ((PowerSeries.coeff j g : ℤ_[2]) : ℚ_[2]) := by
  have h1 := congrArg (fun v => coeffHalf v j) h
  simp only [coeffHalf_algebraMap] at h1
  rw [← h1, coeffHalf, coeffHalf, map_mul, halfToPowerSeries_algebraMap, map_pow, map_ofNat,
    show (2 : PowerSeries ℚ_[2]) ^ e = PowerSeries.C ((2 : ℚ_[2]) ^ e) by
      rw [map_pow, map_ofNat], PowerSeries.coeff_mul_C]

/-- **Coefficients of `g / 2^e`** (`PROVED`; tex 5492–5497): if `u · 2^e = g` with `g ∈ Λ`, then
`[tʲ]u = [tʲ]g / 2^e`. -/
theorem coeffHalf_eq_of_mul_two_pow {u : LambdaHalf} {e : ℕ} {g : Lambda}
    (h : u * algebraMap Lambda LambdaHalf (2 ^ e) = algebraMap Lambda LambdaHalf g) (j : ℕ) :
    coeffHalf u j = ((PowerSeries.coeff j g : ℤ_[2]) : ℚ_[2]) / 2 ^ e := by
  rw [← coeffHalf_mul_two_pow_of_mul h j, mul_div_cancel_right₀ _ (pow_ne_zero _ two_ne_zero)]

/-- **`ũ ∈ Λ[1/2]` in coefficient form** (`PROVED`; tex 5492–5497, 5703–5704): the coefficient
sequence of every `u ∈ Λ[1/2]` satisfies RC16's `CoeffsInLambdaHalf`. -/
theorem coeffsInLambdaHalf_coeffHalf (u : LambdaHalf) : CoeffsInLambdaHalf (coeffHalf u) := by
  obtain ⟨f, m, hf⟩ := exists_mul_two_pow_eq u
  exact ⟨f, m, coeffHalf_mul_two_pow_of_mul hf⟩

/-- **Bounded denominators** (`PROVED`; tex 4916, 5492–5497, 7607–7608: "an element of `A` has
bounded powers of two as denominators in its power-series coefficients"). -/
theorem coeffHalf_bounded (u : LambdaHalf) : ∃ e : ℕ, ∀ j, ‖coeffHalf u j‖ ≤ (2 : ℝ) ^ e :=
  norm_le_of_coeffsInLambdaHalf (coeffsInLambdaHalf_coeffHalf u)

/-- **`CoeffsInLambdaHalf` is exactly the coefficient sequences of `Λ[1/2]`** (`PROVED`;
tex 5492–5497, 6841): RC16's coefficient predicate holds for `c` iff `c` is the coefficient
sequence of some genuine `u ∈ Λ[1/2]`. -/
theorem coeffsInLambdaHalf_iff (c : ℕ → ℚ_[2]) :
    CoeffsInLambdaHalf c ↔ ∃ u : LambdaHalf, ∀ j, c j = coeffHalf u j := by
  constructor
  · rintro ⟨a, m, ha⟩
    refine ⟨IsLocalization.mk' LambdaHalf a (⟨2 ^ m, m, rfl⟩ : Submonoid.powers (2 : Lambda)),
      fun j => ?_⟩
    have hspec := IsLocalization.mk'_spec LambdaHalf a
      (⟨2 ^ m, m, rfl⟩ : Submonoid.powers (2 : Lambda))
    have h1 := coeffHalf_mul_two_pow_of_mul hspec j
    rw [← ha j] at h1
    exact (mul_right_cancel₀ (pow_ne_zero _ two_ne_zero) h1).symm
  · rintro ⟨u, hu⟩
    have : c = coeffHalf u := funext hu
    rw [this]
    exact coeffsInLambdaHalf_coeffHalf u

/-- `‖2‖ = 1/2` in `ℚ₂` (`PROVED`; helper for tex 4916, 7607–7608). -/
theorem norm_two_padic : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
  have := Padic.norm_p (p := 2)
  exact_mod_cast this

/-- **`Λ[1/2]` is the ring of `ℚ₂`-power series with bounded denominators** (`PROVED`;
tex 4916, 6841, 7607–7608): `f ∈ ℚ₂[[t]]` lies in the image of `Λ[1/2]` iff
`∃ e, ∀ j, ‖[tʲ]f‖ ≤ 2^e`. -/
theorem mem_range_halfToPowerSeries_iff (f : PowerSeries ℚ_[2]) :
    f ∈ halfToPowerSeries.range ↔ ∃ e : ℕ, ∀ j, ‖PowerSeries.coeff j f‖ ≤ (2 : ℝ) ^ e := by
  constructor
  · rintro ⟨u, rfl⟩
    exact coeffHalf_bounded u
  · rintro ⟨e, he⟩
    have hint : ∀ j, ‖(2 : ℚ_[2]) ^ e * PowerSeries.coeff j f‖ ≤ 1 := by
      intro j
      rw [norm_mul, norm_pow, norm_two_padic, inv_pow]
      have hpos : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
      calc ((2 : ℝ) ^ e)⁻¹ * ‖PowerSeries.coeff j f‖ ≤ ((2 : ℝ) ^ e)⁻¹ * (2 : ℝ) ^ e := by
            gcongr; exact he j
        _ = 1 := inv_mul_cancel₀ hpos.ne'
    have hz : ∀ j, ∃ z : ℤ_[2], (z : ℚ_[2]) = (2 : ℚ_[2]) ^ e * PowerSeries.coeff j f :=
      fun j => ⟨⟨_, by exact hint j⟩, rfl⟩
    choose z hz using hz
    have hc : CoeffsInLambdaHalf fun j => PowerSeries.coeff j f := by
      refine ⟨PowerSeries.mk z, e, fun j => ?_⟩
      rw [PowerSeries.coeff_mk, hz j, mul_comm]
    obtain ⟨u, hu⟩ := (coeffsInLambdaHalf_iff _).mp hc
    exact ⟨u, PowerSeries.ext fun j => (hu j).symm⟩

/-- **The constant coefficient is the central specialization** (`PROVED`; tex 4914–4920,
5703–5706): `[t⁰]u = u(0)`, the specialization `t ↦ 0` of RC16; this is the top layer's
`u x 0 = ũ_x(0)`. -/
theorem coeffHalf_zero_eq_centralSpecialization (u : LambdaHalf) :
    coeffHalf u 0 = centralSpecialization u := by
  have key : (PowerSeries.constantCoeff.comp halfToPowerSeries : LambdaHalf →+* ℚ_[2]) =
      centralSpecialization := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (2 : Lambda)) ?_
    ext f
    · simp only [RingHom.comp_apply, halfToPowerSeries_algebraMap, centralSpecialization_algebraMap]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      rfl
  rw [coeffHalf, PowerSeries.coeff_zero_eq_constantCoeff_apply, ← key]
  rfl

/-! ## 2. The map `Λ[1/2] → Frac 𝒪` -/

/-- The composite `Λ → 𝒪 → Frac 𝒪`. -/
noncomputable def lambdaToFracO : Lambda →+* FractionRing OO :=
  (algebraMap OO (FractionRing OO)).comp lamToO

/-- `2` is a unit of `Frac 𝒪` (`PROVED`; tex 4830: `𝒪` has two-adic valuation). -/
theorem isUnit_lambdaToFracO_two : IsUnit (lambdaToFracO (2 : Lambda)) := by
  rw [map_ofNat]
  refine isUnit_iff_ne_zero.mpr fun h => ?_
  have h2 : (2 : OO) ≠ 0 := by simpa using two_pow_ne_zero_OO 1
  apply h2
  apply IsFractionRing.injective OO (FractionRing OO)
  rw [map_ofNat, map_zero]
  exact h

/-- The canonical map `Λ[1/2] → Frac 𝒪`: the `IsLocalization.Away.lift` of
`Λ → 𝒪 → Frac 𝒪` (`2` is a unit of `Frac 𝒪`). -/
noncomputable def halfToFracO : LambdaHalf →+* FractionRing OO :=
  IsLocalization.Away.lift (2 : Lambda) isUnit_lambdaToFracO_two

/-- On `Λ ⊂ Λ[1/2]`, `halfToFracO` is `Λ → 𝒪 → Frac 𝒪` (`PROVED`; tex 2747–2748). -/
@[simp]
theorem halfToFracO_algebraMap (f : Lambda) :
    halfToFracO (algebraMap Lambda LambdaHalf f) = algebraMap OO (FractionRing OO) (lamToO f) :=
  IsLocalization.Away.lift_eq _ _ f

/-- **`Λ[1/2] ⊂ Frac 𝒪`** (`PROVED`; tex 4916, 5698–5705, 7600): the canonical map is injective, so
`v_𝒪` on `Λ[1/2]` and the intersection `A ∩ 𝒪` make sense inside `Frac 𝒪`. -/
theorem halfToFracO_injective : Function.Injective halfToFracO := by
  refine (IsLocalization.lift_injective_iff _).mpr fun x y => ⟨fun h => ?_, fun h => ?_⟩
  · rw [algebraMap_lambdaHalf_injective h]
  · exact congrArg _ (lamToO_injective (IsFractionRing.injective OO (FractionRing OO) h))

/-- **`halfToFracO` is RC7's `uK`** (`PROVED`; tex 5492–5497, 5698–5705): if `u · 2^e = g` with
`g ∈ Λ`, then the image of `u` in `Frac 𝒪` is `uK e g = g / 2^e`. -/
theorem halfToFracO_eq_uK {u : LambdaHalf} {e : ℕ} {g : Lambda}
    (h : u * algebraMap Lambda LambdaHalf (2 ^ e) = algebraMap Lambda LambdaHalf g) :
    halfToFracO u = uK (O := OO) e g := by
  have h1 := congrArg halfToFracO h
  rw [map_mul, halfToFracO_algebraMap, halfToFracO_algebraMap, map_pow, map_pow, map_ofNat,
    map_ofNat] at h1
  have h2 : (2 : FractionRing OO) ^ e ≠ 0 := by
    have := isUnit_lambdaToFracO_two
    rw [map_ofNat] at this
    exact pow_ne_zero _ this.ne_zero
  rw [uK, eq_div_iff h2, h1]
  rfl

/-- **Wiring for RC7's `hu`** (`PROVED`; tex 5492–5497, 5698–5705): every `u ∈ Λ[1/2]` is
`g / 2^e` with `g ∈ Λ`, simultaneously in coefficient form (`[tʲ]u = [tʲ]g / 2^e`, the form of
RC7's hypothesis `hu` of `clearing_nodes_genuine`) and in `Frac 𝒪` (`halfToFracO u = uK e g`, the
form of its hypotheses `hrank`, `hacyc`). -/
theorem exists_coeffHalf_uK (u : LambdaHalf) :
    ∃ (e : ℕ) (g : Lambda),
      (∀ j, coeffHalf u j = ((PowerSeries.coeff j g : ℤ_[2]) : ℚ_[2]) / 2 ^ e) ∧
        halfToFracO u = uK (O := OO) e g := by
  obtain ⟨g, e, h⟩ := exists_mul_two_pow_eq u
  exact ⟨e, g, coeffHalf_eq_of_mul_two_pow h, halfToFracO_eq_uK h⟩

/-- **Wiring for RC7's `hu`, family version** (`PROVED`; tex 5492–5497, 5698–5705): for any family
`ũ : ι → Λ[1/2]` (e.g. `ι = Addr b`, the corrected coordinates `ũ_x`) there are `e x`, `g x` with
`coeffHalf (ũ x) j = [tʲ](g x) / 2^{e x}` for all `x, j` — exactly RC7's hypothesis `hu` for
`u := fun x j => coeffHalf (ũ x) j` — and `halfToFracO (ũ x) = uK (e x) (g x)`. -/
theorem exists_coeffHalf_uK_family {ι : Type*} (ũ : ι → LambdaHalf) :
    ∃ (e : ι → ℕ) (g : ι → Lambda),
      (∀ x j, coeffHalf (ũ x) j = ((PowerSeries.coeff j (g x) : ℤ_[2]) : ℚ_[2]) / 2 ^ e x) ∧
        ∀ x, halfToFracO (ũ x) = uK (O := OO) (e x) (g x) := by
  choose e g h using fun x => exists_coeffHalf_uK (ũ x)
  exact ⟨e, g, fun x => (h x).1, fun x => (h x).2⟩

/-- **No negative powers of `t`** (`PROVED`; tex 5703–5704: "Both `ũ_x` and `ũ_0` lie in `Λ[1/2]`
... so neither has negative powers of `t`"): the numerator `g ∈ Λ` of `u = g / 2^e` has vanishing
Laurent coefficients `[tⁱ] g = 0` in `𝒪` for `i < 0`. -/
theorem coeffZ_lamToO_neg (g : Lambda) {i : ℤ} (hi : i < 0) : coeffZ (lamToO g) i = 0 := by
  rw [← algebraMap_eq_lamToO, coeffZ_algebraMap]
  simp [show ¬ (0 ≤ i) by omega]

/-- **No negative powers of `t`, for `u ∈ Λ[1/2]`** (`PROVED`; tex 5703–5706): every `u ∈ Λ[1/2]`
is `g / 2^e` in `Frac 𝒪` with `g ∈ Λ` having no negative Laurent coefficients, and the
constant coefficient of `g` is `2^e u(0)`. -/
theorem exists_noNegativePowers (u : LambdaHalf) :
    ∃ (e : ℕ) (g : Lambda), halfToFracO u = uK (O := OO) e g ∧
      (∀ i : ℤ, i < 0 → coeffZ (lamToO g) i = 0) ∧
      ((coeffZ (lamToO g) 0 : ℤ_[2]) : ℚ_[2]) = 2 ^ e * centralSpecialization u := by
  obtain ⟨g, e, h⟩ := exists_mul_two_pow_eq u
  refine ⟨e, g, halfToFracO_eq_uK h, fun i hi => coeffZ_lamToO_neg g hi, ?_⟩
  rw [← algebraMap_eq_lamToO, coeffZ_algebraMap]
  simp only [le_refl, ↓reduceIte, Int.toNat_zero]
  rw [← coeffHalf_mul_two_pow_of_mul h,
    coeffHalf_zero_eq_centralSpecialization, mul_comm]

/-! ## 3. (E.5): `A ∩ 𝒪 = Λ` -/

/-- **(E.5) `A ∩ 𝒪 = Λ`** (`PROVED`; tex 7600–7609, with `A = Λ[1/2]`, tex 6841): an element of
`Λ[1/2]` whose image in `Frac 𝒪` lies in `𝒪` lies in `Λ`, and conversely.

Elliot's coefficientwise argument: write `u = g / 2^e` (bounded denominators); if `g / 2^e = y ∈ 𝒪`
then `g = 2^e y` in `𝒪`, so `g ≡ 0 (mod 2^e 𝒪)`, i.e. its reduction in `(ℤ/2^e)((t))` vanishes,
so `2^e` divides every coefficient of `g` ("membership in `𝒪` makes their minimum valuation
nonnegative"), so `g = 2^e g'` with `g' ∈ Λ` and `u = g'`. -/
theorem halfToFracO_mem_range_iff (u : LambdaHalf) :
    halfToFracO u ∈ (algebraMap OO (FractionRing OO)).range ↔
      u ∈ (algebraMap Lambda LambdaHalf).range := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨g, e, h⟩ := exists_mul_two_pow_eq u
    have h1 : algebraMap OO (FractionRing OO) (y * 2 ^ e) =
        algebraMap OO (FractionRing OO) (lamToO g) := by
      rw [map_mul, hy, ← halfToFracO_algebraMap, ← h, map_mul, halfToFracO_algebraMap,
        map_pow lamToO, map_ofNat lamToO]
    have h2 : lamToO g = 2 ^ e * y := by
      rw [mul_comm]; exact (IsFractionRing.injective OO (FractionRing OO) h1).symm
    have hdvd : ∀ j : ℕ, (2 : ℤ_[2]) ^ e ∣ PowerSeries.coeff j g := by
      intro j
      have h3 : (proj e (lamToO g)).coeff (j : ℤ) = 0 := by
        rw [h2, proj_two_pow_mul, HahnSeries.coeff_zero]
      rw [coeff_proj_eq_zero_iff, ← algebraMap_eq_lamToO, coeffZ_algebraMap] at h3
      simpa using h3
    choose c hc using hdvd
    refine ⟨PowerSeries.mk c, ?_⟩
    have hg : g = 2 ^ e * PowerSeries.mk c := by
      refine PowerSeries.ext fun j => ?_
      rw [show (2 : Lambda) ^ e = PowerSeries.C ((2 : ℤ_[2]) ^ e) by rw [map_pow, map_ofNat],
        PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc j]
    have h' : algebraMap Lambda LambdaHalf (2 ^ e) * algebraMap Lambda LambdaHalf (PowerSeries.mk c) =
        algebraMap Lambda LambdaHalf (2 ^ e) * u := by
      rw [← map_mul, ← hg, ← h, mul_comm]
    exact (IsLocalization.map_units LambdaHalf
      (⟨2 ^ e, e, rfl⟩ : Submonoid.powers (2 : Lambda))).mul_left_cancel h'
  · rintro ⟨f, rfl⟩
    exact ⟨lamToO f, (halfToFracO_algebraMap f).symm⟩

/-- **(E.5), corollary: `2^c u ∈ 𝒪 ⇒ 2^c u ∈ Λ`** (`PROVED`; tex 7600–7609: "`2^{c_E} u^ev ∈ Λ[G]`
... The coefficientwise intersection retains `c_E`"): for `u ∈ Λ[1/2]`, if `2^c u` (computed in
`Frac 𝒪`) lies in `𝒪`, then `2^c u ∈ Λ`, with the same exponent `c`. -/
theorem two_pow_mul_mem_lambda_of_mem_O (c : ℕ) (u : LambdaHalf)
    (h : (2 : FractionRing OO) ^ c * halfToFracO u ∈ (algebraMap OO (FractionRing OO)).range) :
    (2 : LambdaHalf) ^ c * u ∈ (algebraMap Lambda LambdaHalf).range := by
  rw [← halfToFracO_mem_range_iff, map_mul, map_pow, map_ofNat]
  exact h

/-- **(E.5) in the group basis: `A[G] ∩ 𝒪[G] = Λ[G]`** (`PROVED`; tex 7600–7609: "Coefficientwise
intersection in the original group basis"). For any type `G` (the group of the manuscript is a
finite `2`-group, but nothing is used) and `x ∈ Λ[1/2][G]`: the coefficientwise image of `x` in
`(Frac 𝒪)[G]` lies in `𝒪[G]` iff `x ∈ Λ[G]`. Here `R[G] = MonoidAlgebra R G` and the maps are
`MonoidAlgebra.map` (coefficientwise in the basis `G`). -/
theorem map_mem_range_map_iff {G : Type*} (x : MonoidAlgebra LambdaHalf G) :
    MonoidAlgebra.map halfToFracO.toAddMonoidHom x ∈
        Set.range (MonoidAlgebra.map (algebraMap OO (FractionRing OO)).toAddMonoidHom) ↔
      x ∈ Set.range (MonoidAlgebra.map (algebraMap Lambda LambdaHalf).toAddMonoidHom) := by
  rw [MonoidAlgebra.range_map, MonoidAlgebra.range_map]
  simp only [Set.mem_ofPred_eq, MonoidAlgebra.coeff_map, Finsupp.mapRange_apply]
  refine forall_congr' fun i => ?_
  have := halfToFracO_mem_range_iff (x.coeff i)
  simp only [RingHom.mem_range] at this
  exact this

/-- **(E.5) in the group basis, ring-homomorphism form** (`PROVED`; tex 7501, 7600–7609): for a
monoid `G`, `A[G] ∩ 𝒪[G] = Λ[G]` inside `(Frac 𝒪)[G]`, with the ring maps
`MonoidAlgebra.mapRingHom`. -/
theorem mapRingHom_mem_range_iff {G : Type*} [Monoid G] (x : MonoidAlgebra LambdaHalf G) :
    MonoidAlgebra.mapRingHom G halfToFracO x ∈
        (MonoidAlgebra.mapRingHom G (algebraMap OO (FractionRing OO))).range ↔
      x ∈ (MonoidAlgebra.mapRingHom G (algebraMap Lambda LambdaHalf)).range := by
  simp only [RingHom.mem_range, MonoidAlgebra.coe_mapRingHom]
  exact map_mem_range_map_iff x

/-- **(E.5): `2^{c} u^ev ∈ 𝒪[G] ⇒ 2^{c} u^ev ∈ Λ[G]`** (`PROVED`; tex 7600–7609): for any type `G`
and `U ∈ Λ[1/2][G]`, if every group-basis coefficient of `2^c U` maps into `𝒪`, then there is
`V ∈ Λ[G]` whose coefficientwise image in `Λ[1/2][G]` is `2^c • U`; the exponent `c` is retained
("without a term `v₂|G|`"). `V` is unique (`MonoidAlgebra.map_injective`, `Λ → Λ[1/2]`
injective). -/
theorem exists_map_eq_two_pow_smul {G : Type*} (c : ℕ) (U : MonoidAlgebra LambdaHalf G)
    (h : ∀ g, halfToFracO ((2 : LambdaHalf) ^ c * U.coeff g) ∈
      (algebraMap OO (FractionRing OO)).range) :
    ∃ V : MonoidAlgebra Lambda G,
      MonoidAlgebra.map (algebraMap Lambda LambdaHalf).toAddMonoidHom V = (2 : LambdaHalf) ^ c • U := by
  have hmem : (2 : LambdaHalf) ^ c • U ∈
      Set.range (MonoidAlgebra.map (algebraMap Lambda LambdaHalf).toAddMonoidHom) := by
    rw [← map_mem_range_map_iff, MonoidAlgebra.range_map]
    intro i
    obtain ⟨y, hy⟩ := h i
    exact ⟨y, hy⟩
  exact hmem

/-- Uniqueness of the `Λ[G]`-element in `exists_map_eq_two_pow_smul` (`PROVED`; tex 7600–7609):
`Λ[G] → Λ[1/2][G]` is injective. -/
theorem map_lambda_injective {G : Type*} :
    Function.Injective (MonoidAlgebra.map (M := G) (algebraMap Lambda LambdaHalf).toAddMonoidHom) :=
  MonoidAlgebra.map_injective _ algebraMap_lambdaHalf_injective

/-! ## 4. Non-vacuity: `u = 1/2` -/

/-- The element `1/2 ∈ Λ[1/2]`. -/
noncomputable def half : LambdaHalf := IsLocalization.Away.invSelf (2 : Lambda)

/-- `(1/2) · 2 = 1` in `Λ[1/2]` (`PROVED`; non-vacuity for tex 5492–5497, 7600–7609). -/
theorem half_mul_two : half * algebraMap Lambda LambdaHalf (2 ^ 1) = algebraMap Lambda LambdaHalf 1 := by
  rw [pow_one, map_one, mul_comm]
  exact IsLocalization.Away.mul_invSelf (2 : Lambda)

/-- The coefficients of `1/2` (`PROVED`; non-vacuity for tex 5492–5497): `[t⁰](1/2) = 1/2`, all
other coefficients vanish. -/
theorem coeffHalf_half (j : ℕ) : coeffHalf half j = if j = 0 then (2 : ℚ_[2])⁻¹ else 0 := by
  rw [coeffHalf_eq_of_mul_two_pow half_mul_two, PowerSeries.coeff_one, pow_one]
  split_ifs <;> simp

/-- `1/2 ∉ Λ` (`PROVED`; non-vacuity for (E.5), tex 7600–7609). -/
theorem half_not_mem_lambda : half ∉ (algebraMap Lambda LambdaHalf).range := by
  rintro ⟨f, hf⟩
  have h1 : algebraMap Lambda LambdaHalf (2 * f) = algebraMap Lambda LambdaHalf 1 := by
    rw [map_mul, hf, ← half_mul_two, pow_one, mul_comm]
  have h2 : (2 : Lambda) * f = 1 := algebraMap_lambdaHalf_injective h1
  exact prime_two_lambda.not_isUnit (IsUnit.of_mul_eq_one _ h2)

/-- The image of `1/2` in `Frac 𝒪` is not in `𝒪` (`PROVED`; non-vacuity for (E.5),
tex 7600–7609), although `2 · (1/2) ∈ 𝒪`: the exponent `c = 1` of the corollary is needed. -/
theorem halfToFracO_half_not_mem_O :
    halfToFracO half ∉ (algebraMap OO (FractionRing OO)).range ∧
      (2 : FractionRing OO) ^ 1 * halfToFracO half ∈ (algebraMap OO (FractionRing OO)).range := by
  refine ⟨fun h => half_not_mem_lambda ((halfToFracO_mem_range_iff half).mp h), ?_⟩
  refine ⟨1, ?_⟩
  have := congrArg halfToFracO half_mul_two
  rw [map_mul, halfToFracO_algebraMap, halfToFracO_algebraMap, map_pow, map_pow, map_ofNat,
    map_ofNat, map_one, map_one, pow_one] at this
  rw [map_one, pow_one, mul_comm, this]

/-- Non-vacuity of `exists_map_eq_two_pow_smul` (`PROVED`): `U = (1/2)·[g]` with `c = 1`
satisfies its hypothesis, while `U` itself is not in `Λ[G]`. -/
theorem exists_map_eq_two_pow_smul_nonvacuous {G : Type*} (g₀ : G) :
    (∀ g, halfToFracO ((2 : LambdaHalf) ^ 1 * (MonoidAlgebra.single g₀ half).coeff g) ∈
      (algebraMap OO (FractionRing OO)).range) ∧
    MonoidAlgebra.single g₀ half ∉
      Set.range (MonoidAlgebra.map (algebraMap Lambda LambdaHalf).toAddMonoidHom) := by
  classical
  constructor
  · intro g
    rw [map_mul, map_pow, map_ofNat]
    by_cases hg : g = g₀
    · subst hg
      simpa using halfToFracO_half_not_mem_O.2
    · simp [MonoidAlgebra.coeff_single, Ne.symm hg]
  · rintro ⟨V, hV⟩
    apply half_not_mem_lambda
    refine ⟨V.coeff g₀, ?_⟩
    have := congrArg (fun W => W.coeff g₀) hV
    simpa using this

/-- Non-vacuity of `mem_range_halfToPowerSeries_iff` (`PROVED`; tex 7607–7608): the series
`∑ 2^{-j} tʲ ∈ ℚ₂[[t]]` has unbounded denominators, so it is not in `Λ[1/2]`. -/
theorem not_mem_range_halfToPowerSeries_example :
    PowerSeries.mk (fun j => (2 : ℚ_[2])⁻¹ ^ j) ∉ halfToPowerSeries.range := by
  rw [mem_range_halfToPowerSeries_iff]
  rintro ⟨e, he⟩
  have h := he (e + 1)
  rw [PowerSeries.coeff_mk, norm_pow, norm_inv, norm_two_padic, inv_inv] at h
  have : (2 : ℝ) ^ e < 2 ^ (e + 1) := pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self e)
  linarith

/-- Non-vacuity of `coeffHalf_zero_eq_centralSpecialization` and the bounded-denominator bound
(`PROVED`): for `u = 1/2`, `u(0) = 1/2` and `‖[tʲ]u‖ ≤ 2`. -/
example : centralSpecialization half = (2 : ℚ_[2])⁻¹ ∧ ∀ j, ‖coeffHalf half j‖ ≤ (2 : ℝ) ^ 1 := by
  refine ⟨by rw [← coeffHalf_zero_eq_centralSpecialization, coeffHalf_half]; rfl, ?_⟩
  intro j
  rw [coeffHalf_half]
  split_ifs
  · rw [norm_inv, norm_two_padic, inv_inv, pow_one]
  · simp

end ZInQ.Manuscript.RC.Rings
