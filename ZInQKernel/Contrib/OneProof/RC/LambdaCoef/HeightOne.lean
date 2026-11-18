import ZInQKernel.Contrib.OneProof.RC.Uniform.LambdaHalf
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchLeaf
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Collapse

/-!
# The height-one quotients of `Λ = ℤ₂[[t]]`

Lane RC28 (coefficient modules), round 2: the commutative algebra of the height-one fibres of the
switching argument of `diophantine_zq.tex`, paragraph "Height-one regularity, including quadratic
specializations" (tex 4976–5200). There one fixes a height-one prime `𝔭 ≠ (2)` of `Λ = ℤ₂[[t]]`,
puts `R = Λ_𝔭` and `k = Frac(Λ/𝔭)`, and uses that `R` is a DVR and that `k` has characteristic
zero (tex 4977–4980); regularity at every such `𝔭` and the intersection formula for `Λ[1/2]`
close the argument (tex 5190–5194).

For a prime `P` of `Λ` with `P.height = 1` and `P ≠ (2)` this file proves:

1. `finite_quotient`: `Λ/𝔭` is a finite `ℤ₂`-module;
2. `exists_mul_sub_two_pow_mem`: every `s ∉ 𝔭` divides a power of `2` modulo `𝔭`;
3. `exists_X_pow_mem`: for every `N`, a power of `t` lies in `𝔭 + (2^N)`;
4. `isUnit_two_resAt`: `2` is a unit of `k = ResAt P`;
5. `exists_two_pow_mul_eq`: every element of `k` times a power of `2` is the residue of an element
   of `Λ`;
6. `charZero_resAt`, `injective_algebraMap_padicInt`: `k` has characteristic zero and the
   structure map `ℤ₂ → k` is injective;
7. non-vacuity: all of the above at the height-one prime `𝔭 = (t) ≠ (2)`.

Route. `Λ` is a UFD, so `𝔭 = (g)` with `g` prime, and `2 ∤ g` because `𝔭 ≠ (2)`; hence some
coefficient of `g` is a unit of `ℤ₂`. Weierstrass preparation (Washington, *Introduction to
Cyclotomic Fields*, Thm 7.3; in Mathlib `PowerSeries.exists_isWeierstrassFactorization`) writes
`g = f · h` with `f` a distinguished polynomial and `h` a unit, so `𝔭 = (f)` and
`Λ/𝔭 ≅ ℤ₂[t]/(f)`, a finite `ℤ₂`-module since `f` is monic. The domain `Λ/𝔭` is integral over
`ℤ₂`, so every nonzero principal ideal of it meets `ℤ₂ ∖ 0`, whose elements are `2^v` times
units. The non-leading coefficients of `f` lie in `(2)`, so `t^d ∈ (f) + (2)` for `d = deg f`.

Kinds: every theorem is PROVED; the file introduces no definitions and no hypotheses.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.LambdaCoef

open ZInQ.Manuscript.RC.Uniform (Lambda height_eq_one_iff_exists_prime prime_two_lambda
  two_dvd_iff_forall_coeff)
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)
open ZInQ.Manuscript.RC.CoefModules (two_ne_zero_resAt height_span_X span_X_ne_span_two)

/-! ## Units of `ℤ₂` and ring maps out of `ℤ₂` -/

/-- **A nonzero `2`-adic integer is a unit times a power of `2`** (`a = u · 2^v`). Kind: PROVED.
Locator: `diophantine_zq.tex`, the height-one fibres of the switching argument, tex 4976–5200
(the coefficient ring `ℤ₂` of `Λ`). -/
theorem padicInt_exists_unit_mul_two_pow {a : ℤ_[2]} (ha : a ≠ 0) :
    ∃ (u : ℤ_[2]ˣ) (v : ℕ), a = u * 2 ^ v :=
  ⟨_, _, by exact_mod_cast PadicInt.unitCoeff_spec ha⟩

/-- **A ring map out of `ℤ₂` into a nontrivial ring in which `2` is a unit is injective**: a
nonzero `a = u · 2^v` maps to a unit. Kind: PROVED. Locator: `diophantine_zq.tex`, the
height-one fibres of the switching argument, tex 4976–5200 (`k = Frac(Λ/𝔭)` of characteristic
zero, tex 4977–4980). -/
theorem padicInt_ringHom_injective {K : Type*} [Ring K] [Nontrivial K] (φ : ℤ_[2] →+* K)
    (h2 : IsUnit (2 : K)) : Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  obtain ⟨u, v, hu⟩ := padicInt_exists_unit_mul_two_pow ha0
  have hunit : IsUnit (φ a) := by
    rw [hu, map_mul, map_pow, map_ofNat]
    exact (u.isUnit.map φ).mul (h2.pow v)
  exact hunit.ne_zero ha

/-! ## A distinguished generator of a height-one prime `𝔭 ≠ (2)` -/

section HeightOne

variable {P : Ideal Lambda} [P.IsPrime]

/-- **A height-one prime `𝔭 ≠ (2)` of `Λ` is `(g)` with `g` prime and `2 ∤ g`** (`Λ` is a UFD,
`ZInQ.Manuscript.RC.Uniform.height_eq_one_iff_exists_prime`; `2 ∣ g` would force `(g) = (2)`).
Kind: PROVED. Locator: `diophantine_zq.tex`, the height-one fibres of the switching argument,
tex 4976–5200 ("Fix a height-one prime `𝔭 ≠ (2)`"), and tex 5190–5194. -/
theorem exists_prime_eq_span_of_height_one (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) :
    ∃ g : Lambda, Prime g ∧ P = Ideal.span {g} ∧ ¬ (2 : Lambda) ∣ g := by
  obtain ⟨g, hg, hPg⟩ := (height_eq_one_iff_exists_prime P).mp hP
  refine ⟨g, hg, hPg, fun h2 => hne ?_⟩
  rw [hPg]
  exact (Ideal.span_singleton_eq_span_singleton.mpr
    (prime_two_lambda.irreducible.associated_of_dvd hg.irreducible h2)).symm

/-- **A power series not divisible by `2` has nonzero reduction modulo the maximal ideal of
`ℤ₂`**, i.e. some coefficient is a unit (the hypothesis of Weierstrass preparation). Kind: PROVED.
Locator: `diophantine_zq.tex`, the height-one fibres of the switching argument, tex 4976–5200;
Washington, *Introduction to Cyclotomic Fields*, Thm 7.3. -/
theorem map_residue_ne_zero_of_not_two_dvd {g : Lambda} (hg : ¬ (2 : Lambda) ∣ g) :
    PowerSeries.map (IsLocalRing.residue ℤ_[2]) g ≠ 0 := by
  intro h
  apply hg
  rw [two_dvd_iff_forall_coeff]
  intro n
  have h1 := congrArg (PowerSeries.coeff n) h
  rw [PowerSeries.coeff_map, map_zero, IsLocalRing.residue_eq_zero_iff,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
  exact_mod_cast h1

/-- **A height-one prime `𝔭 ≠ (2)` of `Λ` is generated by a distinguished polynomial**: by
Weierstrass preparation `g = f · h` with `f ∈ ℤ₂[t]` distinguished (monic, non-leading coefficients
in `(2)`) and `h` a unit, so `𝔭 = (g) = (f)`. Kind: PROVED. Locator: `diophantine_zq.tex`, the
height-one fibres of the switching argument, tex 4976–5200; Washington, *Introduction to
Cyclotomic Fields*, Thm 7.3. -/
theorem exists_distinguished_eq_span_of_height_one (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) :
    ∃ f : Polynomial ℤ_[2], f.IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[2]) ∧
      P = Ideal.span {(f : Lambda)} := by
  obtain ⟨g, -, hPg, h2⟩ := exists_prime_eq_span_of_height_one hP hne
  obtain ⟨f, h, H⟩ :=
    PowerSeries.exists_isWeierstrassFactorization (map_residue_ne_zero_of_not_two_dvd h2)
  refine ⟨f, H.isDistinguishedAt, ?_⟩
  rw [hPg, H.eq_mul, Ideal.span_singleton_mul_right_unit H.isUnit]

/-! ## 1. `Λ/𝔭` is a finite `ℤ₂`-module -/

/-- **Item 1: `Λ/𝔭` is a finite `ℤ₂`-module** for a height-one prime `𝔭 ≠ (2)`: with `𝔭 = (f)`,
`f` distinguished, `Λ/𝔭 ≅ ℤ₂[t]/(f)` (Mathlib's `Polynomial.IsDistinguishedAt.algEquivQuotient`),
which is finite because `f` is monic. Kind: PROVED. Locator: `diophantine_zq.tex`, the height-one
fibres of the switching argument, tex 4976–5200 (`R = Λ_𝔭`, `k = Frac(Λ/𝔭)`), and tex 5190–5194;
Washington, *Introduction to Cyclotomic Fields*, Thm 7.3. -/
theorem finite_quotient (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) :
    Module.Finite ℤ_[2] (Lambda ⧸ P) := by
  obtain ⟨f, hf, rfl⟩ := exists_distinguished_eq_span_of_height_one hP hne
  have := hf.monic.finite_quotient
  exact Module.Finite.equiv hf.algEquivQuotient.toLinearEquiv

/-! ## 2. Elements outside `𝔭` divide powers of `2` modulo `𝔭` -/

/-- **Item 2: every `s ∉ 𝔭` divides a power of `2` modulo `𝔭`**: `s · μ - 2^j ∈ 𝔭`. The domain
`Λ/𝔭` is integral over `ℤ₂` (`finite_quotient`), so the nonzero ideal `(s̄)` contains a nonzero
`a ∈ ℤ₂`, and `a = u · 2^j` with `u` a unit. Kind: PROVED. Locator: `diophantine_zq.tex`, the
height-one fibres of the switching argument, tex 4976–5200 (`R = Λ_𝔭`), and tex 5190–5194. -/
theorem exists_mul_sub_two_pow_mem (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) {s : Lambda}
    (hs : s ∉ P) : ∃ (μ : Lambda) (j : ℕ), s * μ - 2 ^ j ∈ P := by
  have := finite_quotient hP hne
  have : Algebra.IsIntegral ℤ_[2] (Lambda ⧸ P) := Algebra.IsIntegral.of_finite ℤ_[2] _
  have hx : Ideal.Quotient.mk P s ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.under_ne_bot_of_integral_mem (R := ℤ_[2]) hx (Ideal.mem_span_singleton_self _)
      (Algebra.IsIntegral.isIntegral (R := ℤ_[2]) (Ideal.Quotient.mk P s)))
  have ha' : algebraMap ℤ_[2] (Lambda ⧸ P) a ∈ Ideal.span {Ideal.Quotient.mk P s} := ha
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp ha'
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨u, v, hu⟩ := padicInt_exists_unit_mul_two_pow ha0
  refine ⟨b * algebraMap ℤ_[2] Lambda ↑u⁻¹, v, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, Ideal.Quotient.mk_algebraMap,
    map_pow, map_ofNat, sub_eq_zero]
  calc Ideal.Quotient.mk P s * (Ideal.Quotient.mk P b * algebraMap ℤ_[2] (Lambda ⧸ P) ↑u⁻¹)
      = algebraMap ℤ_[2] (Lambda ⧸ P) a * algebraMap ℤ_[2] (Lambda ⧸ P) ↑u⁻¹ := by
        rw [← hb]
        ring
    _ = 2 ^ v := by
        rw [← map_mul, hu, mul_right_comm, Units.mul_inv, one_mul, map_pow, map_ofNat]

/-! ## 3. A power of `t` lies in `𝔭 + (2^N)` -/

/-- **A distinguished polynomial is `t^d` modulo `2`**: `2 ∣ f - t^d` in `Λ`, `d = deg f`
(Mathlib's `Polynomial.IsDistinguishedAt.map_eq_X_pow`; the maximal ideal of `ℤ₂` is `(2)`).
Kind: PROVED. Locator: `diophantine_zq.tex`, the height-one fibres of the switching argument,
tex 4976–5200; Washington, *Introduction to Cyclotomic Fields*, Thm 7.3. -/
theorem two_dvd_coe_sub_X_pow {f : Polynomial ℤ_[2]}
    (hf : f.IsDistinguishedAt (IsLocalRing.maximalIdeal ℤ_[2])) :
    (2 : Lambda) ∣ (f : Lambda) - PowerSeries.X ^ f.natDegree := by
  rw [two_dvd_iff_forall_coeff]
  intro n
  have h0 : Polynomial.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[2]))
      (f - Polynomial.X ^ f.natDegree) = 0 := by
    rw [Polynomial.map_sub, hf.map_eq_X_pow, Polynomial.map_pow, Polynomial.map_X, sub_self]
  have h1 := congrArg (fun q => Polynomial.coeff q n) h0
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h1
  rw [Ideal.Quotient.eq_zero_iff_mem, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton] at h1
  have h2 : PowerSeries.coeff n ((f : Lambda) - PowerSeries.X ^ f.natDegree) =
      (f - Polynomial.X ^ f.natDegree).coeff n := by
    rw [← Polynomial.coeff_coe, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X]
  rw [h2]
  exact_mod_cast h1

/-- **Item 3: for every `N` some power of `t` lies in `𝔭 + (2^N)`**: with `𝔭 = (f)`, `f`
distinguished of degree `d`, `t^d = f - 2c`, hence `t^(dN) ≡ (-2c)^N` modulo `(f)`. Kind: PROVED.
Locator: `diophantine_zq.tex`, the height-one fibres of the switching argument, tex 4976–5200,
and tex 5190–5194; Washington, *Introduction to Cyclotomic Fields*, Thm 7.3. -/
theorem exists_X_pow_mem (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) (N : ℕ) :
    ∃ M : ℕ, (PowerSeries.X : Lambda) ^ M ∈ P ⊔ Ideal.span {(2 : Lambda) ^ N} := by
  obtain ⟨f, hf, rfl⟩ := exists_distinguished_eq_span_of_height_one hP hne
  obtain ⟨c, hc⟩ := two_dvd_coe_sub_X_pow hf
  refine ⟨f.natDegree * N, ?_⟩
  have e : (PowerSeries.X : Lambda) ^ (f.natDegree * N) =
      ((PowerSeries.X ^ f.natDegree) ^ N - (2 * -c) ^ N) + (2 * -c) ^ N := by
    rw [pow_mul, sub_add_cancel]
  rw [e]
  refine Submodule.add_mem_sup ?_ ?_
  · rw [Ideal.mem_span_singleton]
    have hf' : (f : Lambda) = PowerSeries.X ^ f.natDegree - 2 * -c := by
      linear_combination hc
    rw [hf']
    exact sub_dvd_pow_sub_pow _ _ _
  · rw [Ideal.mem_span_singleton]
    exact ⟨(-c) ^ N, mul_pow _ _ _⟩

/-! ## 4–6. The residue field `k = Frac(Λ/𝔭)` -/

/-- **Item 4: `2` is a unit of `k = Frac(Λ/𝔭)`** (`2 ∉ 𝔭`,
`ZInQ.Manuscript.RC.CoefModules.two_ne_zero_resAt`). Kind: PROVED. Locator: `diophantine_zq.tex`,
the height-one fibres of the switching argument, tex 4976–5200 (`k = Frac(Λ/𝔭)` of
characteristic zero, tex 4977–4980), and tex 5190–5194. -/
theorem isUnit_two_resAt (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) :
    IsUnit (2 : ResAt P) :=
  isUnit_iff_ne_zero.mpr (two_ne_zero_resAt P hP hne)

/-- **Item 5: every `c ∈ k` times a power of `2` is the residue of an element of `Λ`**: write
`c = ρ(a/s)` with `s ∉ 𝔭` and use `s μ ≡ 2^j` modulo `𝔭` (`exists_mul_sub_two_pow_mem`); then
`2^j c = ρ(μ a)`. Kind: PROVED. Locator: `diophantine_zq.tex`, the height-one fibres of the
switching argument, tex 4976–5200 (`R = Λ_𝔭`, `k = Frac(Λ/𝔭)`), and tex 5190–5194. -/
theorem exists_two_pow_mul_eq (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) (c : ResAt P) :
    ∃ (l : Lambda) (j : ℕ),
      (2 : ResAt P) ^ j * c = resAt P (algebraMap Lambda (Localization.AtPrime P) l) := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective c
  obtain ⟨⟨a, s⟩, hy⟩ := IsLocalization.surj P.primeCompl y
  obtain ⟨μ, j, hμ⟩ := exists_mul_sub_two_pow_mem hP hne (Ideal.mem_primeCompl_iff.mp s.2)
  refine ⟨μ * a, j, ?_⟩
  have h0 : resAt P (algebraMap Lambda (Localization.AtPrime P) ((s : Lambda) * μ - 2 ^ j)) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).mpr hμ)
  rw [map_sub, map_sub, map_pow, map_pow, map_ofNat, map_ofNat, sub_eq_zero] at h0
  rw [← h0, ← map_mul]
  congr 1
  rw [map_mul, map_mul, ← hy]
  ring

/-- **The inferred `ℤ₂`-algebra structure on `k = ResAt P` is the composite `ℤ₂ → Λ → Λ_𝔭 → k`**
(it holds by definition). Kind: PROVED. Locator: `diophantine_zq.tex`, the height-one fibres of
the switching argument, tex 4976–5200 (`R = Λ_𝔭`, `k = Frac(Λ/𝔭)`). -/
theorem algebraMap_padicInt_resAt :
    algebraMap ℤ_[2] (ResAt P) =
      (resAt P).comp
        ((algebraMap Lambda (Localization.AtPrime P)).comp (algebraMap ℤ_[2] Lambda)) :=
  rfl

/-- **Item 6a: the structure map `ℤ₂ → k = Frac(Λ/𝔭)` is injective** (the `ℤ₂`-algebra structure
on `ResAt P` inferred through `Λ_𝔭`, see `algebraMap_padicInt_resAt`; `padicInt_ringHom_injective`
and `isUnit_two_resAt`). Kind: PROVED. Locator: `diophantine_zq.tex`, the height-one fibres of
the switching argument, tex 4976–5200 (`k = Frac(Λ/𝔭)` of characteristic zero, tex 4977–4980),
and tex 5190–5194. -/
theorem injective_algebraMap_padicInt (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) :
    Function.Injective (algebraMap ℤ_[2] (ResAt P)) :=
  padicInt_ringHom_injective _ (isUnit_two_resAt hP hne)

/-- **Item 6b: `k = Frac(Λ/𝔭)` has characteristic zero** ("Here `R` is a DVR and `k` has
characteristic zero", tex 4980): `ℤ₂` has characteristic zero and embeds in `k`
(`injective_algebraMap_padicInt`). Kind: PROVED. Locator: `diophantine_zq.tex`, the height-one
fibres of the switching argument, tex 4976–5200, and tex 5190–5194. -/
theorem charZero_resAt (hP : P.height = 1) (hne : P ≠ Ideal.span {2}) : CharZero (ResAt P) :=
  charZero_of_injective_algebraMap (injective_algebraMap_padicInt hP hne)

end HeightOne

/-! ## 7. Non-vacuity at `𝔭 = (t)` -/

/-- **`t + 2 ∉ (t)`** (its constant coefficient is `2 ≠ 0`); used to instantiate item 2 at a
specific element. Kind: PROVED. Locator: `diophantine_zq.tex`, the height-one fibres of the
switching argument, tex 4976–5200 (the two quadratic primes `(t)` and `(t + 2)`, tex 5004–5007). -/
theorem X_add_two_not_mem_span_X :
    (PowerSeries.X + 2 : Lambda) ∉ Ideal.span {(PowerSeries.X : Lambda)} := by
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_add, PowerSeries.constantCoeff_X,
    zero_add, map_ofNat]
  exact two_ne_zero

/-- Non-vacuity of item 1 (`finite_quotient`) at the height-one prime `(t) ≠ (2)`
(`ZInQ.Manuscript.RC.CoefModules.height_span_X`, `span_X_ne_span_two`). Kind: PROVED. Locator:
`diophantine_zq.tex`, the height-one fibres of the switching argument, tex 4976–5200. -/
example : Module.Finite ℤ_[2] (Lambda ⧸ Ideal.span {(PowerSeries.X : Lambda)}) :=
  finite_quotient height_span_X span_X_ne_span_two

/-- Non-vacuity of item 2 (`exists_mul_sub_two_pow_mem`) at `(t)`, for every `s ∉ (t)`. Kind:
PROVED. Locator: `diophantine_zq.tex`, the height-one fibres of the switching argument,
tex 4976–5200. -/
example {s : Lambda} (hs : s ∉ Ideal.span {(PowerSeries.X : Lambda)}) :
    ∃ (μ : Lambda) (j : ℕ), s * μ - 2 ^ j ∈ Ideal.span {(PowerSeries.X : Lambda)} :=
  exists_mul_sub_two_pow_mem height_span_X span_X_ne_span_two hs

/-- Non-vacuity of item 2 (`exists_mul_sub_two_pow_mem`) at `(t)` and the specific element
`s = t + 2 ∉ (t)`. Kind: PROVED. Locator: `diophantine_zq.tex`, the height-one fibres of the
switching argument, tex 4976–5200. -/
example : ∃ (μ : Lambda) (j : ℕ),
    (PowerSeries.X + 2 : Lambda) * μ - 2 ^ j ∈ Ideal.span {(PowerSeries.X : Lambda)} :=
  exists_mul_sub_two_pow_mem height_span_X span_X_ne_span_two X_add_two_not_mem_span_X

/-- Non-vacuity of item 3 (`exists_X_pow_mem`) at `(t)`. Kind: PROVED. Locator:
`diophantine_zq.tex`, the height-one fibres of the switching argument, tex 4976–5200. -/
example (N : ℕ) : ∃ M : ℕ, (PowerSeries.X : Lambda) ^ M ∈
    Ideal.span {(PowerSeries.X : Lambda)} ⊔ Ideal.span {(2 : Lambda) ^ N} :=
  exists_X_pow_mem height_span_X span_X_ne_span_two N

/-- Non-vacuity of item 4 (`isUnit_two_resAt`) at `(t)`. Kind: PROVED. Locator:
`diophantine_zq.tex`, the height-one fibres of the switching argument, tex 4976–5200. -/
example : IsUnit (2 : ResAt (Ideal.span {(PowerSeries.X : Lambda)})) :=
  isUnit_two_resAt height_span_X span_X_ne_span_two

/-- Non-vacuity of item 5 (`exists_two_pow_mul_eq`) at `(t)`. Kind: PROVED. Locator:
`diophantine_zq.tex`, the height-one fibres of the switching argument, tex 4976–5200. -/
example (c : ResAt (Ideal.span {(PowerSeries.X : Lambda)})) :
    ∃ (l : Lambda) (j : ℕ), (2 : ResAt (Ideal.span {(PowerSeries.X : Lambda)})) ^ j * c =
      resAt (Ideal.span {(PowerSeries.X : Lambda)})
        (algebraMap Lambda (Localization.AtPrime (Ideal.span {(PowerSeries.X : Lambda)})) l) :=
  exists_two_pow_mul_eq height_span_X span_X_ne_span_two c

/-- Non-vacuity of item 6 (`charZero_resAt`) at `(t)`. Kind: PROVED. Locator:
`diophantine_zq.tex`, the height-one fibres of the switching argument, tex 4976–5200. -/
example : CharZero (ResAt (Ideal.span {(PowerSeries.X : Lambda)})) :=
  charZero_resAt height_span_X span_X_ne_span_two

/-- Non-vacuity of item 6 (`injective_algebraMap_padicInt`) at `(t)`. Kind: PROVED. Locator:
`diophantine_zq.tex`, the height-one fibres of the switching argument, tex 4976–5200. -/
example : Function.Injective
    (algebraMap ℤ_[2] (ResAt (Ideal.span {(PowerSeries.X : Lambda)}))) :=
  injective_algebraMap_padicInt height_span_X span_X_ne_span_two

end ZInQ.Manuscript.RC.LambdaCoef
