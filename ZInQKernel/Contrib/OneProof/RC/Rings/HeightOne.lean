import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Uniform.LambdaHalf
import ZInQKernel.Contrib.OneProof.RC.Rings.Localization

/-!
# Lane RC20: the rings `R = Λ_𝔭` at the height-one primes of `Λ = ℤ₂[[t]]`

Manuscript (`diophantine_zq.tex`, 11/5 version), tex 4977–4980:

> Fix a height-one prime `𝔭 ≠ (2)`, put `R = Λ_𝔭` and `k = Frac(Λ/𝔭)`, and use the actual
> primitive scalar Selmer complex over `R`. Here `R` is a DVR and `k` has characteristic zero.

This file proves, for the genuine Mathlib localization `Localization.AtPrime 𝔭` of
`Λ = Uniform.Lambda = PowerSeries ℤ_[2]`:

* `isDiscreteValuationRing_atPrime_of_height_one` : `Λ_𝔭` is a DVR for every height-one prime `𝔭`
  (in the UFD `Λ` such a prime is `(p)`, `p` prime; then `Localization.lean`);
* `two_not_mem_of_height_one`, `isUnit_two_atPrime_of_height_one`, `natCast_not_mem_of_height_one`
  and the `CharZero` statements for `Λ/𝔭`, `k = Frac(Λ/𝔭)` and the residue field of `Λ_𝔭`, for
  `𝔭 ≠ (2)` of height one;
* the quadratic specializations `(t)` and `(t+2)` are height-one primes `≠ (2)`, so the above
  applies to them (also the non-vacuity of the hypotheses).

Everything here is `PROVED`.
-/

namespace ZInQ.Manuscript.RC.Rings

open ZInQ.Manuscript.RC.Uniform PowerSeries

/-! ## 1. `Λ_𝔭` is a DVR -/

/-- **Tex 4977–4980 ("Here `R` is a DVR"), PROVED.** For every height-one prime `𝔭` of
`Λ = ℤ₂[[t]]`, the localization `R = Λ_𝔭` is a discrete valuation ring. Proof: `Λ` is a UFD, so
`𝔭 = (p)` for a prime element `p` (`height_eq_one_iff_exists_prime`), and the localization of a UFD
at a principal prime is a DVR (`isDiscreteValuationRing_of_atPrime`). -/
theorem isDiscreteValuationRing_atPrime_of_height_one (P : Ideal Lambda) [P.IsPrime]
    (h : P.height = 1) : IsDiscreteValuationRing (Localization.AtPrime P) := by
  obtain ⟨p, hp, rfl⟩ := (height_eq_one_iff_exists_prime P).mp h
  exact isDiscreteValuationRing_of_atPrime (p := p) (Localization.AtPrime (Ideal.span {p}))
    hp.ne_zero

/-! ## 2. Away from `(2)`: `2` is a unit and the residue fields have characteristic zero -/

/-- **Tex 4977–4980, PROVED.** A height-one prime `𝔭 ≠ (2)` of `Λ` does not contain `2`: otherwise
`𝔭 = (2)`, since `2` is prime (`prime_two_lambda`) and `𝔭` has height one. -/
theorem two_not_mem_of_height_one (P : Ideal Lambda) [P.IsPrime] (h : P.height = 1)
    (hP2 : P ≠ Ideal.span {2}) : (2 : Lambda) ∉ P := fun h2 =>
  hP2 (Ideal.eq_span_singleton_of_height_eq_one h h2 prime_two_lambda)

/-- **Tex 4977–4980 (and tex 3761–3762 "`−2`, a unit at `𝔭 ≠ (2)`"), PROVED.** At a height-one
prime `𝔭 ≠ (2)`, `2` is a unit of `Λ_𝔭`. -/
theorem isUnit_two_atPrime_of_height_one (P : Ideal Lambda) [P.IsPrime] (h : P.height = 1)
    (hP2 : P ≠ Ideal.span {2}) : IsUnit (2 : Localization.AtPrime P) := by
  have hu := IsLocalization.map_units (Localization.AtPrime P)
    (⟨2, two_not_mem_of_height_one P h hP2⟩ : P.primeCompl)
  rwa [map_ofNat] at hu

/-- **Tex 4977–4980, PROVED.** An odd natural number is a unit of `Λ`: it is the constant series of
an odd number, a unit of `ℤ₂`. -/
theorem isUnit_natCast_of_odd {m : ℕ} (hm : Odd m) : IsUnit (m : Lambda) := by
  have hZ : IsUnit (m : ℤ_[2]) := by
    by_contra hnu
    have hmem : (m : ℤ_[2]) ∈ RingHom.ker (PadicInt.toZMod (p := 2)) := by
      rw [PadicInt.ker_toZMod]
      exact hnu
    rw [RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff_even] at hmem
    exact (Nat.not_even_iff_odd.mpr hm) hmem
  have := hZ.map (PowerSeries.C (R := ℤ_[2]))
  rwa [map_natCast] at this

/-- **Tex 4977–4980 ("`k` has characteristic zero"), PROVED.** At a height-one prime `𝔭 ≠ (2)`, no
positive integer lies in `𝔭`: write `n = 2^a m` with `m` odd; `m` is a unit of `Λ` and `2 ∉ 𝔭`. -/
theorem natCast_not_mem_of_height_one (P : Ideal Lambda) [P.IsPrime] (h : P.height = 1)
    (hP2 : P ≠ Ideal.span {2}) {n : ℕ} (hn : n ≠ 0) : (n : Lambda) ∉ P := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  intro hmem
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hmem
  rcases Ideal.IsPrime.mem_or_mem ‹P.IsPrime› hmem with h2 | hmP
  · exact two_not_mem_of_height_one P h hP2 (Ideal.IsPrime.mem_of_pow_mem ‹P.IsPrime› a h2)
  · exact Ideal.IsPrime.ne_top ‹P.IsPrime›
      (Ideal.eq_top_of_isUnit_mem P hmP (isUnit_natCast_of_odd hm))

/-- **Tex 4977–4980, PROVED.** For a height-one prime `𝔭 ≠ (2)`, the domain `Λ/𝔭` has
characteristic zero. -/
theorem charZero_quotient_of_height_one (P : Ideal Lambda) [P.IsPrime] (h : P.height = 1)
    (hP2 : P ≠ Ideal.span {2}) : CharZero (Lambda ⧸ P) := by
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra hn0
  rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem] at hn
  exact natCast_not_mem_of_height_one P h hP2 hn0 hn

/-- **Tex 4977–4980 ("`k = Frac(Λ/𝔭)` ... has characteristic zero"), PROVED.** For a height-one prime
`𝔭 ≠ (2)`, the field `k = Frac(Λ/𝔭)` has characteristic zero. -/
theorem charZero_fractionRing_quotient_of_height_one (P : Ideal Lambda) [P.IsPrime]
    (h : P.height = 1) (hP2 : P ≠ Ideal.span {2}) : CharZero (FractionRing (Lambda ⧸ P)) := by
  have := charZero_quotient_of_height_one P h hP2
  exact charZero_of_injective_algebraMap (IsFractionRing.injective (Lambda ⧸ P) _)

/-- **Tex 4977–4980, PROVED.** For a height-one prime `𝔭 ≠ (2)`, the residue field of the DVR
`R = Λ_𝔭` (which is `Frac(Λ/𝔭)`) has characteristic zero: the preimage in `Λ` of the maximal ideal
of `Λ_𝔭` is `𝔭`, which contains no positive integer. -/
theorem charZero_residueField_of_height_one (P : Ideal Lambda) [P.IsPrime] (h : P.height = 1)
    (hP2 : P ≠ Ideal.span {2}) :
    CharZero (IsLocalRing.ResidueField (Localization.AtPrime P)) := by
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra hn0
  have h1 : IsLocalRing.residue (Localization.AtPrime P)
      (algebraMap Lambda (Localization.AtPrime P) (n : Lambda)) = 0 := by
    rw [map_natCast, map_natCast]
    exact hn
  rw [IsLocalRing.residue_eq_zero_iff,
    IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P] at h1
  exact natCast_not_mem_of_height_one P h hP2 hn0 h1

/-- **Tex 4977–4980 (the whole sentence), PROVED.** For a height-one prime `𝔭 ≠ (2)`:
`R = Λ_𝔭` is a DVR in which `2` is a unit, and `k = Frac(Λ/𝔭)` and the residue field of `R` have
characteristic zero. -/
theorem atPrime_of_height_one_ne_two (P : Ideal Lambda) [P.IsPrime] (h : P.height = 1)
    (hP2 : P ≠ Ideal.span {2}) :
    IsDiscreteValuationRing (Localization.AtPrime P) ∧ (2 : Lambda) ∉ P ∧
      IsUnit (2 : Localization.AtPrime P) ∧ CharZero (Lambda ⧸ P) ∧
      CharZero (FractionRing (Lambda ⧸ P)) ∧
      CharZero (IsLocalRing.ResidueField (Localization.AtPrime P)) :=
  ⟨isDiscreteValuationRing_atPrime_of_height_one P h, two_not_mem_of_height_one P h hP2,
    isUnit_two_atPrime_of_height_one P h hP2, charZero_quotient_of_height_one P h hP2,
    charZero_fractionRing_quotient_of_height_one P h hP2,
    charZero_residueField_of_height_one P h hP2⟩

/-! ## 3. The quadratic specializations `(t)` and `(t + 2)` -/

/-- **Tex 4342–4343, 5190–5191, PROVED.** `(t)` is a prime ideal of `Λ` (Mathlib's
`PowerSeries.span_X_isPrime`); registered as an instance so that `Λ_(t)` is available. -/
instance span_X_isPrime_lambda : (Ideal.span {(X : Lambda)}).IsPrime :=
  PowerSeries.span_X_isPrime

/-- **Tex 4977–4980, 5190–5191, PROVED.** `t + 2` as a monic linear polynomial over `ℤ₂`; it is
distinguished at the maximal ideal `(2)` of `ℤ₂` (its non-leading coefficient `2` lies in `(2)`). -/
theorem isDistinguished_X_add_two :
    (Polynomial.X - Polynomial.C (-2 : ℤ_[2])).IsDistinguishedAt
      (IsLocalRing.maximalIdeal ℤ_[2]) where
  mem {n} hn := by
    rw [Polynomial.natDegree_X_sub_C] at hn
    obtain rfl : n = 0 := by omega
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, neg_neg,
      PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  monic := Polynomial.monic_X_sub_C _

/-- **Tex 4977–4980, 5190–5191 ("including both quadratic specializations"), PROVED.** `(t + 2)` is a
prime ideal of `Λ`. Proof (Weierstrass preparation): `t + 2` is a distinguished polynomial, so
`Λ/(t+2) ≅ ℤ₂[t]/(t+2) ≅ ℤ₂`, a domain. Registered as an instance. -/
instance span_X_add_two_isPrime : (Ideal.span {(X + 2 : Lambda)}).IsPrime := by
  have e := isDistinguished_X_add_two.algEquivQuotient
  have hcoe : ((Polynomial.X - Polynomial.C (-2 : ℤ_[2]) : Polynomial ℤ_[2]) : Lambda) = X + 2 := by
    rw [Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C, map_neg, sub_neg_eq_add,
      map_ofNat]
  rw [hcoe] at e
  have e2 := Polynomial.quotientSpanXSubCAlgEquiv (R := ℤ_[2]) (-2)
  have : IsDomain (Lambda ⧸ Ideal.span {(X + 2 : Lambda)}) :=
    (e.symm.trans e2).toMulEquiv.isDomain_iff.mpr inferInstance
  exact (Ideal.Quotient.isDomain_iff_prime _).mp this

/-- **Tex 4977–4980, 5190–5191, PROVED.** `t + 2 ≠ 0` in `Λ` (its constant coefficient is `2`). -/
theorem X_add_two_ne_zero : (X + 2 : Lambda) ≠ 0 := by
  intro h
  have := congrArg PowerSeries.constantCoeff h
  rw [map_add, constantCoeff_X, zero_add, map_ofNat, map_zero] at this
  exact two_ne_zero this

/-- **Tex 4977–4980, 5190–5191, PROVED.** A principal prime ideal `(x)`, `x ≠ 0`, of `Λ` has height
one (Krull's principal ideal theorem; `Λ` is noetherian). -/
theorem height_span_eq_one {x : Lambda} (hxp : (Ideal.span {x}).IsPrime) (hx0 : x ≠ 0) :
    (Ideal.span {x}).height = 1 := by
  refine le_antisymm ?_ (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hx0))
  exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) _
    ⟨⟨hxp, le_rfl⟩, fun _ hq _ => hq.2⟩

/-- **Tex 4342–4343, 5190–5191, PROVED.** `(t)` has height one. -/
theorem height_span_X : (Ideal.span {(X : Lambda)}).height = 1 :=
  height_span_eq_one span_X_isPrime_lambda X_ne_zero

/-- **Tex 4977–4980, 5190–5191, PROVED.** `(t + 2)` has height one. -/
theorem height_span_X_add_two : (Ideal.span {(X + 2 : Lambda)}).height = 1 :=
  height_span_eq_one span_X_add_two_isPrime X_add_two_ne_zero

/-- **Tex 4977–4980, 5190–5191, PROVED.** `(t) ≠ (2)`: `t` has constant coefficient `0`, and
`2 ∈ (t)` would force `2 = 0` in `ℤ₂`. -/
theorem span_X_ne_span_two : Ideal.span {(X : Lambda)} ≠ Ideal.span {2} := by
  intro h
  have h2 : (2 : Lambda) ∈ Ideal.span {(X : Lambda)} := h ▸ Ideal.mem_span_singleton_self _
  rw [Ideal.mem_span_singleton, X_dvd_iff, map_ofNat] at h2
  exact two_ne_zero h2

/-- **Tex 4977–4980, 5190–5191, PROVED.** `(t + 2) ≠ (2)`: the `t`-coefficient of `t + 2` is `1`,
which is not divisible by `2` in `ℤ₂`. -/
theorem span_X_add_two_ne_span_two : Ideal.span {(X + 2 : Lambda)} ≠ Ideal.span {2} := by
  intro h
  have h2 : (X + 2 : Lambda) ∈ Ideal.span {(2 : Lambda)} := h ▸ Ideal.mem_span_singleton_self _
  rw [Ideal.mem_span_singleton, two_dvd_iff_forall_coeff] at h2
  obtain ⟨d, hd⟩ := h2 1
  rw [map_add, coeff_X, show (2 : Lambda) = C (2 : ℤ_[2]) from (map_ofNat C 2).symm,
    coeff_C] at hd
  simp only [↓reduceIte, one_ne_zero, add_zero] at hd
  have := congrArg (PadicInt.toZMod (p := 2)) hd
  rw [map_one, map_mul, map_ofNat, show (2 : ZMod 2) = 0 from rfl, zero_mul] at this
  exact one_ne_zero this

/-- **Tex 4977–4980, 5190–5191 ("including both quadratic specializations"), PROVED.** The quadratic
specializations `(t)` and `(t + 2)` are height-one primes of `Λ` different from `(2)`. -/
theorem quadratic_specializations_height_one :
    (Ideal.span {(X : Lambda)}).height = 1 ∧ Ideal.span {(X : Lambda)} ≠ Ideal.span {2} ∧
      (Ideal.span {(X + 2 : Lambda)}).height = 1 ∧
      Ideal.span {(X + 2 : Lambda)} ≠ Ideal.span {2} :=
  ⟨height_span_X, span_X_ne_span_two, height_span_X_add_two, span_X_add_two_ne_span_two⟩

/-- **Tex 4342–4343, 4977–4980, PROVED (non-vacuity of §1–2 at `(t)`).** `Λ_(t)` is a DVR in which `2`
is a unit, and the residue fields at `(t)` have characteristic zero. -/
theorem atPrime_span_X :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {(X : Lambda)})) ∧
      (2 : Lambda) ∉ Ideal.span {(X : Lambda)} ∧
      IsUnit (2 : Localization.AtPrime (Ideal.span {(X : Lambda)})) ∧
      CharZero (Lambda ⧸ Ideal.span {(X : Lambda)}) ∧
      CharZero (FractionRing (Lambda ⧸ Ideal.span {(X : Lambda)})) ∧
      CharZero (IsLocalRing.ResidueField (Localization.AtPrime (Ideal.span {(X : Lambda)}))) :=
  atPrime_of_height_one_ne_two _ height_span_X span_X_ne_span_two

/-- **Tex 4977–4980, 5190–5191, PROVED (non-vacuity of §1–2 at `(t + 2)`).** `Λ_(t+2)` is a DVR in
which `2` is a unit, and the residue fields at `(t + 2)` have characteristic zero. -/
theorem atPrime_span_X_add_two :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {(X + 2 : Lambda)})) ∧
      (2 : Lambda) ∉ Ideal.span {(X + 2 : Lambda)} ∧
      IsUnit (2 : Localization.AtPrime (Ideal.span {(X + 2 : Lambda)})) ∧
      CharZero (Lambda ⧸ Ideal.span {(X + 2 : Lambda)}) ∧
      CharZero (FractionRing (Lambda ⧸ Ideal.span {(X + 2 : Lambda)})) ∧
      CharZero (IsLocalRing.ResidueField
        (Localization.AtPrime (Ideal.span {(X + 2 : Lambda)}))) :=
  atPrime_of_height_one_ne_two _ height_span_X_add_two span_X_add_two_ne_span_two

/-- **Tex 4977–4980, PROVED (non-vacuity).** There is a height-one prime `𝔭 ≠ (2)` of `Λ`, so the
hypotheses of `atPrime_of_height_one_ne_two` are satisfiable. -/
theorem exists_height_one_ne_two :
    ∃ P : Ideal Lambda, P.IsPrime ∧ P.height = 1 ∧ P ≠ Ideal.span {2} :=
  ⟨_, span_X_isPrime_lambda, height_span_X, span_X_ne_span_two⟩

end ZInQ.Manuscript.RC.Rings
