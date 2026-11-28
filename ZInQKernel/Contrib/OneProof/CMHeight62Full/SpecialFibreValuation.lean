import ZInQKernel.Contrib.OneProof.CMHeight62Full.GroupCurveNotP1
import ZInQKernel.Contrib.OneProof.CMHeight62Full.LatticeBasis
import ZInQKernel.Contrib.OneProof.CMHeight62Full.WeierstrassDVR

/-!
# The special-fibre valuation (node N6c)

Let `R` be a discrete valuation ring with uniformizer `ϖ`, `F` its fraction field, `A` a Noetherian
domain over `R` (with `R → A` injective) such that `A / ϖA` is a domain, and `Ω` the fraction field
of `A`. Then `ϖA` is a prime of height one and `A_(ϖ)` is a discrete valuation ring. Its valuation
`w` on `Ω` is the special-fibre valuation.

* `exists_specialFibreValuation`: `w` is `ℤᵐ⁰`-valued, `ϖ` is a uniformizer of `w` (in the sense of
  `IsUniformizer`), `w ≤ 1` on `R` and `w < 1` on its maximal ideal (so `w` restricts to the
  valuation of `R` on `F`), `w(a) < 1` for `a ∈ A` iff `a ∈ ϖA`, and `w(g) ≤ 1` iff `g = r / s`
  with `r, s ∈ A`, `s ∉ ϖA`.
* `specialFibreResidueMap`: the embedding `A / ϖA → κ_w` into the residue field of `w`;
  `isFractionRing_specialFibreResidueMap`: `κ_w` is the fraction field of `A / ϖA`.
* `specialFibrePlace`: when `A / ϖA` is a discrete valuation ring, its image `ē` in `κ_w` is a
  valuation subring. Given an `R`-algebra retraction `ρ : A → R`, `ē` is a degree-one place of
  `κ_w` over the residue field of `R` (`isDegreeOnePlace_specialFibrePlace`), and if
  `ker ρ = (t)` then the image of `t` is a uniformizer at `ē` (`isUniformizerAt_specialFibrePlace`).

Only Mathlib and earlier files of this directory are used.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open IsLocalRing IsDedekindDomain

open scoped WithZero

namespace SpecialFibreValuation

section PrimeLocalization

variable {A : Type*} [CommRing A] [IsDomain A] (Ω : Type*) [Field Ω] [Algebra A Ω]
  [IsFractionRing A Ω]

/-- The localization `A_𝔭` at a prime `𝔭`, realized inside the fraction field `Ω`. -/
abbrev primeLocalization (P : Ideal A) [P.IsPrime] : Subalgebra A Ω :=
  Localization.subalgebra.ofField Ω P.primeCompl P.primeCompl_le_nonZeroDivisors

variable (P : Ideal A) [P.IsPrime]

instance isLocalization_primeLocalization :
    IsLocalization.AtPrime (primeLocalization Ω P) P := by
  unfold primeLocalization
  infer_instance

instance isFractionRing_primeLocalization : IsFractionRing (primeLocalization Ω P) Ω :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl _ Ω

instance isLocalRing_primeLocalization : IsLocalRing (primeLocalization Ω P) :=
  IsLocalization.AtPrime.isLocalRing _ P

variable {Ω}

theorem algebraMap_primeLocalization_apply (a : A) :
    algebraMap (primeLocalization Ω P) Ω (algebraMap A (primeLocalization Ω P) a) =
      algebraMap A Ω a :=
  (IsScalarTower.algebraMap_apply A (primeLocalization Ω P) Ω a).symm

theorem maximalIdeal_primeLocalization {p : A} [(Ideal.span {p}).IsPrime] :
    maximalIdeal (primeLocalization Ω (Ideal.span {p})) =
      Ideal.span {algebraMap A (primeLocalization Ω (Ideal.span {p})) p} := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {p}), Ideal.map_span,
    Set.image_singleton]

variable (Ω) in
/-- For a Noetherian domain `A` and `p ≠ 0` with `(p)` prime, `A_(p)` is a discrete valuation
ring. -/
theorem isDiscreteValuationRing_primeLocalization [IsNoetherianRing A] {p : A} (hp : p ≠ 0)
    [(Ideal.span {p}).IsPrime] :
    IsDiscreteValuationRing (primeLocalization Ω (Ideal.span {p})) := by
  have : IsNoetherianRing (primeLocalization Ω (Ideal.span {p})) :=
    IsLocalization.isNoetherianRing (Ideal.span {p}).primeCompl _ inferInstance
  have hnf : ¬ IsField (primeLocalization Ω (Ideal.span {p})) := by
    intro hf
    have h := IsLocalRing.isField_iff_maximalIdeal_eq.mp hf
    rw [maximalIdeal_primeLocalization, Ideal.span_singleton_eq_bot] at h
    exact hp (IsLocalization.injective (primeLocalization Ω (Ideal.span {p}))
      (Ideal.span {p}).primeCompl_le_nonZeroDivisors (h.trans (map_zero _).symm))
  have hpr : (maximalIdeal (primeLocalization Ω (Ideal.span {p}))).IsPrincipal :=
    ⟨⟨_, maximalIdeal_primeLocalization⟩⟩
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 1 5).mpr hpr

variable (Ω) in
/-- The valuation of the discrete valuation ring `A_(p)`, on the fraction field `Ω`. -/
def primeValuation [IsNoetherianRing A] {p : A} (hp : p ≠ 0) [(Ideal.span {p}).IsPrime] :
    Valuation Ω ℤᵐ⁰ :=
  haveI := isDiscreteValuationRing_primeLocalization Ω hp
  (IsDiscreteValuationRing.maximalIdeal (primeLocalization Ω (Ideal.span {p}))).valuation Ω

variable [IsNoetherianRing A] {p : A} (hp : p ≠ 0) [(Ideal.span {p}).IsPrime]
include hp

theorem primeValuation_le_one (b : primeLocalization Ω (Ideal.span {p})) :
    primeValuation Ω hp (algebraMap _ Ω b) ≤ 1 := by
  have := isDiscreteValuationRing_primeLocalization Ω hp
  exact HeightOneSpectrum.valuation_le_one _ b

theorem primeValuation_lt_one_iff_mem (b : primeLocalization Ω (Ideal.span {p})) :
    primeValuation Ω hp (algebraMap _ Ω b) < 1 ↔
      b ∈ maximalIdeal (primeLocalization Ω (Ideal.span {p})) := by
  have := isDiscreteValuationRing_primeLocalization Ω hp
  exact HeightOneSpectrum.valuation_lt_one_iff_mem _ b

theorem primeValuation_le_one_iff_mem_range (g : Ω) :
    primeValuation Ω hp g ≤ 1 ↔
      g ∈ (algebraMap (primeLocalization Ω (Ideal.span {p})) Ω).range := by
  have := isDiscreteValuationRing_primeLocalization Ω hp
  constructor
  · intro hg
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one Ω g fun v => ?_
    have hv : v = IsDiscreteValuationRing.maximalIdeal _ :=
      HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal (v.isPrime.isMaximal v.ne_bot))
    rw [hv]
    exact hg
  · rintro ⟨b, rfl⟩
    exact primeValuation_le_one hp b

theorem primeValuation_algebraMap_lt_one_iff (a : A) :
    primeValuation Ω hp (algebraMap A Ω a) < 1 ↔ a ∈ Ideal.span {p} := by
  rw [← algebraMap_primeLocalization_apply (Ideal.span {p}), primeValuation_lt_one_iff_mem,
    IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Ideal.span {p})]

theorem primeValuation_algebraMap_le_one (a : A) :
    primeValuation Ω hp (algebraMap A Ω a) ≤ 1 := by
  rw [← algebraMap_primeLocalization_apply (Ideal.span {p})]
  exact primeValuation_le_one hp _

theorem primeValuation_algebraMap_eq_one {a : A} (ha : a ∉ Ideal.span {p}) :
    primeValuation Ω hp (algebraMap A Ω a) = 1 :=
  le_antisymm (primeValuation_algebraMap_le_one hp a)
    (not_lt.mp fun h => ha ((primeValuation_algebraMap_lt_one_iff hp a).mp h))

theorem primeValuation_le_one_iff (g : Ω) :
    primeValuation Ω hp g ≤ 1 ↔ ∃ r s : A, s ∉ Ideal.span {p} ∧
      algebraMap A Ω s * g = algebraMap A Ω r := by
  constructor
  · intro hg
    obtain ⟨b, rfl⟩ := (primeValuation_le_one_iff_mem_range hp g).mp hg
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.span {p}).primeCompl b
    refine ⟨r, s, s.2, ?_⟩
    rw [← algebraMap_primeLocalization_apply (Ideal.span {p}),
      ← algebraMap_primeLocalization_apply (Ideal.span {p}), ← map_mul,
      mul_comm, IsLocalization.mk'_spec]
  · rintro ⟨r, s, hs, h⟩
    have h1 := congrArg (primeValuation Ω hp) h
    rw [map_mul, primeValuation_algebraMap_eq_one hp hs, one_mul] at h1
    rw [h1]
    exact primeValuation_algebraMap_le_one hp r

theorem primeValuation_eq_zpow {g : Ω} (hg : g ≠ 0) :
    ∃ m : ℤ, primeValuation Ω hp g = primeValuation Ω hp (algebraMap A Ω p) ^ m := by
  have := isDiscreteValuationRing_primeLocalization Ω hp
  have hirr : Irreducible (algebraMap A (primeLocalization Ω (Ideal.span {p})) p) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr maximalIdeal_primeLocalization
  have hunit : ∀ u : (primeLocalization Ω (Ideal.span {p}))ˣ,
      primeValuation Ω hp (algebraMap _ Ω (u : primeLocalization Ω (Ideal.span {p}))) = 1 :=
    fun u => le_antisymm (primeValuation_le_one hp _) (not_lt.mp fun h =>
      mem_nonunits_iff.mp ((mem_maximalIdeal _).mp ((primeValuation_lt_one_iff_mem hp _).mp h))
        u.isUnit)
  have hpow : ∀ b : primeLocalization Ω (Ideal.span {p}), b ≠ 0 → ∃ n : ℕ,
      primeValuation Ω hp (algebraMap _ Ω b) = primeValuation Ω hp (algebraMap A Ω p) ^ n := by
    intro b hb
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hirr
    exact ⟨n, by simp only [map_mul, map_pow, hunit, one_mul,
      algebraMap_primeLocalization_apply (Ideal.span {p})]⟩
  obtain ⟨x, y, hy, rfl⟩ :=
    IsFractionRing.div_surjective (A := primeLocalization Ω (Ideal.span {p})) g
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hg
  obtain ⟨n, hn⟩ := hpow x hx0
  obtain ⟨k, hk⟩ := hpow y hy0
  have h0 : primeValuation Ω hp (algebraMap A Ω p) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact (map_ne_zero_iff _ (IsFractionRing.injective A Ω)).mpr hp
  refine ⟨(n : ℤ) - k, ?_⟩
  rw [map_div₀, hn, hk, zpow_sub₀ h0, zpow_natCast, zpow_natCast]

end PrimeLocalization

section SpecialFibre

variable {R : Type*} [CommRing R]
  (A : Type*) [CommRing A] [IsNoetherianRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A]
  (Ω : Type*) [Field Ω] [Algebra A Ω] [IsFractionRing A Ω]
  {ϖ : R} (hϖ : Irreducible ϖ) [IsDomain (A ⧸ Ideal.span {algebraMap R A ϖ})]

omit [IsNoetherianRing A] [IsDomain A] [FaithfulSMul R A] in
theorem isPrime_span_algebraMap : (Ideal.span {algebraMap R A ϖ}).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

include hϖ

omit [IsNoetherianRing A] [IsDomain A] [IsDomain (A ⧸ Ideal.span {algebraMap R A ϖ})] in
theorem algebraMap_ne_zero_of_irreducible : algebraMap R A ϖ ≠ 0 :=
  (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R A)).mpr hϖ.ne_zero

/-- The special-fibre valuation: the valuation of the discrete valuation ring `A_(ϖ)` on `Ω`. -/
def specialFibreValuation : Valuation Ω ℤᵐ⁰ :=
  haveI := isPrime_span_algebraMap A (ϖ := ϖ)
  primeValuation Ω (algebraMap_ne_zero_of_irreducible A hϖ)

variable {A Ω}

theorem specialFibreValuation_algebraMap_le_one (a : A) :
    specialFibreValuation A Ω hϖ (algebraMap A Ω a) ≤ 1 := by
  have := isPrime_span_algebraMap A (ϖ := ϖ)
  exact primeValuation_algebraMap_le_one (algebraMap_ne_zero_of_irreducible A hϖ) a

theorem specialFibreValuation_algebraMap_lt_one_iff (a : A) :
    specialFibreValuation A Ω hϖ (algebraMap A Ω a) < 1 ↔
      a ∈ Ideal.span {algebraMap R A ϖ} := by
  have := isPrime_span_algebraMap A (ϖ := ϖ)
  exact primeValuation_algebraMap_lt_one_iff (algebraMap_ne_zero_of_irreducible A hϖ) a

theorem specialFibreValuation_le_one_iff (g : Ω) :
    specialFibreValuation A Ω hϖ g ≤ 1 ↔ ∃ r s : A, s ∉ Ideal.span {algebraMap R A ϖ} ∧
      algebraMap A Ω s * g = algebraMap A Ω r := by
  have := isPrime_span_algebraMap A (ϖ := ϖ)
  exact primeValuation_le_one_iff (algebraMap_ne_zero_of_irreducible A hϖ) g

section Base

variable [Algebra R Ω] [IsScalarTower R A Ω]

theorem specialFibreValuation_algebraMap_base_le_one (r : R) :
    specialFibreValuation A Ω hϖ (algebraMap R Ω r) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply R A Ω]
  exact specialFibreValuation_algebraMap_le_one hϖ _

theorem specialFibreValuation_eq_zpow {g : Ω} (hg : g ≠ 0) :
    ∃ m : ℤ, specialFibreValuation A Ω hϖ g =
      specialFibreValuation A Ω hϖ (algebraMap R Ω ϖ) ^ m := by
  rw [IsScalarTower.algebraMap_apply R A Ω]
  have := isPrime_span_algebraMap A (ϖ := ϖ)
  exact primeValuation_eq_zpow (algebraMap_ne_zero_of_irreducible A hϖ) hg

variable [IsDomain R] [IsDiscreteValuationRing R]

theorem specialFibreValuation_algebraMap_base_lt_one (r : R) (hr : r ∈ maximalIdeal R) :
    specialFibreValuation A Ω hϖ (algebraMap R Ω r) < 1 := by
  rw [IsScalarTower.algebraMap_apply R A Ω, specialFibreValuation_algebraMap_lt_one_iff]
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ] at hr
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)


/-- `w` restricts to the valuation of `R` on its fraction field `F`: an element of `F` is
`w`-integral iff it lies in `R`. -/
theorem specialFibreValuation_field_le_one_iff {F : Type*} [Field F] [Algebra R F]
    [IsFractionRing R F] [Algebra F Ω] [IsScalarTower R F Ω] (c : F) :
    specialFibreValuation A Ω hϖ (algebraMap F Ω c) ≤ 1 ↔ c ∈ (algebraMap R F).range := by
  have hF : ∀ r : R, algebraMap F Ω (algebraMap R F r) = algebraMap R Ω r := fun r =>
    (IsScalarTower.algebraMap_apply R F Ω r).symm
  refine ⟨fun hc => ?_, ?_⟩
  swap
  · rintro ⟨r, rfl⟩
    rw [hF]
    exact specialFibreValuation_algebraMap_base_le_one hϖ r
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) c
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0]⟩
  have hunit : ∀ u : Rˣ, specialFibreValuation A Ω hϖ (algebraMap R Ω u) = 1 := by
    intro u
    have h1 : specialFibreValuation A Ω hϖ (algebraMap R Ω u) *
        specialFibreValuation A Ω hϖ (algebraMap R Ω ↑u⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    refine le_antisymm (specialFibreValuation_algebraMap_base_le_one hϖ _) (not_lt.mp ?_)
    intro hlt
    have h2 := mul_lt_one_of_lt_of_le hlt
      (specialFibreValuation_algebraMap_base_le_one (A := A) (Ω := Ω) hϖ (↑u⁻¹ : R))
    rw [h1] at h2
    exact lt_irrefl _ h2
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  obtain ⟨n, u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have hval : ∀ (v : Rˣ) (k : ℕ), specialFibreValuation A Ω hϖ (algebraMap R Ω (↑v * ϖ ^ k)) =
      specialFibreValuation A Ω hϖ (algebraMap R Ω ϖ) ^ k := by
    intro v k
    rw [map_mul, map_pow, map_mul, map_pow, hunit, one_mul]
  have hϖ1 : specialFibreValuation A Ω hϖ (algebraMap R Ω ϖ) < 1 :=
    specialFibreValuation_algebraMap_base_lt_one hϖ ϖ
      ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hϖ.not_isUnit))
  have hϖ0 : specialFibreValuation A Ω hϖ (algebraMap R Ω ϖ) ≠ 0 := by
    rw [Valuation.ne_zero_iff, IsScalarTower.algebraMap_apply R A Ω]
    exact (map_ne_zero_iff _ (IsFractionRing.injective A Ω)).mpr
      (algebraMap_ne_zero_of_irreducible A hϖ)
  rw [map_div₀, map_div₀, hF, hF, hval, hval,
    div_le_one₀ (pow_pos (zero_lt_iff.mpr hϖ0) n)] at hc
  have hnm : n ≤ m := (pow_le_pow_iff_right_of_lt_one₀ (zero_lt_iff.mpr hϖ0) hϖ1).mp hc
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  refine ⟨↑(u * u'⁻¹) * ϖ ^ k, ?_⟩
  rw [eq_div_iff ((map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hy0), ← map_mul]
  congr 1
  have hinv : (↑u'⁻¹ : R) * ↑u' = 1 := Units.inv_mul u'
  rw [Units.val_mul, pow_add]
  linear_combination (↑u * ϖ ^ n * ϖ ^ k) * hinv

end Base

variable (A Ω) in
/-- `A → 𝒪_w`. -/
def toSpecialFibreIntegers : A →+* (specialFibreValuation A Ω hϖ).valuationSubring :=
  (algebraMap A Ω).codRestrict _ fun a =>
    ((specialFibreValuation A Ω hϖ).mem_valuationSubring_iff _).2
      (specialFibreValuation_algebraMap_le_one hϖ a)

variable (A Ω) in
/-- The embedding `A / ϖA → κ_w` of the special fibre ring into the residue field of `w`. -/
def specialFibreResidueMap : A ⧸ Ideal.span {algebraMap R A ϖ} →+*
    ResidueField (specialFibreValuation A Ω hϖ).valuationSubring :=
  Ideal.Quotient.lift _ ((residue _).comp (toSpecialFibreIntegers A Ω hϖ)) fun a ha => by
    rw [RingHom.comp_apply, residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    exact (specialFibreValuation_algebraMap_lt_one_iff hϖ a).mpr ha

theorem specialFibreResidueMap_mk (a : A) :
    specialFibreResidueMap A Ω hϖ (Ideal.Quotient.mk _ a) =
      residue _ (toSpecialFibreIntegers A Ω hϖ a) := rfl

theorem specialFibreResidueMap_injective :
    Function.Injective (specialFibreResidueMap A Ω hϖ) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [specialFibreResidueMap_mk, residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff] at hy
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    ((specialFibreValuation_algebraMap_lt_one_iff hϖ a).mp hy)

theorem exists_mul_specialFibreResidueMap_eq
    (z : ResidueField (specialFibreValuation A Ω hϖ).valuationSubring) :
    ∃ a b : A ⧸ Ideal.span {algebraMap R A ϖ}, specialFibreResidueMap A Ω hϖ b ≠ 0 ∧
      z * specialFibreResidueMap A Ω hϖ b = specialFibreResidueMap A Ω hϖ a := by
  obtain ⟨x, rfl⟩ := residue_surjective z
  obtain ⟨r, s, hs, h⟩ := (specialFibreValuation_le_one_iff hϖ (x : Ω)).mp
    ((Valuation.mem_valuationSubring_iff _ _).mp x.2)
  refine ⟨Ideal.Quotient.mk _ r, Ideal.Quotient.mk _ s, ?_, ?_⟩
  · rw [Ne, ← map_zero (specialFibreResidueMap A Ω hϖ)]
    intro h0
    exact hs (Ideal.Quotient.eq_zero_iff_mem.mp (specialFibreResidueMap_injective hϖ h0))
  · rw [specialFibreResidueMap_mk, specialFibreResidueMap_mk, ← map_mul]
    congr 1
    apply Subtype.ext
    show (x : Ω) * algebraMap A Ω s = algebraMap A Ω r
    rw [mul_comm, h]

/-- `κ_w` is the fraction field of `A / ϖA`, through `specialFibreResidueMap`. -/
theorem isFractionRing_specialFibreResidueMap :
    letI := (specialFibreResidueMap A Ω hϖ).toAlgebra
    IsFractionRing (A ⧸ Ideal.span {algebraMap R A ϖ})
      (ResidueField (specialFibreValuation A Ω hϖ).valuationSubring) := by
  let := (specialFibreResidueMap A Ω hϖ).toAlgebra
  have : FaithfulSMul (A ⧸ Ideal.span {algebraMap R A ϖ})
      (ResidueField (specialFibreValuation A Ω hϖ).valuationSubring) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (specialFibreResidueMap_injective hϖ)
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨a, b, hb, h⟩ := exists_mul_specialFibreResidueMap_eq hϖ z
  exact ⟨a, b, (eq_div_iff hb).mpr h⟩

omit [IsNoetherianRing A] [IsDomain A] [FaithfulSMul R A]
  [IsDomain (A ⧸ Ideal.span {algebraMap R A ϖ})] in
/-- An element of the kernel of an `R`-algebra retraction `ρ : A → R` is not a unit mod `ϖ`. -/
theorem not_isUnit_mk_of_mem_ker (ρ : A →ₐ[R] R) {d : A} (hd : ρ d = 0) :
    ¬ IsUnit (Ideal.Quotient.mk (Ideal.span {algebraMap R A ϖ}) d) := by
  intro h
  obtain ⟨e, he⟩ := h.exists_right_inv
  obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective e
  rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq] at he
  obtain ⟨f, hf⟩ := Ideal.mem_span_singleton'.mp he
  have h1 := congrArg ρ hf
  rw [map_mul, map_sub, map_mul, map_one, hd, zero_mul, AlgHom.commutes,
    Algebra.algebraMap_self, RingHom.id_apply] at h1
  exact hϖ.not_isUnit (IsUnit.of_mul_eq_one (-ρ f) (by linear_combination -h1))

section Place

variable [IsDiscreteValuationRing (A ⧸ Ideal.span {algebraMap R A ϖ})]

variable (A Ω) in
/-- The place `ē` of `κ_w`: the image of the discrete valuation ring `A / ϖA`. -/
def specialFibrePlace :
    ValuationSubring (ResidueField (specialFibreValuation A Ω hϖ).valuationSubring) where
  toSubring := (specialFibreResidueMap A Ω hϖ).range
  mem_or_inv_mem' z := by
    obtain ⟨a, b, hb, h⟩ := exists_mul_specialFibreResidueMap_eq hϖ z
    rcases ValuationRing.dvd_total a b with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · right
      have ha : specialFibreResidueMap A Ω hϖ a ≠ 0 := by
        intro ha
        apply hb
        rw [map_mul, ha, zero_mul]
      rw [map_mul] at h
      have h1 : z * specialFibreResidueMap A Ω hϖ c = 1 := by
        apply mul_left_cancel₀ ha
        calc specialFibreResidueMap A Ω hϖ a * (z * specialFibreResidueMap A Ω hϖ c)
            = z * (specialFibreResidueMap A Ω hϖ a * specialFibreResidueMap A Ω hϖ c) := by
              ring
          _ = specialFibreResidueMap A Ω hϖ a * 1 := by rw [h, mul_one]
      exact RingHom.mem_range.mpr ⟨c, eq_inv_of_mul_eq_one_right h1⟩
    · left
      rw [map_mul] at h
      exact RingHom.mem_range.mpr ⟨c, (mul_right_cancel₀ hb (h.trans (mul_comm _ _))).symm⟩

theorem mem_specialFibrePlace
    {z : ResidueField (specialFibreValuation A Ω hϖ).valuationSubring} :
    z ∈ specialFibrePlace A Ω hϖ ↔ ∃ y, specialFibreResidueMap A Ω hϖ y = z :=
  RingHom.mem_range

theorem mem_of_mem_nonunits_specialFibrePlace
    {z : ResidueField (specialFibreValuation A Ω hϖ).valuationSubring}
    (hz : z ∈ (specialFibrePlace A Ω hϖ).nonunits) : z ∈ specialFibrePlace A Ω hϖ :=
  (ValuationSubring.valuation_le_one_iff _ _).mp ((ValuationSubring.mem_nonunits_iff _).mp hz).le

theorem specialFibreResidueMap_mem_nonunits_iff (y : A ⧸ Ideal.span {algebraMap R A ϖ}) :
    specialFibreResidueMap A Ω hϖ y ∈ (specialFibrePlace A Ω hϖ).nonunits ↔ ¬ IsUnit y := by
  have hmem : specialFibreResidueMap A Ω hϖ y ∈ specialFibrePlace A Ω hϖ :=
    (mem_specialFibrePlace hϖ).mpr ⟨y, rfl⟩
  rw [ValuationSubring.mem_nonunits_iff]
  refine (ValuationSubring.valuation_lt_one_iff _ ⟨_, hmem⟩).symm.trans ?_
  rw [mem_maximalIdeal, mem_nonunits_iff]
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨v, hv⟩ := h.exists_right_inv
    obtain ⟨c, hc⟩ := (mem_specialFibrePlace hϖ).mp v.2
    refine IsUnit.of_mul_eq_one c (specialFibreResidueMap_injective (A := A) (Ω := Ω) hϖ ?_)
    rw [map_mul, map_one, hc]
    exact congrArg Subtype.val hv
  · obtain ⟨c, hc⟩ := h.exists_right_inv
    refine IsUnit.of_mul_eq_one ⟨_, (mem_specialFibrePlace hϖ).mpr ⟨c, rfl⟩⟩
      (Subtype.ext ?_)
    show specialFibreResidueMap A Ω hϖ y * specialFibreResidueMap A Ω hϖ c = 1
    rw [← map_mul, hc, map_one]

variable [IsDomain R] [IsDiscreteValuationRing R]

omit [IsNoetherianRing A] [IsDomain A] [FaithfulSMul R A] in
/-- If `ker ρ = (t)`, every nonunit of `A / ϖA` is a multiple of `t`. -/
theorem exists_mk_eq_mk_mul (ρ : A →ₐ[R] R) {t : A} (hker : RingHom.ker ρ = Ideal.span {t})
    {a : A} (ha : ¬ IsUnit (Ideal.Quotient.mk (Ideal.span {algebraMap R A ϖ}) a)) :
    ∃ b : A, Ideal.Quotient.mk (Ideal.span {algebraMap R A ϖ}) a =
      Ideal.Quotient.mk _ t * Ideal.Quotient.mk _ b := by
  have ht : ρ t = 0 := RingHom.mem_ker.mp (hker ▸ Ideal.mem_span_singleton_self t)
  have hd : a - algebraMap R A (ρ a) ∈ Ideal.span {t} := by
    rw [← hker, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hd
  have hρ : ρ a ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : Ideal.Quotient.mk (Ideal.span {algebraMap R A ϖ}) (algebraMap R A (ρ a)) ∈
        maximalIdeal (A ⧸ Ideal.span {algebraMap R A ϖ}) := by
      have e : algebraMap R A (ρ a) = a - b * t := by
        rw [hb]
        ring
      rw [e, map_sub, map_mul]
      exact Ideal.sub_mem _ ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr ha))
        (Ideal.mul_mem_left _ _ ((mem_maximalIdeal _).mpr
          (mem_nonunits_iff.mpr (not_isUnit_mk_of_mem_ker hϖ ρ ht))))
    exact mem_nonunits_iff.mp ((mem_maximalIdeal _).mp h1)
      ((hu.map (algebraMap R A)).map (Ideal.Quotient.mk _))
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ] at hρ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hρ
  refine ⟨b, ?_⟩
  rw [← map_mul, Ideal.Quotient.eq]
  have e : a - t * b = algebraMap R A c * algebraMap R A ϖ := by
    rw [← map_mul, hc]
    linear_combination -hb
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

variable [Algebra R Ω] [IsScalarTower R A Ω]

omit [IsDiscreteValuationRing (A ⧸ Ideal.span {algebraMap R A ϖ})] in
theorem residueHom_residue_eq (r : R) :
    residueHom (specialFibreValuation A Ω hϖ) (specialFibreValuation_algebraMap_base_le_one hϖ)
        (specialFibreValuation_algebraMap_base_lt_one hϖ) (residue R r) =
      specialFibreResidueMap A Ω hϖ (Ideal.Quotient.mk _ (algebraMap R A r)) := by
  have := isLocalHom_toIntegers (specialFibreValuation A Ω hϖ)
    (specialFibreValuation_algebraMap_base_le_one hϖ)
    (specialFibreValuation_algebraMap_base_lt_one hϖ)
  rw [specialFibreResidueMap_mk, residueHom, ResidueField.map_residue]
  congr 1
  apply Subtype.ext
  exact IsScalarTower.algebraMap_apply R A Ω r

/-- **`ē` is a degree-one place** of `κ_w` over the residue field of `R` (the residue field
algebra is `residueHom`), given an `R`-algebra retraction `ρ : A → R`. -/
theorem isDegreeOnePlace_specialFibrePlace (ρ : A →ₐ[R] R) :
    letI := (residueHom (specialFibreValuation A Ω hϖ)
      (specialFibreValuation_algebraMap_base_le_one hϖ)
      (specialFibreValuation_algebraMap_base_lt_one hϖ)).toAlgebra
    IsDegreeOnePlace (ResidueField R) (specialFibrePlace A Ω hϖ) := by
  let := (residueHom (specialFibreValuation A Ω hϖ)
    (specialFibreValuation_algebraMap_base_le_one hϖ)
    (specialFibreValuation_algebraMap_base_lt_one hϖ)).toAlgebra
  refine ⟨fun c => ?_, fun htop => ?_, fun x hx => ?_⟩
  · obtain ⟨r, rfl⟩ := residue_surjective c
    exact (mem_specialFibrePlace hϖ).mpr ⟨_, (residueHom_residue_eq hϖ r).symm⟩
  · obtain ⟨y, hy⟩ := IsDiscreteValuationRing.exists_irreducible
      (A ⧸ Ideal.span {algebraMap R A ϖ})
    have hmem : (specialFibreResidueMap A Ω hϖ y)⁻¹ ∈ specialFibrePlace A Ω hϖ := by
      rw [htop]
      exact ValuationSubring.mem_top _
    obtain ⟨c, hc⟩ := (mem_specialFibrePlace hϖ).mp hmem
    have hy0 : specialFibreResidueMap A Ω hϖ y ≠ 0 :=
      (map_ne_zero_iff _ (specialFibreResidueMap_injective hϖ)).mpr hy.ne_zero
    apply hy.not_isUnit
    refine IsUnit.of_mul_eq_one c (specialFibreResidueMap_injective (A := A) (Ω := Ω) hϖ ?_)
    rw [map_mul, hc, mul_inv_cancel₀ hy0, map_one]
  · obtain ⟨y, rfl⟩ := (mem_specialFibrePlace hϖ).mp hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨residue R (ρ a), ?_⟩
    rw [RingHom.algebraMap_toAlgebra, residueHom_residue_eq, ← map_sub, ← map_sub,
      specialFibreResidueMap_mem_nonunits_iff]
    apply not_isUnit_mk_of_mem_ker hϖ ρ
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]

omit [Algebra R Ω] [IsScalarTower R A Ω] in
/-- If `ker ρ = (t)`, the image `t̄` of `t` is a uniformizer at `ē`. -/
theorem isUniformizerAt_specialFibrePlace (ρ : A →ₐ[R] R) {t : A}
    (hker : RingHom.ker ρ = Ideal.span {t}) :
    IsUniformizerAt (specialFibrePlace A Ω hϖ)
      (specialFibreResidueMap A Ω hϖ (Ideal.Quotient.mk _ t)) := by
  have ht : ρ t = 0 := RingHom.mem_ker.mp (hker ▸ Ideal.mem_span_singleton_self t)
  have hπ0 : specialFibreResidueMap A Ω hϖ (Ideal.Quotient.mk _ t) ≠ 0 := by
    intro h0
    obtain ⟨y, hy⟩ := IsDiscreteValuationRing.exists_irreducible
      (A ⧸ Ideal.span {algebraMap R A ϖ})
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨b, hb⟩ := exists_mk_eq_mk_mul hϖ ρ hker hy.not_isUnit
    have h1 : Ideal.Quotient.mk (Ideal.span {algebraMap R A ϖ}) t = 0 :=
      (map_eq_zero_iff _ (specialFibreResidueMap_injective hϖ)).mp h0
    exact hy.ne_zero (by rw [hb, h1, zero_mul])
  refine ⟨hπ0, (specialFibreResidueMap_mem_nonunits_iff hϖ _).mpr
    (not_isUnit_mk_of_mem_ker hϖ ρ ht), fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := (mem_specialFibrePlace hϖ).mp (mem_of_mem_nonunits_specialFibrePlace hϖ hx)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨b, hb⟩ := exists_mk_eq_mk_mul hϖ ρ hker
    ((specialFibreResidueMap_mem_nonunits_iff hϖ _).mp hx)
  refine (mem_specialFibrePlace hϖ).mpr ⟨Ideal.Quotient.mk _ b, ?_⟩
  rw [hb, map_mul, mul_comm, ← mul_assoc, inv_mul_cancel₀ hπ0, one_mul]

end Place

end SpecialFibre

end SpecialFibreValuation

section Main

open SpecialFibreValuation

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {A : Type*} [CommRing A] [IsNoetherianRing A] {F Ω : Type*} [Field F] [Field Ω]

/-- **The special-fibre valuation** (blueprint node N6c). -/
theorem exists_specialFibreValuation [IsDomain A] [Algebra R A] [FaithfulSMul R A]
    {ϖ : R} (hϖ : Irreducible ϖ) [IsDomain (A ⧸ Ideal.span {algebraMap R A ϖ})]
    [IsDiscreteValuationRing (A ⧸ Ideal.span {algebraMap R A ϖ})]
    [Algebra A Ω] [IsFractionRing A Ω] [Algebra R F] [IsFractionRing R F] [Algebra F Ω]
    [Algebra R Ω] [IsScalarTower R A Ω] [IsScalarTower R F Ω] :
    ∃ w : Valuation Ω ℤᵐ⁰, IsUniformizer (F := F) w (algebraMap R F ϖ) ∧
      (∀ r : R, w (algebraMap R Ω r) ≤ 1) ∧
      (∀ r ∈ maximalIdeal R, w (algebraMap R Ω r) < 1) ∧
      (∀ a : A, w (algebraMap A Ω a) < 1 ↔ a ∈ Ideal.span {algebraMap R A ϖ}) ∧
      ∀ g : Ω, w g ≤ 1 ↔ ∃ r s : A, s ∉ Ideal.span {algebraMap R A ϖ} ∧
        algebraMap A Ω s * g = algebraMap A Ω r := by
  refine ⟨specialFibreValuation A Ω hϖ, ⟨?_, ?_, fun x hx => ?_⟩,
    specialFibreValuation_algebraMap_base_le_one hϖ,
    specialFibreValuation_algebraMap_base_lt_one hϖ,
    specialFibreValuation_algebraMap_lt_one_iff hϖ, specialFibreValuation_le_one_iff hϖ⟩
  · exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hϖ.ne_zero
  · rw [← IsScalarTower.algebraMap_apply R F Ω]
    exact specialFibreValuation_algebraMap_base_lt_one hϖ ϖ
      ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hϖ.not_isUnit))
  · rw [← IsScalarTower.algebraMap_apply R F Ω]
    exact specialFibreValuation_eq_zpow hϖ hx

end Main

end ZInQ.Contrib.CMHeight62Full
