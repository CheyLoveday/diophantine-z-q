import ZInQKernel.Contrib.OneProof.CMHeight62Full.TreeStatements
import ZInQKernel.Contrib.OneProof.CMHeight62Full.LatticeFinite

/-!
# cmHeight62 (finite place): the algebraic core of the N6-bridge

Let `A` be a domain over a discrete valuation ring `R` with fraction field `k`, let `Ω` be the
fraction field of `A`, and let `Ψ : Ω ≃ₐ[k] F` identify `Ω` with a field `F` carrying a place
`P` of `F / k`. Assume that the valuation ring of `P`, read in `Ω`, is the localization of `A` at
`(t)` (`hgen`), that `t` is a uniformizer of `P` (`ht`), and that the localizations of `A` at the
horizontal height-one primes away from `t` are discrete valuation rings (`hhorDVR`). Then the
pole spaces `V_n = Ψ⁻¹ L(nP)` satisfy the three hypotheses `hpole`, `hreg` and `hzero` of
`exists_finite_span_of_poleBound` (`LatticeFinite.lean`).

* `placeOfDVR`: the place of `F / k` attached to a discrete valuation ring `D` with fraction
  field `Ω` whose image contains `k`; its valuation ring is `Ψ` of the image of `D`.
* `mem_range_of_mem_poleSpaceIn`, `mem_of_mem_poleSpaceIn`: an element of `V_n` lies in every
  such discrete valuation ring that differs from the generic one `genericSubring Ψ P`.
* `poleBounds_of_place`: `hpole`, `hreg` and `hzero` for `V_n`.
* `exists_finite_span_of_place`: the conclusion of `exists_finite_span_of_poleBound` for `V_n`.

Compared with the blueprint statement, `poleBounds_of_place` also assumes that `ϖ` is
irreducible: the horizontal primes are those not containing `ϖ`, and the constants `k` lie in the
localization at such a prime only when `ϖ` is a uniformizer of `R`. In `hhorDVR` the primality
of `𝔮` is an instance binder `[𝔮.IsPrime]`, so that `Localization.AtPrime 𝔮` is well formed. The
hypothesis `hfd` is kept in the blueprint shape; the proof does not need it.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

open IsLocalRing IsDedekindDomain

/-! ## The place of a discrete valuation ring of `Ω` -/

section PlaceOfDVR

variable {k F Ω : Type*} [Field k] [Field F] [Field Ω] [Algebra k F] [Algebra k Ω]

/-- The adic valuation of a discrete valuation ring `D` with fraction field `Ω` is at most one
exactly on the image of `D`. -/
theorem dvrValuation_le_one_iff (D : Type*) [CommRing D] [IsDomain D]
    [IsDiscreteValuationRing D] [Algebra D Ω] [IsFractionRing D Ω] (g : Ω) :
    (IsDiscreteValuationRing.maximalIdeal D).valuation Ω g ≤ 1 ↔
      g ∈ (algebraMap D Ω).range := by
  have h := IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring (A := D) (K := Ω)
  constructor
  · intro hg
    have hmem : g ∈ ((IsDiscreteValuationRing.maximalIdeal D).valuation Ω).valuationSubring :=
      (Valuation.mem_valuationSubring_iff _ _).mpr hg
    have hmem' : g ∈ ((IsDiscreteValuationRing.maximalIdeal D).valuation
        Ω).valuationSubring.toSubring := hmem
    rw [← h] at hmem'
    obtain ⟨x, -, rfl⟩ := Subring.mem_map.mp hmem'
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    have hmem : algebraMap D Ω x ∈ Subring.map (algebraMap D Ω) ⊤ :=
      Subring.mem_map.mpr ⟨x, trivial, rfl⟩
    rw [h] at hmem
    exact (Valuation.mem_valuationSubring_iff _ _).mp hmem

/-- A valuation which is at most one on `x` and on `x⁻¹` is one on `x`. -/
theorem valuation_eq_one_of_le_one_of_inv_le_one {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation Ω Γ₀) {x : Ω} (hx : x ≠ 0)
    (h1 : v x ≤ 1) (h2 : v x⁻¹ ≤ 1) : v x = 1 := by
  have hprod : v x * v x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  refine le_antisymm h1 (not_lt.mp fun hlt => hprod.not_lt ?_)
  calc v x * v x⁻¹ ≤ v x * 1 := by gcongr
    _ = v x := mul_one _
    _ < 1 := hlt

/-- **The place of a discrete valuation ring.** For a discrete valuation ring `D` with fraction
field `Ω` whose image contains `k`, the adic valuation of `D`, moved to `F` along `Ψ`, is a place
of `F / k`. -/
def placeOfDVR (Ψ : Ω ≃ₐ[k] F) (D : Type*) [CommRing D] [IsDomain D]
    [IsDiscreteValuationRing D] [Algebra D Ω] [IsFractionRing D Ω]
    (hk : ∀ c : k, algebraMap k Ω c ∈ (algebraMap D Ω).range) : TauCeti.Place k F where
  valuation := ((IsDiscreteValuationRing.maximalIdeal D).valuation Ω).comap
    Ψ.symm.toRingEquiv.toRingHom
  valuation_surjective := by
    intro γ
    obtain ⟨g, hg⟩ :=
      HeightOneSpectrum.valuation_surjective Ω (IsDiscreteValuationRing.maximalIdeal D) γ
    refine ⟨Ψ g, ?_⟩
    rw [Valuation.comap_apply]
    convert hg using 2
    exact Ψ.symm_apply_apply g
  isTrivialOn := by
    refine ⟨fun c hc => ?_⟩
    rw [Valuation.comap_apply]
    have hcomm : Ψ.symm.toRingEquiv.toRingHom (algebraMap k F c) = algebraMap k Ω c :=
      Ψ.symm.commutes c
    rw [hcomm]
    refine valuation_eq_one_of_le_one_of_inv_le_one _
      ((map_ne_zero_iff _ (algebraMap k Ω).injective).mpr hc)
      ((dvrValuation_le_one_iff D _).mpr (hk c)) ?_
    rw [← map_inv₀]
    exact (dvrValuation_le_one_iff D _).mpr (hk c⁻¹)

theorem placeOfDVR_valuation (Ψ : Ω ≃ₐ[k] F) (D : Type*) [CommRing D] [IsDomain D]
    [IsDiscreteValuationRing D] [Algebra D Ω] [IsFractionRing D Ω]
    (hk : ∀ c : k, algebraMap k Ω c ∈ (algebraMap D Ω).range) (x : F) :
    (placeOfDVR Ψ D hk).valuation x =
      (IsDiscreteValuationRing.maximalIdeal D).valuation Ω (Ψ.symm x) :=
  rfl

/-- The valuation ring of `placeOfDVR`, read in `Ω`, is the image of `D`. -/
theorem placeOfDVR_valuation_apply_le_one_iff (Ψ : Ω ≃ₐ[k] F) (D : Type*) [CommRing D]
    [IsDomain D] [IsDiscreteValuationRing D] [Algebra D Ω] [IsFractionRing D Ω]
    (hk : ∀ c : k, algebraMap k Ω c ∈ (algebraMap D Ω).range) (g : Ω) :
    (placeOfDVR Ψ D hk).valuation (Ψ g) ≤ 1 ↔ g ∈ (algebraMap D Ω).range := by
  rw [placeOfDVR_valuation, Ψ.symm_apply_apply, dvrValuation_le_one_iff]

/-- The valuation subring `{g | v_P (Ψ g) ≤ 1}` of `Ω`: the generic one. -/
def genericSubring (Ψ : Ω ≃ₐ[k] F) (P : TauCeti.Place k F) : ValuationSubring Ω :=
  P.integers.comap Ψ.toRingEquiv.toRingHom

theorem mem_genericSubring_iff (Ψ : Ω ≃ₐ[k] F) (P : TauCeti.Place k F) (g : Ω) :
    g ∈ genericSubring Ψ P ↔ P.valuation (Ψ g) ≤ 1 :=
  ValuationSubring.mem_comap.trans P.mem_integers_iff

/-- **Regularity away from `P`.** An element of `V_n = Ψ⁻¹ L(nP)` lies in the image of every
discrete valuation ring `D` with fraction field `Ω` whose image contains `k` and is not the
generic valuation ring. -/
theorem mem_range_of_mem_poleSpaceIn (Ψ : Ω ≃ₐ[k] F) (P : TauCeti.Place k F) {n : ℕ} {f : Ω}
    (hf : f ∈ poleSpaceIn Ψ P n) (D : Type*) [CommRing D] [IsDomain D]
    [IsDiscreteValuationRing D] [Algebra D Ω] [IsFractionRing D Ω]
    (hk : ∀ c : k, algebraMap k Ω c ∈ (algebraMap D Ω).range)
    (hne : ∃ g : Ω, ¬ (P.valuation (Ψ g) ≤ 1 ↔ g ∈ (algebraMap D Ω).range)) :
    f ∈ (algebraMap D Ω).range := by
  have hQ : placeOfDVR Ψ D hk ≠ P := by
    rintro hQP
    obtain ⟨g, hg⟩ := hne
    apply hg
    rw [← hQP, placeOfDVR_valuation_apply_le_one_iff]
  have h := ((mem_poleSpaceIn_iff Ψ P n f).mp hf).1 _ hQ
  exact (placeOfDVR_valuation_apply_le_one_iff Ψ D hk f).mp h

/-- **The companion `mem_of_mem_poleSpaceIn`.** An element of `V_n` lies in every discrete
valuation subring of `Ω` that contains `k` and differs from `genericSubring Ψ P`. -/
theorem mem_of_mem_poleSpaceIn (Ψ : Ω ≃ₐ[k] F) (P : TauCeti.Place k F) {n : ℕ} {f : Ω}
    (hf : f ∈ poleSpaceIn Ψ P n) (Q : ValuationSubring Ω) (hQ : IsDiscreteValuationRing Q)
    (hk : ∀ c : k, algebraMap k Ω c ∈ Q) (hne : Q ≠ genericSubring Ψ P) : f ∈ Q := by
  have hr : ∀ g : Ω, g ∈ (algebraMap Q Ω).range ↔ g ∈ Q := by
    intro g
    constructor
    · rintro ⟨x, rfl⟩
      rw [ValuationSubring.algebraMap_apply]
      exact x.2
    · intro h
      exact ⟨⟨g, h⟩, ValuationSubring.algebraMap_apply Q ⟨g, h⟩⟩
  refine (hr f).mp (mem_range_of_mem_poleSpaceIn Ψ P hf Q (fun c => (hr _).mpr (hk c)) ?_)
  by_contra h
  simp only [not_exists, not_not] at h
  apply hne
  ext g
  rw [mem_genericSubring_iff, h g, hr g]

end PlaceOfDVR

/-! ## Localizations of `A` at primes as subrings of `Ω` -/

section Localization

variable {A Ω : Type*} [CommRing A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω]

theorem isUnit_algebraMap_primeCompl (𝔮 : Ideal A) [𝔮.IsPrime] (y : 𝔮.primeCompl) :
    IsUnit (algebraMap A Ω y) := by
  refine isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective A Ω)).mpr ?_)
  intro h
  exact y.2 (h ▸ 𝔮.zero_mem)

/-- The map `A_𝔮 → Ω`, as an algebra structure. -/
abbrev atPrimeAlgebra (𝔮 : Ideal A) [𝔮.IsPrime] : Algebra (Localization.AtPrime 𝔮) Ω :=
  (IsLocalization.lift (M := 𝔮.primeCompl) (S := Localization.AtPrime 𝔮)
    (isUnit_algebraMap_primeCompl (Ω := Ω) 𝔮)).toAlgebra

theorem atPrime_isScalarTower (𝔮 : Ideal A) [𝔮.IsPrime] :
    letI := atPrimeAlgebra (Ω := Ω) 𝔮
    IsScalarTower A (Localization.AtPrime 𝔮) Ω := by
  let := atPrimeAlgebra (Ω := Ω) 𝔮
  exact IsScalarTower.of_algebraMap_eq fun a => (IsLocalization.lift_eq _ a).symm

theorem atPrime_isFractionRing [IsDomain A] (𝔮 : Ideal A) [𝔮.IsPrime] :
    letI := atPrimeAlgebra (Ω := Ω) 𝔮
    IsFractionRing (Localization.AtPrime 𝔮) Ω := by
  let := atPrimeAlgebra (Ω := Ω) 𝔮
  have := atPrime_isScalarTower (Ω := Ω) 𝔮
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔮.primeCompl _ _

/-- The image of `A_𝔮` in `Ω` is the set of fractions `r / s` with `s ∉ 𝔮`. -/
theorem atPrime_mem_range_iff (𝔮 : Ideal A) [𝔮.IsPrime] (g : Ω) :
    letI := atPrimeAlgebra (Ω := Ω) 𝔮
    g ∈ (algebraMap (Localization.AtPrime 𝔮) Ω).range ↔
      ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * g = algebraMap A Ω r := by
  let := atPrimeAlgebra (Ω := Ω) 𝔮
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl x
    exact ⟨r, s, s.2, ((IsLocalization.lift_mk'_spec _ r g s).mp hx).symm⟩
  · rintro ⟨r, s, hs, h⟩
    exact ⟨IsLocalization.mk' _ r (⟨s, hs⟩ : 𝔮.primeCompl),
      (IsLocalization.lift_mk'_spec _ r g ⟨s, hs⟩).mpr h.symm⟩

end Localization

/-! ## The pole bounds -/

section PoleBounds

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {k : Type*} [Field k] [Algebra R k] [IsFractionRing R k] {A : Type*} [CommRing A] [IsDomain A]
  [Algebra R A] {Ω F : Type*} [Field Ω] [Field F] [Algebra A Ω] [IsFractionRing A Ω] [Algebra k Ω]
  [Algebra R Ω] [IsScalarTower R A Ω] [IsScalarTower R k Ω] [Algebra k F]

omit [IsDomain A] in
/-- A nonzero element of `R` maps outside every prime of `A` that does not contain the image of
the uniformizer. -/
theorem algebraMap_notMem_of_ne_zero {ϖ : R} (hϖ : Irreducible ϖ) (𝔮 : Ideal A) [𝔮.IsPrime]
    (hϖ𝔮 : algebraMap R A ϖ ∉ 𝔮) {b : R} (hb : b ≠ 0) : algebraMap R A b ∉ 𝔮 := by
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  rw [map_mul, map_pow]
  intro h
  rcases Ideal.IsPrime.mem_or_mem ‹_› h with hu | hp
  · exact Ideal.IsPrime.ne_top ‹_›
      (Ideal.eq_top_of_isUnit_mem _ hu ((u.isUnit).map (algebraMap R A)))
  · exact hϖ𝔮 (Ideal.IsPrime.mem_of_pow_mem ‹_› m hp)

omit [IsDomain A] in
/-- The constants `k` lie in the image of `A_𝔮` for a prime `𝔮` not containing `ϖ`. -/
theorem algebraMap_mem_atPrime {ϖ : R} (hϖ : Irreducible ϖ) (𝔮 : Ideal A) [𝔮.IsPrime]
    (hϖ𝔮 : algebraMap R A ϖ ∉ 𝔮) (c : k) :
    ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * algebraMap k Ω c = algebraMap A Ω r := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hs := algebraMap_notMem_of_ne_zero hϖ 𝔮 hϖ𝔮 hb0
  have hs0 : algebraMap A Ω (algebraMap R A b) ≠ 0 := by
    refine (map_ne_zero_iff _ (IsFractionRing.injective A Ω)).mpr ?_
    intro h
    exact hs (h ▸ 𝔮.zero_mem)
  refine ⟨algebraMap R A a, algebraMap R A b, hs, ?_⟩
  rw [map_div₀, ← IsScalarTower.algebraMap_apply R k Ω, ← IsScalarTower.algebraMap_apply R k Ω,
    IsScalarTower.algebraMap_apply R A Ω a, IsScalarTower.algebraMap_apply R A Ω b,
    mul_div_cancel₀ _ hs0]

/-- **N6-bridge, algebraic core.** From a place `P` of `F / k`, an isomorphism `Ψ : Ω ≃ₐ[k] F`
matching the valuation ring of `P` with the localization of `A` at `(t)` (`hgen`), `t` a
uniformizer of `P` (`ht`), discrete valuation rings at the horizontal height-one primes away from
`t` (`hhorDVR`) and `L(P) = k` (`hdim1`): the pole spaces `V_n = Ψ⁻¹ L(nP)` satisfy `hpole`,
`hreg` and `hzero` of `exists_finite_span_of_poleBound`. -/
theorem poleBounds_of_place (Ψ : Ω ≃ₐ[k] F) (P : TauCeti.Place k F) {ϖ : R} (hϖ : Irreducible ϖ)
    {t : A}
    (hgen : ∀ g : Ω, P.valuation (Ψ g) ≤ 1 ↔
      ∃ r s : A, s ∉ Ideal.span {t} ∧ algebraMap A Ω s * g = algebraMap A Ω r)
    (ht : P.valuation (Ψ (algebraMap A Ω t)) = WithZero.exp (-1 : ℤ))
    (hhorDVR : ∀ (𝔮 : Ideal A) [𝔮.IsPrime], 𝔮.height = 1 → algebraMap R A ϖ ∉ 𝔮 → t ∉ 𝔮 →
      IsDiscreteValuationRing (Localization.AtPrime 𝔮))
    (hdim1 : TauCeti.Divisor.dim (Finsupp.single P (1 : ℤ) : TauCeti.Divisor k F) = 1)
    (_hfd : ∀ n : ℕ, FiniteDimensional k (poleSpace P n)) (n : ℕ) :
    (∀ f ∈ poleSpaceIn Ψ P n, ∃ r s : A, s ∉ Ideal.span {t} ∧
        algebraMap A Ω s * (f * algebraMap A Ω t ^ n) = algebraMap A Ω r) ∧
      (∀ f ∈ poleSpaceIn Ψ P n, ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 →
        algebraMap R A ϖ ∉ 𝔮 → t ∉ 𝔮 → ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * f = algebraMap A Ω r) ∧
      (∀ f ∈ poleSpaceIn Ψ P n, ∀ a : A, f = algebraMap A Ω (t * a) → f = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · -- `hpole`: `v_P (Ψ (f tⁿ)) ≤ exp 1 ^ n * exp (-1) ^ n = 1`.
    intro f hf
    have hv := ((mem_poleSpaceIn_iff Ψ P n f).mp hf).2
    apply (hgen _).mp
    rw [map_mul, map_pow, map_mul, map_pow, ht]
    calc P.valuation (Ψ f) * WithZero.exp (-1 : ℤ) ^ n
        ≤ WithZero.exp (1 : ℤ) ^ n * WithZero.exp (-1 : ℤ) ^ n := by gcongr
      _ = 1 := by rw [← mul_pow, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_pow]
  · -- `hreg`: `A_𝔮` is a discrete valuation ring of `Ω` containing `k`, in which `t` is a unit.
    intro f hf 𝔮 h𝔮 h1 hϖ𝔮 ht𝔮
    let := atPrimeAlgebra (Ω := Ω) 𝔮
    have := atPrime_isFractionRing (Ω := Ω) 𝔮
    have := hhorDVR 𝔮 h1 hϖ𝔮 ht𝔮
    have hk : ∀ c : k, algebraMap k Ω c ∈ (algebraMap (Localization.AtPrime 𝔮) Ω).range :=
      fun c => (atPrime_mem_range_iff 𝔮 _).mpr (algebraMap_mem_atPrime hϖ 𝔮 hϖ𝔮 c)
    have ht0 : algebraMap A Ω t ≠ 0 := by
      refine (map_ne_zero_iff _ (IsFractionRing.injective A Ω)).mpr ?_
      intro h
      exact ht𝔮 (h ▸ 𝔮.zero_mem)
    refine (atPrime_mem_range_iff 𝔮 f).mp
      (mem_range_of_mem_poleSpaceIn Ψ P hf (Localization.AtPrime 𝔮) hk ⟨(algebraMap A Ω t)⁻¹, ?_⟩)
    intro hiff
    have hmem : (algebraMap A Ω t)⁻¹ ∈ (algebraMap (Localization.AtPrime 𝔮) Ω).range :=
      (atPrime_mem_range_iff 𝔮 _).mpr ⟨1, t, ht𝔮, by rw [mul_inv_cancel₀ ht0, map_one]⟩
    have hle := hiff.mpr hmem
    rw [map_inv₀, map_inv₀, ht, ← WithZero.exp_neg, neg_neg] at hle
    exact absurd hle (not_le.mpr one_lt_exp_one_int)
  · -- `hzero`: `t a` is regular everywhere and vanishes at `P`, so it is a constant of
    -- valuation `< 1`, hence zero.
    intro f hf a hfa
    have hT : (1 : A) ∉ Ideal.span {t} := by
      intro h1
      obtain ⟨r, s, hs, -⟩ := (hgen 0).mp (by rw [map_zero, map_zero]; exact zero_le_one)
      exact hs ((Ideal.eq_top_iff_one _).mpr h1 ▸ Submodule.mem_top)
    have ha : P.valuation (Ψ (algebraMap A Ω a)) ≤ 1 :=
      (hgen _).mpr ⟨a, 1, hT, by rw [map_one, one_mul]⟩
    have hexp : WithZero.exp (-1 : ℤ) < 1 := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by norm_num)
    have hlt : P.valuation (Ψ f) < 1 := by
      rw [hfa, map_mul, map_mul, map_mul, ht]
      calc WithZero.exp (-1 : ℤ) * P.valuation (Ψ (algebraMap A Ω a))
          ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact hexp
    have hmem : Ψ f ∈ poleSpace P 1 :=
      (mem_poleSpace_iff P 1 _).mpr ⟨((mem_poleSpaceIn_iff Ψ P n f).mp hf).1,
        by rw [pow_one]; exact hlt.le.trans one_lt_exp_one_int.le⟩
    have hfr : Module.finrank k (poleSpace P 1) = 1 := by
      rw [TauCeti.Divisor.dim_def] at hdim1
      unfold poleSpace
      rw [Nat.cast_one]
      exact hdim1
    have h10 : (⟨1, one_mem_poleSpace P⟩ : poleSpace P 1) ≠ 0 := by
      intro h
      exact one_ne_zero (congrArg Subtype.val h)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ h10).mp hfr ⟨Ψ f, hmem⟩
    have hc' : algebraMap k F c = Ψ f := by
      have := congrArg Subtype.val hc
      simpa [Algebra.smul_def] using this
    by_cases hc0 : c = 0
    · rw [hc0, map_zero] at hc'
      exact Ψ.injective (by rw [← hc', map_zero])
    · have h1 := Valuation.IsTrivialOn.eq_one (v := P.valuation) c hc0
      rw [hc'] at h1
      exact absurd hlt (by rw [h1]; exact lt_irrefl 1)

/-- **N6-bridge feeding N8b.** With the inputs of `poleBounds_of_place` and those of
`exists_finite_span_of_poleBound` other than `hpole`, `hreg`, `hzero`, the lattice `V_n ∩ 𝒪_w`
lies in the span of finitely many elements over the `w`-integral constants. -/
theorem exists_finite_span_of_place {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (Ψ : Ω ≃ₐ[k] F) (P : TauCeti.Place k F) {ϖ : R} (hϖ : Irreducible ϖ) {t : A}
    (hgen : ∀ g : Ω, P.valuation (Ψ g) ≤ 1 ↔
      ∃ r s : A, s ∉ Ideal.span {t} ∧ algebraMap A Ω s * g = algebraMap A Ω r)
    (ht : P.valuation (Ψ (algebraMap A Ω t)) = WithZero.exp (-1 : ℤ))
    (hhorDVR : ∀ (𝔮 : Ideal A) [𝔮.IsPrime], 𝔮.height = 1 → algebraMap R A ϖ ∉ 𝔮 → t ∉ 𝔮 →
      IsDiscreteValuationRing (Localization.AtPrime 𝔮))
    (hdim1 : TauCeti.Divisor.dim (Finsupp.single P (1 : ℤ) : TauCeti.Divisor k F) = 1)
    (hfd : ∀ n : ℕ, FiniteDimensional k (poleSpace P n))
    (w : Valuation Ω Γ₀) (ρ : A →ₐ[R] R) (hker : RingHom.ker ρ = Ideal.span {t})
    (hhart : ∀ g : Ω, (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 →
      ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * g = algebraMap A Ω r) → g ∈ (algebraMap A Ω).range)
    (hcases : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → algebraMap R A ϖ ∈ 𝔮 →
      𝔮 = Ideal.span {algebraMap R A ϖ})
    (hw : ∀ g : Ω, w g ≤ 1 → ∃ r s : A, s ∉ Ideal.span {algebraMap R A ϖ} ∧
      algebraMap A Ω s * g = algebraMap A Ω r)
    (hwA : ∀ a : A, w (algebraMap A Ω a) ≤ 1) (n : ℕ) :
    ∃ (m : ℕ) (b : Fin m → Ω), ∀ x ∈ poleSpaceIn Ψ P n, w x ≤ 1 → ∃ c : Fin m → k,
      (∀ j, w (algebraMap k Ω (c j)) ≤ 1) ∧ x = ∑ j, algebraMap k Ω (c j) * b j := by
  obtain ⟨hpole, hreg, hzero⟩ := poleBounds_of_place Ψ P hϖ hgen ht hhorDVR hdim1 hfd n
  exact exists_finite_span_of_poleBound w ρ hker hϖ hhart hcases hw hwA (poleSpaceIn Ψ P n) n
    hpole hreg hzero

end PoleBounds

end ZInQ.Contrib.CMHeight62Full
