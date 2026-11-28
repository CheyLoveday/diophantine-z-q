import Mathlib
import ZInQKernel.Contrib.OneProof.CMHeight62Full.DepthTwoHartogs
import ZInQKernel.Contrib.OneProof.CMHeight62Full.IdentityPointDepth
import ZInQKernel.Contrib.OneProof.CMHeight62Full.SpecialFibreFunctionField

/-!
# Centres of constant places (node N9-bridge, part B2: the hypothesis `hcentre`)

`SpecialFibreFunctionField.reduce_mem_polePart` takes a hypothesis `hcentre`: every constant
place `O ≠ ē` of the residue field `κ_w` has a centre `A_c ⊆ Ω` dominated by the composite ring
`Õ`, with the Hartogs property, whose height-one primes through `ϖ` are controlled by `w`, and at
whose other height-one primes `f` is regular. This file produces it.

**Local algebra.** Let `A_c` be a local Noetherian subring of `Ω` with fraction field `Ω`, `ϖ` a
nonzerodivisor in its maximal ideal with `A_c / ϖ` a discrete valuation ring.

* `centre_hartogs`: Hartogs at `A_c` (the depth-two lemma).
* `centre_val_eq_one`: if `w ≤ 1` on `A_c`, `w ϖ < 1` and `w` is not centred at the closed point
  (some `c ∈ 𝔪` has `w c = 1`), then `w = 1` off `(ϖ)`.
* `centre_vertical`: under the same hypotheses, every `g` with `w g ≤ 1` lies in `(A_c)_𝔮` for
  the height-one primes `𝔮 ∋ ϖ` (they all equal `(ϖ)`).
* `centre_spec`: the four clauses of `hcentre` for one place.

**The trivial place.** `O = ⊤` is a constant place, and its centre is `𝒪_w` itself:
`isDiscreteValuationRing_valuationSubring` (a discrete `w` has a DVR as valuation ring) and
`centre_spec_top`.

**Assembly.** `hcentre_of_centres`: `hcentre` from centres at the nontrivial constant places.

Only Mathlib and the earlier files of this directory are used.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62Full

namespace Centre

open IsLocalRing SpecialFibreFunctionField

section DVR

/-- In a discrete valuation ring, every element of the maximal ideal has a power divisible by a
given nonzero element. -/
theorem dvd_pow_of_mem_maximalIdeal {S : Type*} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] {x y : S} (hx : x ≠ 0) (hy : y ∈ maximalIdeal S) :
    ∃ N : ℕ, x ∣ y ^ N := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  refine ⟨n, ?_⟩
  rw [Units.mul_left_dvd]
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hy
  exact pow_dvd_pow_of_dvd hy n

end DVR

section Local

variable {Ω : Type*} [Field Ω] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (w : Valuation Ω Γ₀)
variable {Ac : Subring Ω} [IsLocalRing Ac] [IsNoetherianRing Ac] {ϖ : Ac}
  (hϖ : ϖ ∈ nonZeroDivisors Ac) (hm : ϖ ∈ maximalIdeal Ac)
  [IsDomain (Ac ⧸ Ideal.span {ϖ})] [IsDiscreteValuationRing (Ac ⧸ Ideal.span {ϖ})]

include hϖ hm

/-- **Hartogs at a centre.** -/
theorem centre_hartogs [IsFractionRing Ac Ω] (g : Ω)
    (hg : ∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r) :
    g ∈ Ac := by
  obtain ⟨a, ha⟩ := depthTwo_mem_range hϖ hm g hg
  rw [← ha]
  exact a.2

omit [IsNoetherianRing Ac] hϖ in
/-- If `w ≤ 1` on `A_c`, `w ϖ < 1`, and some element of the maximal ideal has value one, then
`w = 1` off `(ϖ)`. -/
theorem centre_val_eq_one (hAw : ∀ a : Ac, w a ≤ 1) (hϖw : w ϖ < 1)
    (hcen : ∃ c ∈ maximalIdeal Ac, w c = 1) {b : Ac} (hb : b ∉ Ideal.span {ϖ}) : w b = 1 := by
  obtain ⟨c, hc, hc1⟩ := hcen
  by_contra hne
  have hlt : w b < 1 := lt_of_le_of_ne (hAw b) hne
  have hb0 : Ideal.Quotient.mk (Ideal.span {ϖ}) b ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hcm : Ideal.Quotient.mk (Ideal.span {ϖ}) c ∈ maximalIdeal (Ac ⧸ Ideal.span {ϖ}) := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : Ac ⧸ Ideal.span {ϖ})
    have h1 : Ideal.Quotient.mk (Ideal.span {ϖ}) (c * d - 1) = 0 := by
      rw [map_sub, map_mul, hd, ← hu, map_one, Units.mul_inv, sub_self]
    rw [Ideal.Quotient.eq_zero_iff_mem] at h1
    have h2 : c * d - 1 ∈ maximalIdeal Ac :=
      (Ideal.span_singleton_le_iff_mem _).mpr hm h1
    have h3 : c * d ∈ maximalIdeal Ac := Ideal.mul_mem_right d _ hc
    have h4 : (1 : Ac) ∈ maximalIdeal Ac := by
      have := Ideal.sub_mem _ h3 h2
      rwa [sub_sub_cancel] at this
    exact (maximalIdeal.isMaximal Ac).ne_top ((Ideal.eq_top_iff_one _).mpr h4)
  obtain ⟨N, d, hd⟩ := dvd_pow_of_mem_maximalIdeal hb0 hcm
  obtain ⟨d', rfl⟩ := Ideal.Quotient.mk_surjective d
  have hmem : c ^ N - b * d' ∈ Ideal.span {ϖ} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_mul, hd, sub_self]
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hmem
  have hcN : w ((c : Ω) ^ N) = 1 := by rw [map_pow, hc1, one_pow]
  have heq : ((c : Ω) ^ N) = (b : Ω) * d' + e * ϖ := by
    have := congrArg (fun x : Ac => (x : Ω)) he
    push_cast at this
    linear_combination -this
  have h1 : w ((b : Ω) * d') < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hAw d')) hlt
  have h2 : w ((e : Ω) * ϖ) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hAw e)) hϖw
  have h3 := Valuation.map_add_lt w h1 h2
  rw [← heq, hcN] at h3
  exact lt_irrefl _ h3

/-- **Vertical primes.** Every height-one prime through `ϖ` is `(ϖ)`, and every `g` with
`w g ≤ 1` is a fraction with denominator outside `(ϖ)`. -/
theorem centre_vertical [IsFractionRing Ac Ω] (hAw : ∀ a : Ac, w a ≤ 1) (hϖw : w ϖ < 1)
    (hcen : ∃ c ∈ maximalIdeal Ac, w c = 1) (𝔮 : Ideal Ac) (hq : 𝔮.IsPrime) (h1 : 𝔮.height = 1)
    (hϖq : ϖ ∈ 𝔮) (g : Ω) (hg : w g ≤ 1) : ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r := by
  have h𝔮 := depthTwo_height_one_cases hϖ hm 𝔮 h1 hϖq
  subst h𝔮
  have hP := depthTwo_isPrime hϖ hm
  have := depthTwo_isDomain hϖ hm
  have hϖ0 : (ϖ : Ω) ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hϖ (Subtype.ext h)
  by_cases hg0 : g = 0
  · refine ⟨0, 1, fun h => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h), ?_⟩
    rw [hg0, mul_zero]
    rfl
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Ac) g
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbΩ : (b : Ω) ≠ 0 := fun h => hb0 (Subtype.ext h)
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hg0
    rw [← hab]
    simp
  obtain ⟨n, a', ha', rfl⟩ := depthTwo_exists_pow_mul hϖ hm ha0
  obtain ⟨k, b', hb', rfl⟩ := depthTwo_exists_pow_mul hϖ hm hb0
  have hgb : g * ((ϖ ^ k * b' : Ac) : Ω) = ((ϖ ^ n * a' : Ac) : Ω) := by
    rw [← hab]
    exact div_mul_cancel₀ _ hbΩ
  push_cast at hgb
  have hwa : w (a' : Ω) = 1 := centre_val_eq_one w hm hAw hϖw hcen ha'
  rcases le_or_gt k n with hkn | hnk
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
    refine ⟨ϖ ^ j * a', b', hb', ?_⟩
    have hk0 : (ϖ : Ω) ^ k ≠ 0 := pow_ne_zero _ hϖ0
    apply mul_left_cancel₀ hk0
    push_cast
    rw [pow_add] at hgb
    linear_combination hgb
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hnk
    exfalso
    have hn0 : (ϖ : Ω) ^ n ≠ 0 := pow_ne_zero _ hϖ0
    have hrel : g * (ϖ : Ω) ^ (j + 1) * b' = a' := by
      apply mul_left_cancel₀ hn0
      rw [pow_add] at hgb
      linear_combination hgb
    have hb'1 : w (b' : Ω) ≤ 1 := hAw b'
    have hlt : w (g * (ϖ : Ω) ^ (j + 1) * b') < 1 := by
      rw [map_mul, map_mul, map_pow]
      refine lt_of_le_of_lt (mul_le_of_le_one_right' hb'1) ?_
      refine lt_of_le_of_lt (mul_le_of_le_one_left' hg) ?_
      exact pow_lt_one₀ zero_le hϖw (Nat.succ_ne_zero j)
    rw [hrel, hwa] at hlt
    exact lt_irrefl _ hlt

/-- **The four clauses of `hcentre` at one place.** -/
theorem centre_spec [IsFractionRing Ac Ω] (O : ValuationSubring (ResidueField w.valuationSubring))
    (hdom : ∀ a ∈ Ac, a ∈ liftValuationSubring w O) (hϖw : w ϖ < 1)
    (hcen : ∃ c ∈ maximalIdeal Ac, w c = 1) {f : Ω}
    (hhor : ∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → ϖ ∉ 𝔮 →
      ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * f = r) :
    (∀ a ∈ Ac, a ∈ liftValuationSubring w O) ∧
      (∀ g : Ω, (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 →
        ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r) → g ∈ Ac) ∧
      (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → ϖ ∈ 𝔮 → ∀ g : Ω, w g ≤ 1 →
        ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r) ∧
      (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → ϖ ∉ 𝔮 →
        ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * f = r) := by
  have hAw : ∀ a : Ac, w a ≤ 1 := fun a =>
    (w.mem_valuationSubring_iff _).mp (liftValuationSubring_le O (hdom a a.2))
  exact ⟨hdom, centre_hartogs hϖ hm, fun 𝔮 hq h1 hϖq g hg =>
    centre_vertical w hϖ hm hAw hϖw hcen 𝔮 hq h1 hϖq g hg, hhor⟩

end Local

section Top

variable {Ω : Type*} [Field Ω] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (w : Valuation Ω Γ₀) {ϖw : Ω}

/-- The element `ϖ` of `𝒪_w`. -/
def topUniformizer (hϖw : w ϖw < 1) : w.valuationSubring.toSubring :=
  ⟨ϖw, (w.mem_valuationSubring_iff ϖw).2 hϖw.le⟩

variable (hϖ0 : ϖw ≠ 0) (hϖw : w ϖw < 1)
  (hdisc : ∀ x : Ω, x ≠ 0 → ∃ m : ℤ, w x = w ϖw ^ m)
include hϖ0 hϖw hdisc

/-- A nonzero element with `w ≤ 1` has value a natural power of `w ϖ`. -/
theorem exists_nat_of_le_one {x : Ω} (hx0 : x ≠ 0) (hx : w x ≤ 1) :
    ∃ n : ℕ, w x = w ϖw ^ n := by
  obtain ⟨m, hm⟩ := hdisc x hx0
  rcases m with n | k
  · refine ⟨n, ?_⟩
    rw [hm, Int.ofNat_eq_natCast, zpow_natCast]
  · exfalso
    have hw0 : w ϖw ≠ 0 := (Valuation.ne_zero_iff w).mpr hϖ0
    have h1 : w x * w ϖw ^ (k + 1) = 1 := by
      rw [hm, zpow_negSucc, inv_mul_cancel₀ (pow_ne_zero _ hw0)]
    have h2 : w x * w ϖw ^ (k + 1) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' hx)
        (pow_lt_one₀ zero_le hϖw (Nat.succ_ne_zero k))
    rw [h1] at h2
    exact lt_irrefl _ h2

omit hϖ0 hϖw hdisc in
/-- Elements of value one are units of `𝒪_w`. -/
theorem isUnit_of_val_eq_one (a : w.valuationSubring.toSubring) (ha : w (a : Ω) = 1) :
    IsUnit a := by
  have ha0 : (a : Ω) ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact zero_ne_one ha
  have hmem : (a : Ω)⁻¹ ∈ w.valuationSubring.toSubring := by
    refine (w.mem_valuationSubring_iff _).2 ?_
    rw [map_inv₀, ha, inv_one]
  exact isUnit_iff_exists_inv.mpr ⟨⟨(a : Ω)⁻¹, hmem⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

/-- Every nonzero element of `𝒪_w` is associated to a power of `ϖ`. -/
theorem exists_associated_pow (x : w.valuationSubring.toSubring) (hx : x ≠ 0) :
    ∃ n : ℕ, Associated (topUniformizer w hϖw ^ n) x := by
  have hx0 : (x : Ω) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨n, hn⟩ := exists_nat_of_le_one w hϖ0 hϖw hdisc hx0
    ((w.mem_valuationSubring_iff _).1 x.2)
  have hw0 : w ϖw ≠ 0 := (Valuation.ne_zero_iff w).mpr hϖ0
  have hpn : ϖw ^ n ≠ 0 := pow_ne_zero _ hϖ0
  have hu1 : w ((x : Ω) / ϖw ^ n) = 1 := by
    rw [map_div₀, map_pow, hn, div_self (pow_ne_zero _ hw0)]
  let u : w.valuationSubring.toSubring :=
    ⟨(x : Ω) / ϖw ^ n, (w.mem_valuationSubring_iff _).2 hu1.le⟩
  have hu : IsUnit u := isUnit_of_val_eq_one w u hu1
  refine ⟨n, hu.unit, Subtype.ext ?_⟩
  rw [IsUnit.unit_spec, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  change ϖw ^ n * ((x : Ω) / ϖw ^ n) = x
  exact mul_div_cancel₀ _ hpn

/-- A nonunit nonzero element of `𝒪_w` has value at most `w ϖ`. -/
theorem val_le_of_lt_one {x : Ω} (hx0 : x ≠ 0) (hx : w x < 1) : w x ≤ w ϖw := by
  obtain ⟨n, hn⟩ := exists_nat_of_le_one w hϖ0 hϖw hdisc hx0 hx.le
  rcases n with _ | m
  · rw [hn, pow_zero] at hx
    exact absurd hx (lt_irrefl _)
  · rw [hn, pow_succ]
    exact mul_le_of_le_one_left' (pow_le_one₀ zero_le hϖw.le)

/-- `ϖ` is irreducible in `𝒪_w`. -/
theorem irreducible_topUniformizer : Irreducible (topUniformizer w hϖw) := by
  have hw0 : w ϖw ≠ 0 := (Valuation.ne_zero_iff w).mpr hϖ0
  refine ⟨?_, ?_⟩
  · rintro ⟨u, hu⟩
    have h := congrArg (fun y : w.valuationSubring.toSubring => w (y : Ω)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one, map_mul, map_one] at h
    rw [hu] at h
    have h2 : w (topUniformizer w hϖw : Ω) * w (((u⁻¹ : _ˣ) : w.valuationSubring.toSubring) : Ω)
        < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right'
        ((w.mem_valuationSubring_iff _).1 (u⁻¹ : _ˣ).1.2)) hϖw
    rw [h] at h2
    exact lt_irrefl _ h2
  · intro a b hab
    have h := congrArg (fun y : w.valuationSubring.toSubring => w (y : Ω)) hab
    simp only [MulMemClass.coe_mul, map_mul] at h
    change w ϖw = w (a : Ω) * w (b : Ω) at h
    have ha1 : w (a : Ω) ≤ 1 := (w.mem_valuationSubring_iff _).1 a.2
    have hb1 : w (b : Ω) ≤ 1 := (w.mem_valuationSubring_iff _).1 b.2
    by_cases ha : w (a : Ω) = 1
    · exact Or.inl (isUnit_of_val_eq_one w a ha)
    by_cases hb : w (b : Ω) = 1
    · exact Or.inr (isUnit_of_val_eq_one w b hb)
    exfalso
    have ha0 : (a : Ω) ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at h
      exact hw0 h
    have hale := val_le_of_lt_one w hϖ0 hϖw hdisc ha0 (lt_of_le_of_ne ha1 ha)
    have hpos : 0 < w ϖw := lt_of_le_of_ne zero_le (Ne.symm hw0)
    have h3 : w (a : Ω) * w (b : Ω) < w ϖw :=
      calc w (a : Ω) * w (b : Ω) ≤ w ϖw * w (b : Ω) := mul_le_mul_of_nonneg_right hale zero_le
        _ < w ϖw := mul_lt_of_lt_one_right hpos (lt_of_le_of_ne hb1 hb)
    rw [← h] at h3
    exact lt_irrefl _ h3

/-- **`𝒪_w` is a discrete valuation ring** when `w` is discrete with uniformizer `ϖ`. -/
theorem isDiscreteValuationRing_valuationSubring :
    IsDiscreteValuationRing w.valuationSubring.toSubring :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨topUniformizer w hϖw, irreducible_topUniformizer w hϖ0 hϖw hdisc,
      fun {x} hx => exists_associated_pow w hϖ0 hϖw hdisc x hx⟩

/-- **The trivial place.** Its centre is `𝒪_w`, with `ϖ`. -/
theorem centre_spec_top (f : Ω) :
    ∃ (Ac : Subring Ω) (ϖ : Ac), (∀ a ∈ Ac, a ∈ liftValuationSubring w ⊤) ∧
      (∀ g : Ω, (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 →
        ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r) → g ∈ Ac) ∧
      (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → ϖ ∈ 𝔮 → ∀ g : Ω, w g ≤ 1 →
        ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r) ∧
      (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → ϖ ∉ 𝔮 →
        ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * f = r) := by
  have hdvr := isDiscreteValuationRing_valuationSubring w hϖ0 hϖw hdisc
  refine ⟨w.valuationSubring.toSubring, topUniformizer w hϖw, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact (mem_liftValuationSubring ((w.mem_valuationSubring_iff a).1 ha)).2
      (ValuationSubring.mem_top _)
  · intro g hg
    have hht : (maximalIdeal w.valuationSubring.toSubring).height = 1 := by
      have h := maximalIdeal_height_eq_ringKrullDim (R := w.valuationSubring.toSubring)
      rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h
      exact_mod_cast h
    obtain ⟨r, s, hs, hsr⟩ := hg _ (maximalIdeal.isMaximal _).isPrime hht
    have hsu : IsUnit s := by
      by_contra h
      exact hs ((mem_maximalIdeal _).2 h)
    obtain ⟨U, rfl⟩ := hsu
    have hg' : g = ((↑U⁻¹ * r : w.valuationSubring.toSubring) : Ω) := by
      have h1 : ((↑U⁻¹ : w.valuationSubring.toSubring) : Ω) * ((U : _) : Ω) = 1 := by
        rw [← MulMemClass.coe_mul, Units.inv_mul, OneMemClass.coe_one]
      rw [MulMemClass.coe_mul, ← hsr, ← mul_assoc, h1, one_mul]
    rw [hg']
    exact Subtype.property _
  · intro 𝔮 hq _ _ g hg
    refine ⟨⟨g, (w.mem_valuationSubring_iff g).2 hg⟩, 1,
      fun h => hq.ne_top ((Ideal.eq_top_iff_one _).mpr h), ?_⟩
    rw [OneMemClass.coe_one, one_mul]
  · intro 𝔮 hq h1 hϖq
    exfalso
    have hne : 𝔮 ≠ ⊥ := by
      intro h
      rw [h, Ideal.height_bot] at h1
      exact zero_ne_one h1
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨n, U, hU⟩ := exists_associated_pow w hϖ0 hϖw hdisc x hx0
    have hpn : topUniformizer w hϖw ^ n ∈ 𝔮 := by
      have : topUniformizer w hϖw ^ n = x * ↑U⁻¹ := by
        rw [← hU, mul_assoc, Units.mul_inv, mul_one]
      rw [this]
      exact Ideal.mul_mem_right _ _ hx
    exact hϖq (hq.mem_of_pow_mem n hpn)

end Top

section CurveDVR

open Polynomial

variable {k B κ : Type*} [Field k] [CommRing B] [Algebra k B] [Field κ] [Algebra k κ]
variable (π : B →ₐ[k] κ) (b : Module.Basis (Fin 1) B Ω[B⁄k])

/-- The `κ`-valued derivation at the point `π`: `a ↦ π (coordinate of da)`. -/
def ptDer (a : B) : κ :=
  π (b.repr (KaehlerDifferential.D k B a) 0)

theorem ptDer_add (x y : B) : ptDer π b (x + y) = ptDer π b x + ptDer π b y := by
  simp [ptDer]

theorem ptDer_sub (x y : B) : ptDer π b (x - y) = ptDer π b x - ptDer π b y := by
  simp [ptDer]

theorem ptDer_mul (x y : B) :
    ptDer π b (x * y) = π x * ptDer π b y + π y * ptDer π b x := by
  simp [ptDer, Derivation.leibniz]

theorem ptDer_algebraMap (r : k) : ptDer π b (algebraMap k B r) = 0 := by
  simp [ptDer]

theorem ptDer_zero : ptDer π b 0 = 0 := by
  simp [ptDer]

theorem ptDer_one : ptDer π b 1 = 0 := by
  simp [ptDer]

/-- If `π t = 0` and `D t = 1`, then `s * t ^ n ≠ 0` whenever `π s ≠ 0` (formal smoothness
lifts `a ↦ π a + (Da) X` to `κ[X]/(X^(n+1))`). -/
theorem ptDer_mul_pow_ne_zero [Algebra.FormallySmooth k B] {t : B} (ht : π t = 0)
    (hDt : ptDer π b t = 1) {s : B} (hs : π s ≠ 0) (n : ℕ) : s * t ^ n ≠ 0 := by
  intro h0
  let Q := κ[X] ⧸ Ideal.span {(X : κ[X]) ^ (n + 1)}
  let x : Q := Ideal.Quotient.mk _ X
  have hx : x ^ (n + 1) = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  let J : Ideal Q := Ideal.span {x ^ 2}
  have hJ : IsNilpotent J := by
    refine ⟨n + 1, ?_⟩
    rw [Ideal.zero_eq_bot, Ideal.span_singleton_pow, ← pow_mul, mul_comm, pow_mul, hx,
      zero_pow two_ne_zero, Ideal.span_singleton_eq_bot]
  let δ : B → Q := fun a => algebraMap κ Q (π a) + algebraMap κ Q (ptDer π b a) * x
  have hδmul : ∀ a c, δ (a * c) - δ a * δ c ∈ J := by
    intro a c
    refine Ideal.mem_span_singleton'.2
      ⟨-(algebraMap κ Q (ptDer π b a) * algebraMap κ Q (ptDer π b c)), ?_⟩
    simp only [δ, ptDer_mul, map_mul, map_add]
    ring
  let g : B →ₐ[k] Q ⧸ J :=
    { toFun := fun a => Ideal.Quotient.mk J (δ a)
      map_one' := by simp [δ, ptDer_one]
      map_mul' := fun a c => by
        rw [← (Ideal.Quotient.mk J).map_mul]
        exact Ideal.Quotient.eq.2 (hδmul a c)
      map_zero' := by simp [δ, ptDer_zero]
      map_add' := fun a c => by
        rw [← (Ideal.Quotient.mk J).map_add]
        congr 1
        simp only [δ, map_add, ptDer_add]
        ring
      commutes' := fun r => by
        simp only [δ, ptDer_algebraMap, map_zero, zero_mul, add_zero, AlgHom.commutes]
        rw [← IsScalarTower.algebraMap_apply]
        rfl }
  let ψ := Algebra.FormallySmooth.lift J hJ g
  have key : ∀ a, ψ a - δ a ∈ J := fun a =>
    Ideal.Quotient.eq.1 (Algebra.FormallySmooth.mk_lift J hJ g a)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (key t)
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.1 (key s)
  simp only [δ, ht, hDt, map_zero, map_one] at hc
  have htt : ψ t = x * (1 + c * x) := by linear_combination -hc
  have hss : ψ s = algebraMap κ Q (π s) + x * (algebraMap κ Q (ptDer π b s) + c' * x) := by
    linear_combination -hc'
  have hψ : ψ (s * t ^ n) = 0 := by rw [h0, map_zero]
  rw [map_mul, map_pow, htt, hss, mul_pow] at hψ
  obtain ⟨e, he⟩ := sub_dvd_pow_sub_pow (1 + c * x) 1 n
  set r := algebraMap κ Q (π s)
  set d := algebraMap κ Q (ptDer π b s) + c' * x
  have hrx : r * x ^ n = 0 := by
    linear_combination hψ - r * x ^ n * he - (r * c * e + d * (1 + c * x) ^ n) * hx
  have hmk : Ideal.Quotient.mk (Ideal.span {(X : κ[X]) ^ (n + 1)}) (C (π s) * X ^ n) = 0 := by
    rw [map_mul, map_pow]
    exact hrx
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmk
  obtain ⟨q, hq⟩ := hmk
  have hcoeff := congrArg (fun p : κ[X] => p.coeff n) hq
  simp [coeff_X_pow_mul'] at hcoeff
  exact hs hcoeff

/-- There is `t ∈ ker π` with `D t = 1`, when `κ` is formally unramified over `k`. -/
theorem ptDer_exists_param [Algebra.FormallyUnramified k κ] (hπ : Function.Surjective π) :
    ∃ t : B, π t = 0 ∧ ptDer π b t = 1 := by
  let _ : Algebra B κ := π.toRingHom.toAlgebra
  have : IsScalarTower k B κ := IsScalarTower.of_algebraMap_eq fun r => (π.commutes r).symm
  have hsurj : Function.Surjective (algebraMap B κ) := hπ
  have hex := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k B κ hsurj
  obtain ⟨y, hy⟩ := (hex (1 ⊗ₜ b 0)).1 (Subsingleton.elim _ _)
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ y
  refine ⟨x, hx, ?_⟩
  rw [KaehlerDifferential.kerCotangentToTensor_toCotangent] at hy
  have := congrArg (fun z => (Algebra.TensorProduct.basis κ b).repr z 0) hy
  simp [Algebra.TensorProduct.basis_repr_tmul] at this
  exact this

/-- Formal smoothness of `B` and `κ`: an element of `ker π` with `D x = 0` lies in `(ker π)²`. -/
theorem ptDer_mem_sq [Algebra.FormallySmooth k B] [Algebra.FormallySmooth k κ]
    (hπ : Function.Surjective π) {x : B} (hx : π x = 0) (hD : ptDer π b x = 0) :
    x ∈ RingHom.ker π ^ 2 := by
  let _ : Algebra B κ := π.toRingHom.toAlgebra
  have : IsScalarTower k B κ := IsScalarTower.of_algebraMap_eq fun r => (π.commutes r).symm
  have hsurj : Function.Surjective (algebraMap B κ) := hπ
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := k) (A := κ)
    (P := B) hsurj).2 inferInstance
  have hx' : x ∈ RingHom.ker (algebraMap B κ) := hx
  have h0 : KaehlerDifferential.kerCotangentToTensor k B κ
      ((RingHom.ker (algebraMap B κ)).toCotangent ⟨x, hx'⟩) = 0 := by
    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]
    apply (Algebra.TensorProduct.basis κ b).repr.injective
    refine Finsupp.ext fun i => ?_
    fin_cases i
    simp [Algebra.TensorProduct.basis_repr_tmul]
    exact hD
  rw [← map_zero (KaehlerDifferential.kerCotangentToTensor k B κ)] at h0
  exact (Ideal.toCotangent_eq_zero _ _).1 (hinj h0)

/-- `ker π = (t) + (ker π)²`. -/
theorem ptDer_ker_le [Algebra.FormallySmooth k B] [Algebra.FormallySmooth k κ]
    (hπ : Function.Surjective π) {t : B} (ht : π t = 0) (hDt : ptDer π b t = 1) :
    RingHom.ker π ≤ Ideal.span {t} ⊔ RingHom.ker π ^ 2 := by
  intro x hx
  have hx' : π x = 0 := RingHom.mem_ker.1 hx
  obtain ⟨c, hc⟩ := hπ (ptDer π b x)
  have h : x - c * t ∈ RingHom.ker π ^ 2 := by
    refine ptDer_mem_sq π b hπ ?_ ?_
    · rw [map_sub, map_mul, hx', ht, mul_zero, sub_zero]
    · rw [ptDer_sub, ptDer_mul, hDt, ht, hc]
      ring
  have : x = c * t + (x - c * t) := by ring
  rw [this]
  exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self t)) h

include b in
/-- **Local rings of a smooth curve over a field.** Let `B` be a formally smooth Noetherian
`k`-algebra with `Ω[B⁄k]` free of rank one, and `π : B → κ` a surjection onto a field which is
formally étale over `k` (for instance finite separable). Then the localization of `B` at
`𝔭 = ker π` is a discrete valuation ring. -/
theorem isDiscreteValuationRing_of_formallySmooth [Algebra.FormallySmooth k B]
    [IsNoetherianRing B] [Algebra.FormallySmooth k κ] [Algebra.FormallyUnramified k κ]
    (hπ : Function.Surjective π) (𝔭 : Ideal B) [𝔭.IsPrime] (h𝔭 : RingHom.ker π = 𝔭)
    (A : Type*) [CommRing A] [Algebra B A] [IsLocalization.AtPrime A 𝔭] :
    ∃ _ : IsDomain A, IsDiscreteValuationRing A := by
  subst h𝔭
  have := IsLocalization.AtPrime.isLocalRing A (RingHom.ker π)
  have : IsNoetherianRing A := IsLocalization.isNoetherianRing (RingHom.ker π).primeCompl A
    inferInstance
  obtain ⟨t, ht, hDt⟩ := ptDer_exists_param π b hπ
  set ι := algebraMap B A
  have hmax : maximalIdeal A = Ideal.span {ι t} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker π) A]
    apply le_antisymm
    · have hle := Ideal.map_mono (f := ι) (ptDer_ker_le π b hπ ht hDt)
      rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_pow] at hle
      have hm : (RingHom.ker π).map ι ≤ maximalIdeal A :=
        (IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker π) A).le
      refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
        (I := maximalIdeal A) ?_ (hle.trans (sup_le_sup_left ?_ _))
      · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      · rw [sq, Ideal.smul_eq_mul]
        exact Ideal.mul_mono_left hm
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ (RingHom.mem_ker.2 ht)
  have hnil : ¬ IsNilpotent (ι t) := by
    rintro ⟨n, hn⟩
    rw [← map_pow, IsLocalization.map_eq_zero_iff (RingHom.ker π).primeCompl] at hn
    obtain ⟨⟨m, hm⟩, hm0⟩ := hn
    have hm' : π m ≠ 0 := fun h => (Ideal.mem_primeCompl_iff.1 hm) (RingHom.mem_ker.2 h)
    exact ptDer_mul_pow_ne_zero π b ht hDt hm' n hm0
  have hdom := IdentityPointDepth.isDomain_of_maximalIdeal_eq_span hmax hnil
  refine ⟨hdom, IdentityPointDepth.isDiscreteValuationRing_of_maximalIdeal_eq_span hmax ?_⟩
  rintro h
  exact hnil (h ▸ IsNilpotent.zero)

omit π b in
/-- **Smooth curves over a perfect field.** If `B` is standard smooth of relative dimension one
over a perfect field `k` (for instance a finite field), its localization at every maximal ideal
(the local ring at a closed point) is a discrete valuation ring. -/
theorem isDiscreteValuationRing_of_standardSmooth [PerfectField k]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k B] (𝔭 : Ideal B) [𝔭.IsMaximal]
    (A : Type*) [CommRing A] [Algebra B A] [IsLocalization.AtPrime A 𝔭] :
    ∃ _ : IsDomain A, IsDiscreteValuationRing A := by
  have : Algebra.IsStandardSmooth k B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  have : Nontrivial B := (Ideal.Quotient.mk 𝔭).domain_nontrivial
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hΩ := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k)
    (S := B) 1
  have : Module.Finite B Ω[B⁄k] := Module.rank_lt_aleph0_iff.1 (by
    rw [hΩ]
    exact Cardinal.one_lt_aleph0)
  let b : Module.Basis (Fin 1) B Ω[B⁄k] :=
    Module.finBasisOfFinrankEq B Ω[B⁄k] (Module.finrank_eq_of_rank_eq (by simpa using hΩ))
  let _ : Field (B ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have : Algebra.FiniteType k (B ⧸ 𝔭) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k 𝔭) (Ideal.Quotient.mkₐ_surjective k 𝔭)
  have : Module.Finite k (B ⧸ 𝔭) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ 𝔭)
  have : Algebra.IsSeparable k (B ⧸ 𝔭) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Algebra.FormallyEtale k (B ⧸ 𝔭) := Algebra.FormallyEtale.of_isSeparable k (B ⧸ 𝔭)
  exact isDiscreteValuationRing_of_formallySmooth (Ideal.Quotient.mkₐ k 𝔭) b
    (Ideal.Quotient.mkₐ_surjective k 𝔭) 𝔭 (Ideal.Quotient.mkₐ_ker k 𝔭) A

end CurveDVR

section Assembly

variable {Ω : Type*} [Field Ω] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {w : Valuation Ω Γ₀}

/-- **`hcentre`.** Let `w` be discrete with uniformizer `ϖ_w`. Suppose every constant place
`O ≠ ē, ⊤` of `κ_w` has a centre: a local Noetherian subring `A_c` of `Ω` with fraction field `Ω`
and an element `ϖ` of its maximal ideal, a nonzerodivisor with `A_c / ϖ` a discrete valuation
ring, such that `A_c ⊆ Õ`, `w ϖ < 1`, `w` is not centred at the closed point, and `f` is regular
at the height-one primes of `A_c` off `ϖ`. Then the hypothesis `hcentre` of
`SpecialFibreFunctionField.reduce_mem_polePart` holds. -/
theorem hcentre_of_centres {k : Type*} [Field k] [Algebra k (ResidueField w.valuationSubring)]
    (ē : ValuationSubring (ResidueField w.valuationSubring)) {ϖw : Ω} (hϖ0 : ϖw ≠ 0)
    (hϖw : w ϖw < 1) (hdisc : ∀ x : Ω, x ≠ 0 → ∃ m : ℤ, w x = w ϖw ^ m) {f : Ω}
    (hc : ∀ O : ValuationSubring (ResidueField w.valuationSubring), IsConstPlace k O →
      O ≠ ē → O ≠ ⊤ → ∃ (Ac : Subring Ω) (_ : IsLocalRing Ac) (_ : IsNoetherianRing Ac)
        (_ : IsFractionRing Ac Ω) (ϖ : Ac) (_ : IsDomain (Ac ⧸ Ideal.span {ϖ})),
        IsDiscreteValuationRing (Ac ⧸ Ideal.span {ϖ}) ∧ ϖ ∈ nonZeroDivisors Ac ∧
        ϖ ∈ maximalIdeal Ac ∧ w ϖ < 1 ∧ (∃ c ∈ maximalIdeal Ac, w c = 1) ∧
        (∀ a ∈ Ac, a ∈ liftValuationSubring w O) ∧
        (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → ϖ ∉ 𝔮 →
          ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * f = r)) :
    ∀ O : ValuationSubring (ResidueField w.valuationSubring), IsConstPlace k O →
      O ≠ ē → ∃ (Ac : Subring Ω) (ϖ : Ac), (∀ a ∈ Ac, a ∈ liftValuationSubring w O) ∧
        (∀ g : Ω, (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 →
          ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r) → g ∈ Ac) ∧
        (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → ϖ ∈ 𝔮 → ∀ g : Ω, w g ≤ 1 →
          ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r) ∧
        (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → ϖ ∉ 𝔮 →
          ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * f = r) := by
  intro O hO hne
  by_cases htop : O = ⊤
  · subst htop
    exact centre_spec_top w hϖ0 hϖw hdisc f
  obtain ⟨Ac, _, _, _, ϖ, _, _, hϖ, hm, hϖw', hcen, hdom, hhor⟩ := hc O hO hne htop
  exact ⟨Ac, ϖ, centre_spec w hϖ hm O hdom hϖw' hcen hhor⟩

end Assembly

end Centre

end ZInQ.Contrib.CMHeight62Full
