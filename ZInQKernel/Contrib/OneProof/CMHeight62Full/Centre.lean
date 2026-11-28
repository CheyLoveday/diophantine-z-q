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

**Local algebra.** Let `A` be a local Noetherian ring with fraction field `Ω`, and `ϖ` a
nonzerodivisor in its maximal ideal with `A / ϖ` a discrete valuation ring.

* `centre_val_eq_one`: if `w ≤ 1` on `A`, `w ϖ < 1` and `w` is not centred at the closed point
  (some `c ∈ 𝔪` has `w c = 1`), then `w = 1` off `(ϖ)`.
* `centre_vertical`: under the same hypotheses, every `g` with `w g ≤ 1` lies in `A_𝔮` for the
  height-one primes `𝔮 ∋ ϖ` (they all equal `(ϖ)`).
* `centre_spec`: the four clauses of `hcentre` for one place, for the image `A_c` of `A` in `Ω`
  (`rangeEquiv`, `forall_height_one_of_range`, `forall_height_one_range_of` transport primes
  and heights to the image).

**The trivial place.** `O = ⊤` is a constant place, and its centre is `𝒪_w` itself:
`isDiscreteValuationRing_valuationSubring` (a discrete `w` has a DVR as valuation ring) and
`centre_spec_top`.

**Smooth curves over a field.** `isDiscreteValuationRing_of_formallySmooth`: for `B` formally
smooth and Noetherian over a field `k` with `Ω[B⁄k]` free of rank one, and a surjection `π` of
`B` onto a field formally étale over `k`, the localization at `ker π` is a discrete valuation
ring. The derivation `ptDer` along `π` plays the role of the section derivation of
`LocalStructure.lean`: formal smoothness of `κ` makes `ker π = (t) + (ker π)²`, and lifting
`a ↦ π a + (Da) X` to `κ[X]/(X^(n+1))` shows `t` is not nilpotent.
`isDiscreteValuationRing_of_standardSmooth`: hence the local rings at closed points of a smooth
curve over a perfect field are discrete valuation rings.

**Schemes.**
* `centre_unique`: centres are unique for a separated morphism.
* `stalk_hom_eq_of_spec`, `exists_centre_germ`: the local map at a centre is the generic germ.
* `exists_val_eq_one_of_centre`: `w` is centred at a single point, so at any other point some
  element of the maximal ideal has value one.

**Horizontal primes.** `localizationValuationSubring`: `A_𝔮 ⊆ Ω` as a discrete valuation
subring; `exists_of_forall_valuationSubring` turns "f lies in every such subring other than
`A_g`" into regularity at `𝔮`.

**Assembly.**
* `hcentre_of_centres`: `hcentre` from centres at the nontrivial constant places.
* `hcentre_of_model`: `hcentre` from a proper integral locally Noetherian model, the point `η`
  at which `w` is centred, and the local facts at the centres (the depth-two hypotheses, `w ϖ < 1`
  and regularity of `f` at the horizontal primes).

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
variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra A Ω] {ϖ : A}
  (hϖ : ϖ ∈ nonZeroDivisors A) (hm : ϖ ∈ maximalIdeal A)
  [IsDomain (A ⧸ Ideal.span {ϖ})] [IsDiscreteValuationRing (A ⧸ Ideal.span {ϖ})]

include hϖ hm

omit [IsNoetherianRing A] hϖ in
/-- If `w ≤ 1` on `A`, `w ϖ < 1`, and some element of the maximal ideal has value one, then
`w = 1` off `(ϖ)`. -/
theorem centre_val_eq_one (hAw : ∀ a : A, w (algebraMap A Ω a) ≤ 1)
    (hϖw : w (algebraMap A Ω ϖ) < 1) (hcen : ∃ c ∈ maximalIdeal A, w (algebraMap A Ω c) = 1)
    {b : A} (hb : b ∉ Ideal.span {ϖ}) : w (algebraMap A Ω b) = 1 := by
  obtain ⟨c, hc, hc1⟩ := hcen
  by_contra hne
  have hlt : w (algebraMap A Ω b) < 1 := lt_of_le_of_ne (hAw b) hne
  have hb0 : Ideal.Quotient.mk (Ideal.span {ϖ}) b ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hcm : Ideal.Quotient.mk (Ideal.span {ϖ}) c ∈ maximalIdeal (A ⧸ Ideal.span {ϖ}) := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : A ⧸ Ideal.span {ϖ})
    have h1 : Ideal.Quotient.mk (Ideal.span {ϖ}) (c * d - 1) = 0 := by
      rw [map_sub, map_mul, hd, ← hu, map_one, Units.mul_inv, sub_self]
    rw [Ideal.Quotient.eq_zero_iff_mem] at h1
    have h2 : c * d - 1 ∈ maximalIdeal A :=
      (Ideal.span_singleton_le_iff_mem _).mpr hm h1
    have h3 : c * d ∈ maximalIdeal A := Ideal.mul_mem_right d _ hc
    have h4 : (1 : A) ∈ maximalIdeal A := by
      have := Ideal.sub_mem _ h3 h2
      rwa [sub_sub_cancel] at this
    exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h4)
  obtain ⟨N, d, hd⟩ := dvd_pow_of_mem_maximalIdeal hb0 hcm
  obtain ⟨d', rfl⟩ := Ideal.Quotient.mk_surjective d
  have hmem : c ^ N - b * d' ∈ Ideal.span {ϖ} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_mul, hd, sub_self]
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hmem
  have hcN : w (algebraMap A Ω c ^ N) = 1 := by rw [map_pow, hc1, one_pow]
  have heq : algebraMap A Ω c ^ N =
      algebraMap A Ω b * algebraMap A Ω d' + algebraMap A Ω e * algebraMap A Ω ϖ := by
    have := congrArg (algebraMap A Ω) he
    simp only [map_mul, map_sub, map_pow] at this
    linear_combination -this
  have h1 : w (algebraMap A Ω b * algebraMap A Ω d') < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hAw d')) hlt
  have h2 : w (algebraMap A Ω e * algebraMap A Ω ϖ) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hAw e)) hϖw
  have h3 := Valuation.map_add_lt w h1 h2
  rw [← heq, hcN] at h3
  exact lt_irrefl _ h3

/-- **Vertical primes.** Every height-one prime through `ϖ` is `(ϖ)`, and every `g` with
`w g ≤ 1` is a fraction with denominator outside `(ϖ)`. -/
theorem centre_vertical [IsFractionRing A Ω] (hAw : ∀ a : A, w (algebraMap A Ω a) ≤ 1)
    (hϖw : w (algebraMap A Ω ϖ) < 1) (hcen : ∃ c ∈ maximalIdeal A, w (algebraMap A Ω c) = 1)
    (𝔮 : Ideal A) (hq : 𝔮.IsPrime) (h1 : 𝔮.height = 1) (hϖq : ϖ ∈ 𝔮) (g : Ω) (hg : w g ≤ 1) :
    ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * g = algebraMap A Ω r := by
  have h𝔮 := depthTwo_height_one_cases hϖ hm 𝔮 h1 hϖq
  subst h𝔮
  have hP := depthTwo_isPrime hϖ hm
  have := depthTwo_isDomain hϖ hm
  have hϖ0 : algebraMap A Ω ϖ ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hϖ
  by_cases hg0 : g = 0
  · refine ⟨0, 1, fun h => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h), ?_⟩
    rw [hg0, mul_zero, map_zero]
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := A) g
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbΩ : algebraMap A Ω b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hg0
    rw [← hab, map_zero, zero_div]
  obtain ⟨n, a', ha', rfl⟩ := depthTwo_exists_pow_mul hϖ hm ha0
  obtain ⟨k, b', hb', rfl⟩ := depthTwo_exists_pow_mul hϖ hm hb0
  have hgb : g * algebraMap A Ω (ϖ ^ k * b') = algebraMap A Ω (ϖ ^ n * a') := by
    rw [← hab]
    exact div_mul_cancel₀ _ hbΩ
  simp only [map_mul, map_pow] at hgb
  have hwa : w (algebraMap A Ω a') = 1 := centre_val_eq_one w hm hAw hϖw hcen ha'
  rcases le_or_gt k n with hkn | hnk
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
    refine ⟨ϖ ^ j * a', b', hb', ?_⟩
    have hk0 : algebraMap A Ω ϖ ^ k ≠ 0 := pow_ne_zero _ hϖ0
    apply mul_left_cancel₀ hk0
    rw [map_mul, map_pow]
    rw [pow_add] at hgb
    linear_combination hgb
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hnk
    exfalso
    have hn0 : algebraMap A Ω ϖ ^ n ≠ 0 := pow_ne_zero _ hϖ0
    have hrel : g * algebraMap A Ω ϖ ^ (j + 1) * algebraMap A Ω b' = algebraMap A Ω a' := by
      apply mul_left_cancel₀ hn0
      rw [pow_add] at hgb
      linear_combination hgb
    have hlt : w (g * algebraMap A Ω ϖ ^ (j + 1) * algebraMap A Ω b') < 1 := by
      rw [map_mul, map_mul, map_pow]
      refine lt_of_le_of_lt (mul_le_of_le_one_right' (hAw b')) ?_
      refine lt_of_le_of_lt (mul_le_of_le_one_left' hg) ?_
      exact pow_lt_one₀ zero_le hϖw (Nat.succ_ne_zero j)
    rw [hrel, hwa] at hlt
    exact lt_irrefl _ hlt

end Local

section Transport

variable {Ω : Type*} [Field Ω] {A : Type*} [CommRing A] [Algebra A Ω]
  (hinj : Function.Injective (algebraMap A Ω))

/-- `A` is isomorphic to its image in `Ω`. -/
def rangeEquiv : A ≃+* (algebraMap A Ω).range :=
  RingEquiv.ofBijective (algebraMap A Ω).rangeRestrict
    ⟨fun _ _ h => hinj (congrArg Subtype.val h), (algebraMap A Ω).rangeRestrict_surjective⟩

theorem coe_rangeEquiv (a : A) : ((rangeEquiv hinj a : (algebraMap A Ω).range) : Ω) =
    algebraMap A Ω a :=
  rfl

theorem algebraMap_rangeEquiv_symm (s : (algebraMap A Ω).range) :
    algebraMap A Ω ((rangeEquiv hinj).symm s) = s := by
  rw [← coe_rangeEquiv hinj, RingEquiv.apply_symm_apply]

include hinj in
/-- Height-one conditions on the image transfer to `A`. -/
theorem forall_height_one_of_range {g : Ω}
    (h : ∀ 𝔮 : Ideal (algebraMap A Ω).range, 𝔮.IsPrime → 𝔮.height = 1 →
      ∃ r s : (algebraMap A Ω).range, s ∉ 𝔮 ∧ (s : Ω) * g = r) :
    ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 →
      ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * g = algebraMap A Ω r := by
  intro 𝔮 hq h1
  set e := rangeEquiv hinj
  have hP : (𝔮.comap e.symm).IsPrime := Ideal.comap_isPrime _ _
  have hh : (𝔮.comap e.symm).height = 1 := by
    rw [Ideal.comap_symm, RingEquiv.height_map, h1]
  obtain ⟨r, s, hs, hrs⟩ := h _ hP hh
  refine ⟨e.symm r, e.symm s, hs, ?_⟩
  rw [algebraMap_rangeEquiv_symm, algebraMap_rangeEquiv_symm, hrs]

/-- Height-one conditions on `A` transfer to the image. -/
theorem forall_height_one_range_of (Φ : Ideal A → Prop) {g : Ω}
    (h : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → Φ 𝔮 →
      ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * g = algebraMap A Ω r) :
    ∀ 𝔮 : Ideal (algebraMap A Ω).range, 𝔮.IsPrime → 𝔮.height = 1 →
      Φ (𝔮.comap (rangeEquiv hinj)) →
      ∃ r s : (algebraMap A Ω).range, s ∉ 𝔮 ∧ (s : Ω) * g = r := by
  intro 𝔮 hq h1 hΦ
  set e := rangeEquiv hinj
  have hP : (𝔮.comap e).IsPrime := Ideal.comap_isPrime _ _
  have hh : (𝔮.comap e).height = 1 := by
    rw [← Ideal.map_symm, RingEquiv.height_map, h1]
  obtain ⟨r, s, hs, hrs⟩ := h _ hP hh hΦ
  exact ⟨e r, e s, hs, hrs⟩

end Transport

section Spec

variable {Ω : Type*} [Field Ω] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (w : Valuation Ω Γ₀)
variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra A Ω]
  [IsFractionRing A Ω] {ϖ : A} (hϖ : ϖ ∈ nonZeroDivisors A) (hm : ϖ ∈ maximalIdeal A)
  [IsDomain (A ⧸ Ideal.span {ϖ})] [IsDiscreteValuationRing (A ⧸ Ideal.span {ϖ})]

include hϖ hm

/-- **The four clauses of `hcentre` at one place**, for the image `A_c` of a local ring `A` with
fraction field `Ω` and `ϖ` as in the depth-two lemmas, dominated by `Õ`, with `w ϖ < 1`, `w` not
centred at the closed point, and `f` regular at the height-one primes off `ϖ`. -/
theorem centre_spec (O : ValuationSubring (ResidueField w.valuationSubring))
    (hdom : ∀ a : A, algebraMap A Ω a ∈ liftValuationSubring w O)
    (hϖw : w (algebraMap A Ω ϖ) < 1) (hcen : ∃ c ∈ maximalIdeal A, w (algebraMap A Ω c) = 1)
    {f : Ω} (hhor : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → ϖ ∉ 𝔮 →
      ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * f = algebraMap A Ω r) :
    ∃ (Ac : Subring Ω) (ϖ' : Ac), (∀ a ∈ Ac, a ∈ liftValuationSubring w O) ∧
      (∀ g : Ω, (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 →
        ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r) → g ∈ Ac) ∧
      (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → ϖ' ∈ 𝔮 → ∀ g : Ω, w g ≤ 1 →
        ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * g = r) ∧
      (∀ 𝔮 : Ideal Ac, 𝔮.IsPrime → 𝔮.height = 1 → ϖ' ∉ 𝔮 →
        ∃ r s : Ac, s ∉ 𝔮 ∧ (s : Ω) * f = r) := by
  have hinj := IsFractionRing.injective A Ω
  have hAw : ∀ a : A, w (algebraMap A Ω a) ≤ 1 := fun a =>
    (w.mem_valuationSubring_iff _).mp (liftValuationSubring_le O (hdom a))
  refine ⟨(algebraMap A Ω).range, rangeEquiv hinj ϖ, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact hdom a
  · intro g hg
    obtain ⟨a, ha⟩ := depthTwo_mem_range hϖ hm g (forall_height_one_of_range hinj hg)
    exact ⟨a, ha⟩
  · intro 𝔮 hq h1 hϖq g hg
    exact forall_height_one_range_of hinj (fun 𝔮' => ϖ ∈ 𝔮')
      (fun 𝔮' hq' h1' hϖ' => centre_vertical w hϖ hm hAw hϖw hcen 𝔮' hq' h1' hϖ' g hg)
      𝔮 hq h1 hϖq
  · intro 𝔮 hq h1 hϖq
    exact forall_height_one_range_of hinj (fun 𝔮' => ϖ ∉ 𝔮') hhor 𝔮 hq h1 hϖq

end Spec

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

section Uniqueness

open AlgebraicGeometry CategoryTheory

universe u

/-- **Uniqueness of centres (separatedness).** Let `g : X → Y` be separated and `R` a valuation
ring with fraction field `K`. If two points `c₁, c₂` of `X` carry local homomorphisms
`𝒪_{X,cᵢ} → R` inducing the same `Spec K → X` and the same `Spec R → Y`, then `c₁ = c₂`. -/
theorem centre_unique {X Y : Scheme.{u}} (g : X ⟶ Y) [IsSeparated g] {R K : Type u}
    [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {c₁ c₂ : X} (φ₁ : X.presheaf.stalk c₁ ⟶ CommRingCat.of R)
    (φ₂ : X.presheaf.stalk c₂ ⟶ CommRingCat.of R) [IsLocalHom φ₁.hom] [IsLocalHom φ₂.hom]
    (h₁ : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ Spec.map φ₁ ≫ X.fromSpecStalk c₁ =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ Spec.map φ₂ ≫ X.fromSpecStalk c₂)
    (h₂ : Spec.map φ₁ ≫ X.fromSpecStalk c₁ ≫ g = Spec.map φ₂ ≫ X.fromSpecStalk c₂ ≫ g) :
    c₁ = c₂ := by
  let l₁ := Spec.map φ₁ ≫ X.fromSpecStalk c₁
  let l₂ := Spec.map φ₂ ≫ X.fromSpecStalk c₂
  let S : ValuativeCommSq g := ⟨R, K, Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l₁,
    l₁ ≫ g, ⟨by simp only [Category.assoc]⟩⟩
  have hsub := IsSeparated.valuativeCriterion g S
  let L₁ : S.commSq.LiftStruct := ⟨l₁, rfl, rfl⟩
  let L₂ : S.commSq.LiftStruct := ⟨l₂, h₁.symm, by
    change (Spec.map φ₂ ≫ X.fromSpecStalk c₂) ≫ g = (Spec.map φ₁ ≫ X.fromSpecStalk c₁) ≫ g
    simp only [Category.assoc]
    exact h₂.symm⟩
  have hl : l₁ = l₂ := congrArg CommSq.LiftStruct.l (Subsingleton.elim L₁ L₂)
  have e₁ : l₁ (IsLocalRing.closedPoint (CommRingCat.of R)) = c₁ := by
    change (X.fromSpecStalk c₁) ((Spec.map φ₁) (IsLocalRing.closedPoint (CommRingCat.of R))) = _
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have e₂ : l₂ (IsLocalRing.closedPoint (CommRingCat.of R)) = c₂ := by
    change (X.fromSpecStalk c₂) ((Spec.map φ₂) (IsLocalRing.closedPoint (CommRingCat.of R))) = _
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  rw [← e₁, ← e₂, hl]

/-- **The stalk map at a centre is the generic germ.** If `ψ : 𝒪_{X,c} → Ω` induces the same
`Spec Ω → X` as `τ : K(X) → Ω` at the generic point, then `ψ` is the specialization map
`𝒪_{X,c} → K(X)` followed by `τ`. -/
theorem stalk_hom_eq_of_spec {X : Scheme.{u}} [IrreducibleSpace X] (c : X) {Ω : CommRingCat.{u}}
    (ψ : X.presheaf.stalk c ⟶ Ω) (τ : X.functionField ⟶ Ω)
    (h : Spec.map ψ ≫ X.fromSpecStalk c = Spec.map τ ≫ X.fromSpecStalk (genericPoint X)) :
    ψ = X.presheaf.stalkSpecializes (genericPoint_specializes c) ≫ τ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk c), h, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

/-- **Centres from properness, ring form.** Let `g : X → Y` be proper with `X` irreducible,
`τ : K(X) → Ω` a map to a field, `V` a valuation ring of `Ω`, and `Spec V → Y` extending the
generic point. Then there is a point `c` and a local homomorphism `φ : 𝒪_{X,c} → V` such that
`τ` of the generic germ of every `b ∈ 𝒪_{X,c}` is `φ b ∈ V`. -/
theorem exists_centre_germ {X Y : Scheme.{u}} [IrreducibleSpace X] (g : X ⟶ Y) [IsProper g]
    {Ω : Type u} [Field Ω] (τ : X.functionField ⟶ CommRingCat.of Ω) (V : ValuationSubring Ω)
    (i₂ : Spec (CommRingCat.of V) ⟶ Y)
    (hsq : (Spec.map τ ≫ X.fromSpecStalk (genericPoint X)) ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ i₂) :
    ∃ (c : X) (φ : X.presheaf.stalk c ⟶ CommRingCat.of V), IsLocalHom φ.hom ∧
      Spec.map φ ≫ X.fromSpecStalk c ≫ g = i₂ ∧
      ∀ b, τ.hom ((X.presheaf.stalkSpecializes (genericPoint_specializes c)).hom b) =
        algebraMap V Ω (φ.hom b) := by
  obtain ⟨c, φ, hφ, h₂, h₁⟩ := exists_centre g (Spec.map τ ≫ X.fromSpecStalk (genericPoint X))
    i₂ hsq
  refine ⟨c, φ, hφ, h₂, fun b => ?_⟩
  have key := stalk_hom_eq_of_spec c (φ ≫ CommRingCat.ofHom (algebraMap V Ω)) τ (by
    rw [Spec.map_comp, Category.assoc]
    exact h₁)
  have := congrArg (fun f => f.hom b) key
  exact this.symm

/-- Two morphisms `Spec V → Spec T` that agree on `Spec Ω`, for an injective `V → Ω`, agree. -/
theorem spec_ext_of_injective {V Ω T : CommRingCat.{u}} (a : V ⟶ Ω)
    (ha : Function.Injective a.hom) (l₁ l₂ : Spec V ⟶ Spec T)
    (h : Spec.map a ≫ l₁ = Spec.map a ≫ l₂) : l₁ = l₂ := by
  rw [← Spec.map_preimage l₁, ← Spec.map_preimage l₂] at h ⊢
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext x
  apply ha
  have := congrArg (fun f => f.hom x) h'
  simpa using this

/-- Units of `𝒪_w` have value one. -/
theorem val_eq_one_of_isUnit {Ω : Type*} [Field Ω] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation Ω Γ₀) {x : w.valuationSubring}
    (hx : IsUnit x) : w (x : Ω) = 1 := by
  obtain ⟨u, rfl⟩ := hx
  have h := congrArg (fun y : w.valuationSubring => w (y : Ω)) u.mul_inv
  simp only [MulMemClass.coe_mul, OneMemClass.coe_one, map_mul, map_one] at h
  have h1 : w ((u : w.valuationSubring) : Ω) ≤ 1 :=
    (w.mem_valuationSubring_iff _).1 (u : w.valuationSubring).2
  have h2 : w (((u⁻¹ : _ˣ) : w.valuationSubring) : Ω) ≤ 1 :=
    (w.mem_valuationSubring_iff _).1 (u⁻¹ : _ˣ).1.2
  by_contra hne
  have hlt := lt_of_le_of_ne h1 hne
  have := lt_of_le_of_lt (mul_le_of_le_one_right' h2) hlt
  rw [h] at this
  exact lt_irrefl _ this

/-- **The valuation is not centred at another point (separatedness).** Let `g : X → Spec T` be
separated, `τ : K(X) → Ω`, and `w` a valuation of `Ω` centred at a point `η` (a local
`𝒪_{X,η} → 𝒪_w` compatible with `τ`). If `w ≤ 1` on `𝒪_{X,c}` for a point `c ≠ η`, then some
element of the maximal ideal of `𝒪_{X,c}` has value one. -/
theorem exists_val_eq_one_of_centre {X : Scheme.{u}} [IrreducibleSpace X] {T : CommRingCat.{u}}
    (g : X ⟶ Spec T) [IsSeparated g] {Ω : Type u} [Field Ω]
    (τ : X.functionField ⟶ CommRingCat.of Ω) {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation Ω Γ₀) (c η : X)
    (hAw : ∀ b, w (τ.hom ((X.presheaf.stalkSpecializes (genericPoint_specializes c)).hom b)) ≤ 1)
    (φ₀ : X.presheaf.stalk η ⟶ CommRingCat.of w.valuationSubring) [IsLocalHom φ₀.hom]
    (hφ₀ : ∀ b, τ.hom ((X.presheaf.stalkSpecializes (genericPoint_specializes η)).hom b) =
      algebraMap w.valuationSubring Ω (φ₀.hom b))
    (hne : c ≠ η) :
    ∃ b ∈ maximalIdeal (X.presheaf.stalk c),
      w (τ.hom ((X.presheaf.stalkSpecializes (genericPoint_specializes c)).hom b)) = 1 := by
  by_contra hcon
  push Not at hcon
  let ψ := (X.presheaf.stalkSpecializes (genericPoint_specializes c) ≫ τ).hom
  let φc : X.presheaf.stalk c →+* w.valuationSubring :=
    ψ.codRestrict w.valuationSubring fun b => (w.mem_valuationSubring_iff _).2 (hAw b)
  have hloc : IsLocalHom (CommRingCat.ofHom φc).hom := ⟨fun b hb => by
    by_contra hnu
    have hb1 := val_eq_one_of_isUnit w hb
    exact hcon b ((mem_maximalIdeal _).2 hnu) hb1⟩
  let a := CommRingCat.ofHom (algebraMap w.valuationSubring Ω)
  have e1 : CommRingCat.ofHom φc ≫ a =
      X.presheaf.stalkSpecializes (genericPoint_specializes c) ≫ τ := by
    ext b
    rfl
  have e2 : φ₀ ≫ a = X.presheaf.stalkSpecializes (genericPoint_specializes η) ≫ τ := by
    ext b
    exact (hφ₀ b).symm
  have h₁ : Spec.map a ≫ Spec.map (CommRingCat.ofHom φc) ≫ X.fromSpecStalk c =
      Spec.map a ≫ Spec.map φ₀ ≫ X.fromSpecStalk η := by
    rw [← Category.assoc, ← Spec.map_comp, e1, ← Category.assoc, ← Spec.map_comp, e2,
      Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have h₂ : Spec.map (CommRingCat.ofHom φc) ≫ X.fromSpecStalk c ≫ g =
      Spec.map φ₀ ≫ X.fromSpecStalk η ≫ g := by
    refine spec_ext_of_injective a Subtype.val_injective _ _ ?_
    have := h₁ =≫ g
    simp only [Category.assoc] at this
    exact this
  exact hne (centre_unique g (K := Ω) (CommRingCat.ofHom φc) φ₀ h₁ h₂)

end Uniqueness

section Horizontal

variable {Ω : Type*} [Field Ω] {A : Type*} [CommRing A] [IsDomain A] [Algebra A Ω]
  [IsFractionRing A Ω] (𝔮 : Ideal A) [𝔮.IsPrime]

omit [IsDomain A] in
theorem isUnit_algebraMap_primeCompl (y : 𝔮.primeCompl) : IsUnit (algebraMap A Ω y) := by
  refine isUnit_iff_ne_zero.2 fun h => ?_
  have h0 : (y : A) = 0 := IsFractionRing.injective A Ω (by rw [h, map_zero])
  exact y.2 (h0 ▸ 𝔮.zero_mem)

/-- The embedding `A_𝔮 → Ω`. -/
def localizationLift : Localization.AtPrime 𝔮 →+* Ω :=
  IsLocalization.lift (M := 𝔮.primeCompl) (isUnit_algebraMap_primeCompl 𝔮)

theorem localizationLift_injective : Function.Injective (localizationLift (Ω := Ω) 𝔮) := by
  refine (IsLocalization.lift_injective_iff _).2 fun x y => ?_
  constructor
  · intro h
    rw [IsLocalization.injective (Localization.AtPrime 𝔮)
      (Ideal.primeCompl_le_nonZeroDivisors 𝔮) h]
  · intro h
    rw [IsFractionRing.injective A Ω h]

omit [IsDomain A] in
theorem localizationLift_algebraMap (a : A) :
    localizationLift (Ω := Ω) 𝔮 (algebraMap A (Localization.AtPrime 𝔮) a) = algebraMap A Ω a :=
  IsLocalization.lift_eq _ a

variable [IsDiscreteValuationRing (Localization.AtPrime 𝔮)]

/-- The valuation subring `A_𝔮 ⊆ Ω`, for `A_𝔮` a discrete valuation ring. -/
def localizationValuationSubring : ValuationSubring Ω :=
  { (localizationLift (Ω := Ω) 𝔮).range with
    mem_or_inv_mem' := fun g => by
      by_cases hg : g = 0
      · exact Or.inl ⟨0, by rw [hg, map_zero]⟩
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) g
      have hb0 : algebraMap A Ω b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
      have ha0 : algebraMap A Ω a ≠ 0 := fun h => hg (by rw [h, zero_div])
      rcases ValuationRing.dvd_total (algebraMap A (Localization.AtPrime 𝔮) b)
        (algebraMap A (Localization.AtPrime 𝔮) a) with ⟨z, hz⟩ | ⟨z, hz⟩
      · left
        refine ⟨z, ?_⟩
        have := congrArg (localizationLift (Ω := Ω) 𝔮) hz
        rw [map_mul, localizationLift_algebraMap, localizationLift_algebraMap] at this
        rw [this, mul_div_cancel_left₀ _ hb0]
      · right
        refine ⟨z, ?_⟩
        have := congrArg (localizationLift (Ω := Ω) 𝔮) hz
        rw [map_mul, localizationLift_algebraMap, localizationLift_algebraMap] at this
        rw [inv_div, this, mul_div_cancel_left₀ _ ha0] }

theorem mem_localizationValuationSubring {g : Ω} :
    g ∈ localizationValuationSubring 𝔮 ↔ ∃ y, localizationLift 𝔮 y = g :=
  Iff.rfl

/-- `A_𝔮 ⊆ Ω` is a discrete valuation ring. -/
theorem localizationValuationSubring_isDVR :
    IsDiscreteValuationRing (localizationValuationSubring (Ω := Ω) 𝔮) := by
  let φ : Localization.AtPrime 𝔮 →+* localizationValuationSubring (Ω := Ω) 𝔮 :=
    (localizationLift 𝔮).codRestrict (localizationValuationSubring 𝔮) fun y => ⟨y, rfl⟩
  have hbij : Function.Bijective φ := by
    refine ⟨fun x y h => localizationLift_injective 𝔮 (congrArg Subtype.val h), ?_⟩
    rintro ⟨g, y, rfl⟩
    exact ⟨y, rfl⟩
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (RingEquiv.ofBijective φ hbij)

/-- `A` lies in `A_𝔮`. -/
theorem algebraMap_mem_localizationValuationSubring (a : A) :
    algebraMap A Ω a ∈ localizationValuationSubring 𝔮 :=
  ⟨algebraMap A (Localization.AtPrime 𝔮) a, localizationLift_algebraMap 𝔮 a⟩

/-- Elements outside `𝔮` are invertible in `A_𝔮`. -/
theorem inv_algebraMap_mem_localizationValuationSubring {s : A} (hs : s ∉ 𝔮) :
    (algebraMap A Ω s)⁻¹ ∈ localizationValuationSubring 𝔮 := by
  refine ⟨IsLocalization.mk' (Localization.AtPrime 𝔮) (1 : A) (⟨s, hs⟩ : 𝔮.primeCompl), ?_⟩
  have h := congrArg (localizationLift (Ω := Ω) 𝔮)
    (IsLocalization.mk'_spec (Localization.AtPrime 𝔮) (1 : A) (⟨s, hs⟩ : 𝔮.primeCompl))
  rw [map_mul, localizationLift_algebraMap, localizationLift_algebraMap, map_one] at h
  have hs0 : algebraMap A Ω s ≠ 0 := (isUnit_algebraMap_primeCompl 𝔮 ⟨s, hs⟩).ne_zero
  exact eq_inv_of_mul_eq_one_left h

/-- Membership in `A_𝔮` is regularity at `𝔮`. -/
theorem exists_of_mem_localizationValuationSubring {g : Ω}
    (hg : g ∈ localizationValuationSubring 𝔮) :
    ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * g = algebraMap A Ω r := by
  obtain ⟨y, rfl⟩ := hg
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl y
  refine ⟨r, s, s.2, ?_⟩
  have h := congrArg (localizationLift (Ω := Ω) 𝔮)
    (IsLocalization.mk'_spec (Localization.AtPrime 𝔮) r s)
  rw [map_mul, localizationLift_algebraMap, localizationLift_algebraMap] at h
  rw [mul_comm]
  exact h

/-- **Horizontal primes.** If `f` lies in every discrete valuation subring of `Ω` with a property
`P` other than `A_g`, then `f` is regular at every prime `𝔮` with `A_𝔮` a discrete valuation ring,
`A_𝔮 ⊆ Ω` satisfying `P`, and `A_𝔮 ≠ A_g`. -/
theorem exists_of_forall_valuationSubring (P : ValuationSubring Ω → Prop)
    (Ag : ValuationSubring Ω) {f : Ω}
    (hhor : ∀ Q : ValuationSubring Ω, P Q → IsDiscreteValuationRing Q → Q ≠ Ag → f ∈ Q)
    (hP : P (localizationValuationSubring 𝔮)) (hAg : localizationValuationSubring 𝔮 ≠ Ag) :
    ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * f = algebraMap A Ω r :=
  exists_of_mem_localizationValuationSubring 𝔮
    (hhor _ hP (localizationValuationSubring_isDVR 𝔮) hAg)

end Horizontal

section Assembly

universe v

variable {Ω : Type*} [Field Ω] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {w : Valuation Ω Γ₀}

/-- **`hcentre`.** Let `w` be discrete with uniformizer `ϖ_w`. Suppose every constant place
`O ≠ ē, ⊤` of `κ_w` has a centre: a local Noetherian ring `A` with fraction field `Ω` and an
element `ϖ` of its maximal ideal, a nonzerodivisor with `A / ϖ` a discrete valuation ring, such
that `A ⊆ Õ`, `w ϖ < 1`, `w` is not centred at the closed point, and `f` is regular at the
height-one primes of `A` off `ϖ`. Then the hypothesis `hcentre` of
`SpecialFibreFunctionField.reduce_mem_polePart` holds. -/
theorem hcentre_of_centres {k : Type*} [Field k] [Algebra k (ResidueField w.valuationSubring)]
    (ē : ValuationSubring (ResidueField w.valuationSubring)) {ϖw : Ω} (hϖ0 : ϖw ≠ 0)
    (hϖw : w ϖw < 1) (hdisc : ∀ x : Ω, x ≠ 0 → ∃ m : ℤ, w x = w ϖw ^ m) {f : Ω}
    (hc : ∀ O : ValuationSubring (ResidueField w.valuationSubring), IsConstPlace k O →
      O ≠ ē → O ≠ ⊤ → ∃ (A : Type v) (_ : CommRing A) (_ : IsLocalRing A)
        (_ : IsNoetherianRing A) (_ : Algebra A Ω) (_ : IsFractionRing A Ω) (ϖ : A)
        (_ : IsDomain (A ⧸ Ideal.span {ϖ})),
        IsDiscreteValuationRing (A ⧸ Ideal.span {ϖ}) ∧ ϖ ∈ nonZeroDivisors A ∧
        ϖ ∈ maximalIdeal A ∧ w (algebraMap A Ω ϖ) < 1 ∧
        (∃ c ∈ maximalIdeal A, w (algebraMap A Ω c) = 1) ∧
        (∀ a : A, algebraMap A Ω a ∈ liftValuationSubring w O) ∧
        (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → ϖ ∉ 𝔮 →
          ∃ r s : A, s ∉ 𝔮 ∧ algebraMap A Ω s * f = algebraMap A Ω r)) :
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
  obtain ⟨A, _, _, _, _, _, ϖ, _, _, hϖ, hm, hϖw', hcen, hdom, hhor⟩ := hc O hO hne htop
  exact centre_spec w hϖ hm O hdom hϖw' hcen hhor

end Assembly

section Model

open AlgebraicGeometry CategoryTheory

universe u

/-- For an integral scheme and a field isomorphism `τ : K(X) ≅ Ω`, every stalk has fraction field
`Ω` (through the generic germ followed by `τ`). -/
theorem isFractionRing_stalk {X : Scheme.{u}} [IsIntegral X] (c : X) {Ω : Type u} [Field Ω]
    (τ : X.functionField ⟶ CommRingCat.of Ω) (hτ : Function.Bijective τ.hom) :
    letI := (X.presheaf.stalkSpecializes (genericPoint_specializes c) ≫ τ).hom.toAlgebra
    IsFractionRing (X.presheaf.stalk c) Ω := by
  let _ := (X.presheaf.stalkSpecializes (genericPoint_specializes c) ≫ τ).hom.toAlgebra
  let e : X.functionField ≃ₐ[X.presheaf.stalk c] Ω :=
    { RingEquiv.ofBijective τ.hom hτ with commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors _) e

/-- **`hcentre` from a proper model.** Let `g : X → Spec T` be proper with `X` integral and locally
Noetherian, `τ : K(X) ≅ Ω`, and `w` a discrete valuation of `Ω` centred at a point `η` (a local
surjection `𝒪_{X,η} → 𝒪_w` compatible with `τ`). Let `ρ : T → Ω` be the generic point of
`Spec T`, landing in `Õ` for every constant place `O`. Suppose that at every centre `c` of a
constant place `O ≠ ē, ⊤` (a point with a local `𝒪_{X,c} → Õ` compatible with `τ`) there is an
element `ϖ` of `𝔪_c` which is a nonzerodivisor with `𝒪_{X,c}/ϖ` a discrete valuation ring and
`w ϖ < 1`, and `f` is regular at the height-one primes of `𝒪_{X,c}` off `ϖ`. Then `hcentre`
holds. -/
theorem hcentre_of_model {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {T : CommRingCat.{u}} (g : X ⟶ Spec T) [IsProper g] {Ω : Type u} [Field Ω]
    (τ : X.functionField ⟶ CommRingCat.of Ω) (hτ : Function.Bijective τ.hom)
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {w : Valuation Ω Γ₀}
    {ϖw : Ω} (hϖ0 : ϖw ≠ 0) (hϖw : w ϖw < 1) (hdisc : ∀ x : Ω, x ≠ 0 → ∃ m : ℤ, w x = w ϖw ^ m)
    {k : Type*} [Field k] [Algebra k (ResidueField w.valuationSubring)]
    (ē : ValuationSubring (ResidueField w.valuationSubring))
    (ρ : T ⟶ CommRingCat.of Ω)
    (hρ : (Spec.map τ ≫ X.fromSpecStalk (genericPoint X)) ≫ g = Spec.map ρ)
    (hρO : ∀ O : ValuationSubring (ResidueField w.valuationSubring), IsConstPlace k O →
      ∀ t, ρ.hom t ∈ liftValuationSubring w O)
    (η : X) (φ₀ : X.presheaf.stalk η ⟶ CommRingCat.of w.valuationSubring) [IsLocalHom φ₀.hom]
    (hφ₀ : ∀ b, τ.hom ((X.presheaf.stalkSpecializes (genericPoint_specializes η)).hom b) =
      algebraMap w.valuationSubring Ω (φ₀.hom b)) (hφ₀s : Function.Surjective φ₀.hom)
    {f : Ω}
    (hloc : ∀ O : ValuationSubring (ResidueField w.valuationSubring), IsConstPlace k O →
      O ≠ ē → O ≠ ⊤ → ∀ (c : X)
      (φ : X.presheaf.stalk c ⟶ CommRingCat.of (liftValuationSubring w O)), IsLocalHom φ.hom →
      (∀ b, τ.hom ((X.presheaf.stalkSpecializes (genericPoint_specializes c)).hom b) =
        algebraMap (liftValuationSubring w O) Ω (φ.hom b)) →
      ∃ (ϖ : X.presheaf.stalk c) (_ : IsDomain (X.presheaf.stalk c ⧸ Ideal.span {ϖ})),
        IsDiscreteValuationRing (X.presheaf.stalk c ⧸ Ideal.span {ϖ}) ∧
        ϖ ∈ nonZeroDivisors (X.presheaf.stalk c) ∧ ϖ ∈ maximalIdeal (X.presheaf.stalk c) ∧
        w (τ.hom ((X.presheaf.stalkSpecializes (genericPoint_specializes c)).hom ϖ)) < 1 ∧
        ∀ 𝔮 : Ideal (X.presheaf.stalk c), 𝔮.IsPrime → 𝔮.height = 1 → ϖ ∉ 𝔮 →
          ∃ r s : X.presheaf.stalk c, s ∉ 𝔮 ∧
            τ.hom ((X.presheaf.stalkSpecializes (genericPoint_specializes c)).hom s) * f =
            τ.hom ((X.presheaf.stalkSpecializes (genericPoint_specializes c)).hom r)) :
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
  let ρO : T →+* liftValuationSubring w O :=
    ρ.hom.codRestrict (liftValuationSubring w O) (hρO O hO)
  have hsq : (Spec.map τ ≫ X.fromSpecStalk (genericPoint X)) ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap (liftValuationSubring w O) Ω)) ≫
        Spec.map (CommRingCat.ofHom ρO) := by
    rw [hρ, ← Spec.map_comp]
    rfl
  obtain ⟨c, φ, hφ, -, hgerm⟩ := exists_centre_germ g τ (liftValuationSubring w O)
    (Spec.map (CommRingCat.ofHom ρO)) hsq
  obtain ⟨ϖ, _, _, hϖ, hm, hϖw', hhor⟩ := hloc O hO hne htop c φ hφ hgerm
  have hcη : c ≠ η := by
    rintro rfl
    apply htop
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨b, rfl⟩ := hφ₀s y
    have hmem : algebraMap w.valuationSubring Ω (φ₀.hom b) ∈ liftValuationSubring w O := by
      rw [← hφ₀, hgerm]
      exact (φ.hom b).2
    obtain ⟨_, hres⟩ := hmem
    exact hres
  let _ := (X.presheaf.stalkSpecializes (genericPoint_specializes c) ≫ τ).hom.toAlgebra
  have := isFractionRing_stalk c τ hτ
  have hdom : ∀ b : X.presheaf.stalk c,
      algebraMap (X.presheaf.stalk c) Ω b ∈ liftValuationSubring w O := fun b => by
    change τ.hom ((X.presheaf.stalkSpecializes (genericPoint_specializes c)).hom b) ∈ _
    rw [hgerm b]
    exact (φ.hom b).2
  have hAw : ∀ b, w (τ.hom ((X.presheaf.stalkSpecializes (genericPoint_specializes c)).hom b))
      ≤ 1 := fun b =>
    (w.mem_valuationSubring_iff _).mp (liftValuationSubring_le O (hdom b))
  have hcen := exists_val_eq_one_of_centre g τ w c η hAw φ₀ hφ₀ hcη
  exact centre_spec w hϖ hm O hdom hϖw' hcen hhor

end Model

end Centre

end ZInQ.Contrib.CMHeight62Full
