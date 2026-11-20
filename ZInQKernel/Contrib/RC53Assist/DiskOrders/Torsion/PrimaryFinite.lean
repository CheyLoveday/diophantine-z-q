import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TorsionReduction

/-!
# Finiteness of the `p`-primary torsion of an elliptic curve over a number field

Let `K` be a number field, `W/K` an elliptic curve and `p` a prime. This file proves, without the
Mordell–Weil theorem, that the `p`-primary component `W(K)[p^∞]` of the group of rational points
is finite. The proof is the classical reduction argument (Silverman, *The Arithmetic of Elliptic
Curves*, 2nd ed., Proposition VII.3.1(b), read over the global field):

1. choose a height-one prime `u` of `𝓞_K` with `p ∉ u` at which the five coefficients of `W` are
   integral and the discriminant `Δ(W)` is a unit. Such a prime exists: a nonzero algebraic
   integer `c` lies outside every prime of `𝓞_K` above a rational prime larger than the absolute
   norm of `(c)`, and one takes for `c` the product of `p` with denominators of
   `a₁, a₂, a₃, a₄, a₆` and `Δ⁻¹` (`exists_notMem_of_ne_zero`, `exists_goodPrime`);
2. at such a prime the equation of `W` is an integral model with good reduction, and for every
   `n` the order of `W(K)[p^n]` divides the number `N` of points of the reduced curve over the
   residue field (the vendored theorem
   `WeierstrassCurve.Affine.Point.card_torsionBy_dvd_card_reduction`, Silverman VII.3.1(b));
3. the residue field `𝓞_K/u` is finite, so `N` is finite and nonzero (`finite_residueField`,
   `finite_point`);
4. a group whose `p^n`-torsion has order dividing a fixed `N ≠ 0` for every `n` has its
   `p`-primary component inside the `p^N`-torsion, hence finite
   (`primaryComponent_le_torsionBy`, `finite_primaryComponent_of_card_dvd`).

## Main results

* `finite_primaryComponent`: for an elliptic curve `W` over a number field `K` and a prime `p`,
  the `p`-primary component of `W(K)` is finite.

Kinds: PROVED throughout (no inputs beyond Mathlib and the vendored reduction theory).
-/

noncomputable section

set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.DiskOrders.Torsion

open IsDedekindDomain NumberField WeierstrassCurve IsLocalRing

section PrimaryBound

variable {A : Type*} [AddCommGroup A]

/-- **Uniformly bounded `p`-power torsion lies in one torsion subgroup**: if the order of
`A[p^n]` divides a fixed `N ≠ 0` for every `n`, then every element of `p`-power order has order
`p^j` with `p^j ∣ N`, so `j < p^j ≤ N` and the `p`-primary component of `A` is contained in
`A[p^N]`. Kind: PROVED. -/
theorem primaryComponent_le_torsionBy {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : N ≠ 0)
    (h : ∀ n : ℕ, Nat.card (AddSubgroup.torsionBy A ((p ^ n : ℕ) : ℤ)) ∣ N) :
    AddCommGroup.primaryComponent A p ≤ AddSubgroup.torsionBy A ((p ^ N : ℕ) : ℤ) := by
  intro x hx
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.1 hx
  have hxk : x ∈ AddSubgroup.torsionBy A ((p ^ k : ℕ) : ℤ) :=
    AddSubgroup.torsionBy.nsmul_iff.2 hk
  -- the order of `x` divides the order of `A[p^k]`, hence `N`, and it divides `p^k`
  have hc : Nat.card (AddSubgroup.torsionBy A ((p ^ k : ℕ) : ℤ)) • x = 0 :=
    congrArg Subtype.val (card_nsmul_eq_zero' (x := (⟨x, hxk⟩ : AddSubgroup.torsionBy A _)))
  have hoN : addOrderOf x ∣ N := (addOrderOf_dvd_of_nsmul_eq_zero hc).trans (h k)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (addOrderOf_dvd_of_nsmul_eq_zero hk)
  have hjN : j ≤ N :=
    (Nat.lt_pow_self hp.one_lt).le.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (hj ▸ hoN))
  rw [AddSubgroup.torsionBy.nsmul_iff, ← addOrderOf_dvd_iff_nsmul_eq_zero, hj]
  exact pow_dvd_pow p hjN

/-- **A primary component with uniformly bounded `p`-power torsion is finite**: if the order of
`A[p^n]` divides a fixed `N ≠ 0` for every `n`, the `p`-primary component of `A` is finite.
Kind: PROVED. -/
theorem finite_primaryComponent_of_card_dvd {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : N ≠ 0)
    (h : ∀ n : ℕ, Nat.card (AddSubgroup.torsionBy A ((p ^ n : ℕ) : ℤ)) ∣ N) :
    Finite (AddCommGroup.primaryComponent A p) :=
  have : Finite (AddSubgroup.torsionBy A ((p ^ N : ℕ) : ℤ)) :=
    Nat.finite_of_card_ne_zero fun h0 => hN (Nat.eq_zero_of_zero_dvd (h0 ▸ h N))
  Finite.of_injective _ (AddSubgroup.inclusion_injective (primaryComponent_le_torsionBy hp hN h))

/-- Non-vacuity of the bound: in `ℤ/4` every `2^n`-torsion subgroup has order dividing `4`, so
the criterion applies. Kind: PROVED (non-vacuity). -/
example : Finite (AddCommGroup.primaryComponent (ZMod 4) 2) :=
  finite_primaryComponent_of_card_dvd Nat.prime_two (N := 4) four_ne_zero fun _ =>
    (AddSubgroup.card_addSubgroup_dvd_card _).trans (by rw [Nat.card_zmod])

end PrimaryBound

section FinitePoints

/-- **A Weierstrass curve over a finite ring has finitely many points**: a point is the point at
infinity or is determined by its two coordinates, so the points inject into `Option (R × R)`.
Kind: PROVED. -/
theorem finite_point {R : Type*} [CommRing R] [Finite R] (W : Affine R) : Finite W.Point :=
  Finite.of_injective (β := Option (R × R))
    (fun P => match P with
      | .zero => none
      | .some x y _ => Option.some (x, y))
    (by
      rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hPQ
      · rfl
      · cases hPQ
      · cases hPQ
      · simp only [Option.some.injEq, Prod.mk.injEq] at hPQ
        obtain ⟨rfl, rfl⟩ := hPQ
        rfl)

end FinitePoints

section Primes

variable (K : Type*) [Field K] [NumberField K]

/-- **The residue field of the valuation ring of a finite place of a number field is finite**:
the valuation ring of the `u`-adic valuation is the localization of `𝓞_K` at `u`, whose residue
field is `𝓞_K/u`, a finite field. Kind: PROVED. -/
theorem finite_residueField (u : HeightOneSpectrum (𝓞 K)) :
    Finite (ResidueField (u.valuation K).valuationSubring) := by
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact Finite.of_equiv _ (IsLocalization.AtPrime.equivQuotMaximalIdeal u.asIdeal
    (HeightOneSpectrum.valuationSubringAtPrime K u)).toEquiv

/-- **A nonzero algebraic integer lies outside some height-one prime**: if `c ≠ 0` and `n` is
the absolute norm of `(c)`, then `c ∣ n`; a prime of `𝓞_K` above a rational prime `q > n` does
not contain `n`, hence not `c`. Kind: PROVED. -/
theorem exists_notMem_of_ne_zero {c : 𝓞 K} (hc : c ≠ 0) :
    ∃ u : HeightOneSpectrum (𝓞 K), c ∉ u.asIdeal := by
  set n := Ideal.absNorm (Ideal.span {c}) with hn_def
  have hn : n ≠ 0 := by
    rw [hn_def, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc
  have hnc : (n : 𝓞 K) ∈ Ideal.span {c} := Ideal.absNorm_mem _
  obtain ⟨q, hqn, hq⟩ := Nat.exists_infinite_primes (n + 1)
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hP : (Ideal.span {(q : ℤ)}).IsPrime := (Ideal.span_singleton_prime hqZ.ne_zero).2 hqZ
  have hPmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    hP.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hqZ.ne_zero)
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K)
    (Ideal.span {(q : ℤ)}) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 K)).injective_int]
      exact bot_le)
  -- a natural number lies in `Q` exactly when `q` divides it
  have hmem (m : ℕ) : (m : 𝓞 K) ∈ Q ↔ q ∣ m := by
    have : ((m : ℤ) ∈ Ideal.under ℤ Q) ↔ (m : 𝓞 K) ∈ Q := by
      rw [Ideal.mem_comap, map_natCast]
    rw [← this, hQ, Ideal.mem_span_singleton, Int.natCast_dvd_natCast]
  have hQ0 : Q ≠ ⊥ := by
    intro h
    have hq0 : (q : 𝓞 K) ∈ Q := (hmem q).2 dvd_rfl
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hq0
    exact hq.ne_zero hq0
  refine ⟨⟨Q, hQmax.isPrime, hQ0⟩, fun hcQ => ?_⟩
  have hnQ : (n : 𝓞 K) ∈ Q := (Ideal.span_le.2 (Set.singleton_subset_iff.2 hcQ)) hnc
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ((hmem n).1 hnQ)
  omega

/-- **An element of `K` is integral at all primes avoiding one denominator**: writing `z = x/y`
with `x, y ∈ 𝓞_K` and `y ≠ 0`, `v_u(z) ≤ 1` at every height-one prime `u` with `y ∉ u`.
Kind: PROVED. -/
theorem exists_valuation_le_one (z : K) :
    ∃ y : 𝓞 K, y ≠ 0 ∧ ∀ u : HeightOneSpectrum (𝓞 K), y ∉ u.asIdeal → u.valuation K z ≤ 1 := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) z
  refine ⟨y, nonZeroDivisors.ne_zero hy, fun u hu => ?_⟩
  rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hu,
    div_one]
  exact u.intValuation_le_one x

/-- **A prime of good reduction avoiding a given nonzero algebraic integer**: for a Weierstrass
curve `W/K` and a nonzero `c ∈ 𝓞_K` there is a height-one prime `u ∌ c` at which
`a₁, a₂, a₃, a₄, a₆` and `Δ⁻¹` all have valuation at most `1`, so that the equation of `W` is
integral at `u` with unit discriminant. The prime avoids `c` and one denominator of each of the six
elements (`exists_valuation_le_one`, `exists_notMem_of_ne_zero`). Kind: PROVED. -/
theorem exists_goodPrime (W : WeierstrassCurve K) {c : 𝓞 K} (hc : c ≠ 0) :
    ∃ u : HeightOneSpectrum (𝓞 K), c ∉ u.asIdeal ∧ u.valuation K W.a₁ ≤ 1 ∧
      u.valuation K W.a₂ ≤ 1 ∧ u.valuation K W.a₃ ≤ 1 ∧ u.valuation K W.a₄ ≤ 1 ∧
        u.valuation K W.a₆ ≤ 1 ∧ u.valuation K W.Δ⁻¹ ≤ 1 := by
  obtain ⟨y₁, h₁, H₁⟩ := exists_valuation_le_one K W.a₁
  obtain ⟨y₂, h₂, H₂⟩ := exists_valuation_le_one K W.a₂
  obtain ⟨y₃, h₃, H₃⟩ := exists_valuation_le_one K W.a₃
  obtain ⟨y₄, h₄, H₄⟩ := exists_valuation_le_one K W.a₄
  obtain ⟨y₆, h₆, H₆⟩ := exists_valuation_le_one K W.a₆
  obtain ⟨y₇, h₇, H₇⟩ := exists_valuation_le_one K W.Δ⁻¹
  obtain ⟨u, hu⟩ := exists_notMem_of_ne_zero K (c := c * y₁ * y₂ * y₃ * y₄ * y₆ * y₇)
    (by simp [hc, h₁, h₂, h₃, h₄, h₆, h₇])
  have hfac (a b : 𝓞 K) (h : a * b ∉ u.asIdeal) : a ∉ u.asIdeal ∧ b ∉ u.asIdeal :=
    ⟨fun ha => h (u.asIdeal.mul_mem_right b ha), fun hb => h (u.asIdeal.mul_mem_left a hb)⟩
  obtain ⟨hu, hu₇⟩ := hfac _ _ hu
  obtain ⟨hu, hu₆⟩ := hfac _ _ hu
  obtain ⟨hu, hu₄⟩ := hfac _ _ hu
  obtain ⟨hu, hu₃⟩ := hfac _ _ hu
  obtain ⟨hu, hu₂⟩ := hfac _ _ hu
  obtain ⟨hu, hu₁⟩ := hfac _ _ hu
  exact ⟨u, hu, H₁ u hu₁, H₂ u hu₂, H₃ u hu₃, H₄ u hu₄, H₆ u hu₆, H₇ u hu₇⟩

end Primes

section Main

variable (K : Type*) [Field K] [NumberField K] [DecidableEq K]

/-- **The `p`-primary torsion of an elliptic curve over a number field is finite**, without the
Mordell–Weil theorem (Silverman, AEC, 2nd ed., Proposition VII.3.1(b), read over the global
field): at a height-one prime `u ∌ p` of good reduction (`exists_goodPrime`), the order of
`W(K)[p^n]` divides the number of points of the reduced curve over the finite residue field, for
every `n` (`WeierstrassCurve.Affine.Point.card_torsionBy_dvd_card_reduction`); a uniform bound on
the `p^n`-torsion makes the `p`-primary component finite (`finite_primaryComponent_of_card_dvd`).
Kind: PROVED. -/
theorem finite_primaryComponent (W : WeierstrassCurve K) [W.IsElliptic] {p : ℕ} (hp : p.Prime) :
    Finite (AddCommGroup.primaryComponent W.toAffine.Point p) := by
  have hp0 : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨u, hpu, h₁, h₂, h₃, h₄, h₆, hΔ⟩ := exists_goodPrime K W hp0
  let R := (u.valuation K).valuationSubring
  have hR (z : K) (hz : u.valuation K z ≤ 1) : ∃ r : R, algebraMap R K r = z :=
    ⟨⟨z, (Valuation.mem_valuationSubring_iff _ _).2 hz⟩, rfl⟩
  -- the equation of `W` is integral at `u` ...
  have : IsIntegral R W.toAffine :=
    isIntegral_of_exists_lift R (hR _ h₁) (hR _ h₂) (hR _ h₃) (hR _ h₄) (hR _ h₆)
  -- ... with unit discriminant, its inverse being integral at `u` as well
  have : (integralModel R W.toAffine).IsElliptic := by
    refine ⟨IsUnit.of_mul_eq_one (⟨W.Δ⁻¹, (Valuation.mem_valuationSubring_iff _ _).2 hΔ⟩ : R) ?_⟩
    apply Subtype.ext
    change algebraMap R K (integralModel R W.toAffine).Δ * W.Δ⁻¹ = 1
    rw [integralModel_Δ_eq]
    exact mul_inv_cancel₀ W.isUnit_Δ.ne_zero
  have := finite_residueField K u
  have := finite_point ((integralModel R W.toAffine).map (residue R)).toAffine
  refine finite_primaryComponent_of_card_dvd hp
    (N := Nat.card ((integralModel R W.toAffine).map (residue R)).toAffine.Point)
    Nat.card_pos.ne' fun n => ?_
  refine Affine.Point.card_torsionBy_dvd_card_reduction u (W := W.toAffine) (n := p ^ n) ?_
  rw [Nat.cast_pow]
  exact fun h => hpu (u.isPrime.mem_of_pow_mem n h)

/-- Non-vacuity: the curve `y² = x³ - x` over `ℚ` (discriminant `64`) is elliptic, so its
rational `2`-primary torsion is finite by `finite_primaryComponent`. Kind: PROVED
(non-vacuity). -/
example : Finite (AddCommGroup.primaryComponent
    (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).toAffine.Point 2) :=
  have : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).IsElliptic :=
    ⟨isUnit_iff_ne_zero.2 (by norm_num [Δ, b₂, b₄, b₆, b₈])⟩
  finite_primaryComponent ℚ _ Nat.prime_two

end Main

end ZInQ.Contrib.RC53Assist.DiskOrders.Torsion
