import ZInQKernel.Contrib.CloudB3E1RingClass.InertiaLocal

/-!
# Inertia at a split prime: the kernel of `Gal(H_r/K) → Cl(K)` lies in the inertia group

Manuscript `diophantine_zq.tex`, tex 3679–3681 ("the inertia group at `r` is the image of
`(𝒪_K/r)^× = 𝐅_r^× × 𝐅_r^×` modulo the diagonal; `(a, 1) ≡ (1, a⁻¹)`").

Let `K` be a quadratic field and `r` a rational prime with `r𝒪_K = 𝔯 𝔯'`, `𝔯 ≠ 𝔯'`.

* Arithmetic of the split prime: `natCast_mem_iff_dvd`, `eq_or_eq_of_natCast_mem` (the only
  primes over `r` are `𝔯`, `𝔯'`), `absNorm_right_eq` and `exists_natCast_eq_mk` (residue degree
  one), `exponent_conductorModulus_le_one` and `dvd_conductor_ringClassOrder_left` (the conductor
  of `ℤ + r𝒪_K` has exponent exactly one at `𝔯` and `𝔯'`).
* Ray classes of local ideles: `rayClassQuotient_ofAdicCompletion_eq_one` (a local unit congruent
  to one has trivial ray class) and `principalRayClass_eq_rayClassQuotient` (the principal ray class
  of `x` is the class of the idele `(x⁻¹ at v₁, x⁻¹ at v₂)` when the modulus is supported at
  `v₁, v₂` and has no real places).
* `rayClassToPic_principalRayClass_natCast`: the principal class of an integer prime to `r` dies in
  `Pic(ℤ + r𝒪_K)`.
* **`exists_unitPic_eq`**: a local unit at `𝔯'` has the Picard class of a local unit at `𝔯`.
* **`ker_galToClassGroup_le_inertiaGal`**: `ker(Gal(H_r/K) → Cl(K)) ≤ inertiaGal r S 𝔯`.

Kinds: definitions and PROVED.
-/

noncomputable section

open NumberField IsDedekindDomain
open TauCeti TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.SelmerComplex

namespace ZInQ.Contrib.CloudB3E1RingClass

variable {K : Type} [Field K] [NumberField K]

/-! ### Arithmetic of a split rational prime in a quadratic field -/

section Split

variable {r : ℕ} (hr : r.Prime) {𝔯 𝔯' : HeightOneSpectrum (𝓞 K)}

omit [NumberField K] in
include hr in
/-- Bezout for a natural number prime to `r`. Kind: PROVED. -/
theorem exists_bezout (c : ℕ) (hc : ¬ r ∣ c) :
    ∃ a b : 𝓞 K, (r : 𝓞 K) * a + (c : 𝓞 K) * b = 1 := by
  rcases Nat.coprime_or_dvd_of_prime hr c with hco | hd
  · have h1 : ((Nat.gcd r c : ℕ) : ℤ) = r * Nat.gcdA r c + c * Nat.gcdB r c :=
      Nat.gcd_eq_gcd_ab r c
    rw [hco, Nat.cast_one] at h1
    refine ⟨(Nat.gcdA r c : 𝓞 K), (Nat.gcdB r c : 𝓞 K), ?_⟩
    have := congrArg (fun z : ℤ => (z : 𝓞 K)) h1
    push_cast at this
    exact this.symm
  · exact absurd hd hc

omit [NumberField K] in
include hr in
/-- At a prime containing `r`, a natural number lies in the prime exactly when `r` divides it.
Kind: PROVED. -/
theorem natCast_mem_iff_dvd (v : HeightOneSpectrum (𝓞 K)) (hv : (r : 𝓞 K) ∈ v.asIdeal) (c : ℕ) :
    (c : 𝓞 K) ∈ v.asIdeal ↔ r ∣ c := by
  constructor
  · intro hc
    by_contra hd
    obtain ⟨a, b, hab⟩ := exists_bezout (K := K) hr c hd
    apply v.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_right _ hv) (v.asIdeal.mul_mem_right _ hc)
  · rintro ⟨m, rfl⟩
    rw [Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hv

omit [NumberField K] in
/-- An integer lies in a prime exactly when its absolute value does. Kind: PROVED. -/
theorem intCast_mem_iff_natAbs (v : HeightOneSpectrum (𝓞 K)) (a : ℤ) :
    (a : 𝓞 K) ∈ v.asIdeal ↔ (a.natAbs : 𝓞 K) ∈ v.asIdeal := by
  rcases Int.natAbs_eq a with h | h
  · conv_lhs => rw [h]
    rw [Int.cast_natCast]
  · conv_lhs => rw [h]
    rw [Int.cast_neg, Int.cast_natCast, neg_mem_iff]

variable (hsplit : Ideal.span {(r : 𝓞 K)} = 𝔯.asIdeal * 𝔯'.asIdeal)

omit [NumberField K] in
include hsplit in
/-- `r ∈ 𝔯`. Kind: PROVED. -/
theorem natCast_mem_left : (r : 𝓞 K) ∈ 𝔯.asIdeal := by
  have h : (r : 𝓞 K) ∈ Ideal.span {(r : 𝓞 K)} := Ideal.mem_span_singleton_self _
  rw [hsplit] at h
  exact Ideal.mul_le_left (I := 𝔯.asIdeal) (J := 𝔯'.asIdeal) h

omit [NumberField K] in
include hsplit in
/-- `r ∈ 𝔯'`. Kind: PROVED. -/
theorem natCast_mem_right : (r : 𝓞 K) ∈ 𝔯'.asIdeal := by
  have h : (r : 𝓞 K) ∈ Ideal.span {(r : 𝓞 K)} := Ideal.mem_span_singleton_self _
  rw [hsplit] at h
  exact Ideal.mul_le_right (I := 𝔯.asIdeal) (J := 𝔯'.asIdeal) h

include hsplit in
/-- The only primes containing `r` are `𝔯` and `𝔯'`. Kind: PROVED. -/
theorem eq_or_eq_of_natCast_mem (v : HeightOneSpectrum (𝓞 K)) (hv : (r : 𝓞 K) ∈ v.asIdeal) :
    v = 𝔯 ∨ v = 𝔯' := by
  have hle : 𝔯.asIdeal * 𝔯'.asIdeal ≤ v.asIdeal := by
    rw [← hsplit, Ideal.span_le]
    simpa using hv
  rcases v.isPrime.mul_le.mp hle with h | h
  · exact Or.inl (HeightOneSpectrum.ext (𝔯.isMaximal.eq_of_le v.isPrime.ne_top h).symm)
  · exact Or.inr (HeightOneSpectrum.ext (𝔯'.isMaximal.eq_of_le v.isPrime.ne_top h).symm)

include hr hsplit in
/-- In a quadratic field, a split prime `𝔯'` over `r` has norm `r`. Kind: PROVED. -/
theorem absNorm_right_eq (hK : Module.finrank ℚ K = 2) : Ideal.absNorm 𝔯'.asIdeal = r := by
  have h1 : Ideal.absNorm (Ideal.span {(r : 𝓞 K)}) = r ^ 2 := by
    have : ((r : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (r : ℤ) := by simp
    rw [this, Ideal.absNorm_span_singleton, Algebra.norm_algebraMap, RingOfIntegers.rank, hK]
    simp [Int.natAbs_pow]
  have h2 : Ideal.absNorm 𝔯.asIdeal * Ideal.absNorm 𝔯'.asIdeal = r ^ 2 := by
    rw [← map_mul, ← hsplit, h1]
  have hn1 : Ideal.absNorm 𝔯.asIdeal ≠ 1 := fun h =>
    𝔯.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hn2 : Ideal.absNorm 𝔯'.asIdeal ≠ 1 := fun h =>
    𝔯'.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).mp (Dvd.intro _ h2)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hr).mp (Dvd.intro_left _ h2)
  rw [hj, hk, ← pow_add] at h2
  have hjk : j + k = 2 := Nat.pow_right_injective hr.two_le h2
  have hj0 : j ≠ 0 := by rintro rfl; exact hn1 (by rw [hj, pow_zero])
  have hk0 : k ≠ 0 := by rintro rfl; exact hn2 (by rw [hk, pow_zero])
  rw [hk, show k = 1 by omega, pow_one]

include hr hsplit in
/-- In a quadratic field, every residue class modulo a split prime `𝔯'` over `r` is the class of
a natural number. Kind: PROVED. -/
theorem exists_natCast_eq_mk (hK : Module.finrank ℚ K = 2) (y : 𝓞 K ⧸ 𝔯'.asIdeal) :
    ∃ c : ℕ, Ideal.Quotient.mk 𝔯'.asIdeal (c : 𝓞 K) = y := by
  have : Fact r.Prime := ⟨hr⟩
  have hcard : Nat.card (𝓞 K ⧸ 𝔯'.asIdeal) = r := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, absNorm_right_eq hr hsplit hK]
  have : Finite (𝓞 K ⧸ 𝔯'.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hr.ne_zero)
  have : 𝔯'.asIdeal.IsPrime := 𝔯'.isPrime
  have : CharP (𝓞 K ⧸ 𝔯'.asIdeal) r := ⟨fun x => by
    rw [← map_natCast (Ideal.Quotient.mk 𝔯'.asIdeal), Ideal.Quotient.eq_zero_iff_mem,
      natCast_mem_iff_dvd hr 𝔯' (natCast_mem_right hsplit)]⟩
  let φ : ZMod r →+* 𝓞 K ⧸ 𝔯'.asIdeal := ZMod.castHom (dvd_refl r) _
  have hinj : Function.Injective φ := φ.injective
  have hbij : Function.Bijective φ :=
    hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_zmod])
  obtain ⟨z, rfl⟩ := hbij.2 y
  refine ⟨z.val, ?_⟩
  rw [map_natCast, ← map_natCast φ, ZMod.natCast_zmod_val]

include hsplit in
/-- The conductor exponent of `ℤ + r𝒪_K` at a split prime over `r` is at most one.
Kind: PROVED. -/
theorem exponent_conductorModulus_le_one (hr0 : r ≠ 0) (hne : 𝔯 ≠ 𝔯') :
    (ringClassOrder (K := K) r hr0).conductorModulus.exponent 𝔯' ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have hdvd : 𝔯'.asIdeal ^ 2 ∣ (ringClassOrder (K := K) r hr0).conductorModulus.finitePart :=
    (Modulus.pow_dvd_finitePart_iff_le_exponent _ _).mpr h
  have hc : (ringClassOrder (K := K) r hr0).conductor ∣ 𝔯.asIdeal * 𝔯'.asIdeal :=
    Ideal.dvd_iff_le.mpr (hsplit ▸ span_le_conductor_ringClassOrder r hr0)
  have h3 : 𝔯'.asIdeal * 𝔯'.asIdeal ∣ 𝔯'.asIdeal * 𝔯.asIdeal := by
    rw [← pow_two, mul_comm]
    exact hdvd.trans hc
  have h4 : 𝔯'.asIdeal ∣ 𝔯.asIdeal := (mul_dvd_mul_iff_left 𝔯'.ne_bot).mp h3
  exact hne (HeightOneSpectrum.ext
    (𝔯.isMaximal.eq_of_le 𝔯'.isPrime.ne_top (Ideal.dvd_iff_le.mp h4)))

end Split

/-! ### Ray classes of local ideles -/

section Ideles

/-- The image of a global unit in the units of a completion. Kind: definition. -/
abbrev locUnit (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) : (v.adicCompletion K)ˣ :=
  Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x

/-- The valuation of a global unit in a completion. Kind: PROVED. -/
theorem valued_locUnit (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    Valued.v ((locUnit v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = v.valuation K (x : K) :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : K)

/-- The valuation of an integer of `K` in a completion. Kind: PROVED. -/
theorem valued_algebraMap_intValuation (v : HeightOneSpectrum (𝓞 K)) (y : 𝓞 K) :
    Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) y) = v.intValuation y := by
  rw [IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K)]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans
    (HeightOneSpectrum.valuation_of_algebraMap v _)

/-- A local unit congruent to one modulo the modulus has trivial ray class. Kind: PROVED. -/
theorem rayClassQuotient_ofAdicCompletion_eq_one (𝔪 : Modulus K) (v : HeightOneSpectrum (𝓞 K))
    (z : (v.adicCompletion K)ˣ) (hz1 : Valued.v (z : v.adicCompletion K) = 1)
    (hz : Valued.v ((z : v.adicCompletion K) - 1) ≤ WithZero.exp (-(𝔪.exponent v : ℤ))) :
    rayClassQuotient 𝔪 (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v z) = 1 := by
  have hmem : IdeleGroup.ofAdicCompletion (𝓞 K) K v z ∈ ideleCongrOneSubgroup 𝔪 := by
    rw [mem_ideleCongrOneSubgroup_iff]
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · by_cases h : w = v
      · subst h
        rw [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self]
        exact hz
      · rw [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne w h]
        simp
    · simp
  rw [IdeleClassGroup.ofAdicCompletion_apply, rayClassQuotient_mk_of_mem hmem]
  convert map_one (rayClassMk 𝔪) using 2
  exact Subtype.ext (by simp [hz1])

/-- **The principal ray class of `x` as a local idele class** (modulus without real places and
supported at two places `v₁ ≠ v₂`): the class of the idele `(x⁻¹ at v₁, x⁻¹ at v₂, 1 elsewhere)`.
Kind: PROVED. -/
theorem principalRayClass_eq_rayClassQuotient (𝔪 : Modulus K) (hinf : 𝔪.infinitePart = ∅)
    {v₁ v₂ : HeightOneSpectrum (𝓞 K)} (hne : v₁ ≠ v₂)
    (hsupp : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.finitePart → v = v₁ ∨ v = v₂)
    (x : primeToSubgroup 𝔪) (h₁ : v₁.valuation K ((x : Kˣ) : K) = 1)
    (h₂ : v₂.valuation K ((x : Kˣ) : K) = 1) :
    principalRayClass 𝔪 x = rayClassQuotient 𝔪
      (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v₁ (locUnit v₁ (x : Kˣ))⁻¹ *
        IdeleClassGroup.ofAdicCompletion (𝓞 K) K v₂ (locUnit v₂ (x : Kˣ))⁻¹) := by
  set y : IdeleGroup (𝓞 K) K := IdeleGroup.unitEmbedding (𝓞 K) K (x : Kˣ) *
    (IdeleGroup.ofAdicCompletion (𝓞 K) K v₁ (locUnit v₁ (x : Kˣ))⁻¹ *
      IdeleGroup.ofAdicCompletion (𝓞 K) K v₂ (locUnit v₂ (x : Kˣ))⁻¹) with hy_def
  have hy : y ∈ ideleCongrOneSubgroup 𝔪 := by
    rw [mem_ideleCongrOneSubgroup_iff]
    refine ⟨fun v hv => ?_, fun w hw => ?_⟩
    · rcases hsupp v hv with rfl | rfl
      · rw [hy_def, map_mul, map_mul, HeightOneSpectrum.ideleFiniteCoord_unitEmbedding,
          HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self,
          HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne _ hne, mul_one,
          mul_inv_cancel, Units.val_one, sub_self, map_zero]
        exact zero_le
      · rw [hy_def, map_mul, map_mul, HeightOneSpectrum.ideleFiniteCoord_unitEmbedding,
          HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self,
          HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne _ hne.symm, one_mul,
          mul_inv_cancel, Units.val_one, sub_self, map_zero]
        exact zero_le
    · rw [hinf] at hw
      exact absurd hw (Finset.notMem_empty _)
  have hcls : ((y : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K) =
      IdeleClassGroup.ofAdicCompletion (𝓞 K) K v₁ (locUnit v₁ (x : Kˣ))⁻¹ *
        IdeleClassGroup.ofAdicCompletion (𝓞 K) K v₂ (locUnit v₂ (x : Kˣ))⁻¹ := by
    rw [hy_def, mul_comm, QuotientGroup.mk_mul_of_mem _ (MonoidHom.mem_range.mpr ⟨(x : Kˣ), rfl⟩),
      IdeleClassGroup.ofAdicCompletion_apply, IdeleClassGroup.ofAdicCompletion_apply,
      ← QuotientGroup.mk_mul]
  rw [← hcls, rayClassQuotient_mk_of_mem hy, principalRayClass_apply]
  congr 1
  apply Subtype.ext
  have e₁ : Valued.v (((locUnit v₁ (x : Kˣ))⁻¹ : (v₁.adicCompletion K)ˣ) : v₁.adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, valued_locUnit, h₁, inv_one]
  have e₂ : Valued.v (((locUnit v₂ (x : Kˣ))⁻¹ : (v₂.adicCompletion K)ˣ) : v₂.adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, valued_locUnit, h₂, inv_one]
  rw [NumberFieldArithmetic.coe_principalIdealAway]
  change toPrincipalIdeal (𝓞 K) K (x : Kˣ) =
    FiniteAdeleRing.toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 K) K y)
  rw [hy_def, map_mul, map_mul, map_mul, map_mul,
    HeightOneSpectrum.toFractionalIdeal_toFiniteIdele_ofAdicCompletion,
    HeightOneSpectrum.toFractionalIdeal_toFiniteIdele_ofAdicCompletion, e₁, e₂]
  simp

end Ideles

/-! ### The split case: the kernel lies in the inertia group -/

section Main

variable {r : ℕ} (hr : r.Prime) {𝔯 𝔯' : HeightOneSpectrum (𝓞 K)}
  (hsplit : Ideal.span {(r : 𝓞 K)} = 𝔯.asIdeal * 𝔯'.asIdeal) (hne : 𝔯 ≠ 𝔯')

include hr hsplit hne in
/-- **`𝔯` divides the conductor of `ℤ + r𝒪_K`.** Otherwise some `t` in the conductor lies outside
`𝔯`; for `y ∈ 𝔯' \ 𝔯` the element `t y` lies in `ℤ + r𝒪_K` and in `𝔯'` but not in `𝔯`, while
every element `a + r z` of `ℤ + r𝒪_K` lies in `𝔯` as soon as it lies in `𝔯'`. Kind: PROVED. -/
theorem dvd_conductor_ringClassOrder_left :
    𝔯.asIdeal ∣ (ringClassOrder (K := K) r hr.ne_zero).conductor := by
  by_contra h
  rw [Ideal.dvd_iff_le, IsConcreteLE.not_le_iff_exists] at h
  obtain ⟨t, ht, ht𝔯⟩ := h
  have hle : ¬ 𝔯'.asIdeal ≤ 𝔯.asIdeal := fun hle =>
    hne (HeightOneSpectrum.ext (𝔯'.isMaximal.eq_of_le 𝔯.isPrime.ne_top hle)).symm
  obtain ⟨y, hy, hy𝔯⟩ := IsConcreteLE.not_le_iff_exists.mp hle
  have hspan : Ideal.span {t} ≤ (ringClassOrder (K := K) r hr.ne_zero).conductor := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact ht
  have hu := (le_conductor_iff _ _).mp hspan (t * y)
    (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self t))
  obtain ⟨a, ha⟩ := (mem_ringClassOrder_iff r hr.ne_zero (t * y)).mp hu
  have hr𝔯 := natCast_mem_left hsplit
  have hr𝔯' := natCast_mem_right hsplit
  have hspan𝔯 : Ideal.span {(r : 𝓞 K)} ≤ 𝔯.asIdeal := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hr𝔯
  have hspan𝔯' : Ideal.span {(r : 𝓞 K)} ≤ 𝔯'.asIdeal := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hr𝔯'
  have ha' : (a : 𝓞 K) ∈ 𝔯'.asIdeal := by
    have h1 : t * y - (t * y - (a : 𝓞 K)) = (a : 𝓞 K) := by ring
    rw [← h1]
    exact 𝔯'.asIdeal.sub_mem (𝔯'.asIdeal.mul_mem_left t hy) (hspan𝔯' ha)
  have ha𝔯 : (a : 𝓞 K) ∈ 𝔯.asIdeal := by
    rw [intCast_mem_iff_natAbs, natCast_mem_iff_dvd hr 𝔯 hr𝔯] at ⊢
    rw [intCast_mem_iff_natAbs, natCast_mem_iff_dvd hr 𝔯' hr𝔯'] at ha'
    exact ha'
  have hty : t * y ∈ 𝔯.asIdeal := by
    have h1 : (t * y - (a : 𝓞 K)) + (a : 𝓞 K) = t * y := by ring
    rw [← h1]
    exact 𝔯.asIdeal.add_mem (hspan𝔯 ha) ha𝔯
  rcases 𝔯.isPrime.mem_or_mem hty with h | h
  · exact ht𝔯 h
  · exact hy𝔯 h

include hr in
/-- The principal ray class of a natural number prime to `r` dies in `Pic(ℤ + r𝒪_K)`: its ideal
is generated by an element of the order. Kind: PROVED. -/
theorem rayClassToPic_principalRayClass_natCast (c : ℕ) (hc : ¬ r ∣ c) (hc0 : (c : K) ≠ 0)
    (hx : Units.mk0 (c : K) hc0 ∈
      primeToSubgroup (ringClassOrder (K := K) r hr.ne_zero).conductorModulus) :
    (ringClassOrder (K := K) r hr.ne_zero).rayClassToPic
      (principalRayClass _ ⟨Units.mk0 (c : K) hc0, hx⟩) = 1 := by
  have hJ : Ideal.span {(c : 𝓞 K)} ∈
      integralIdealsPrimeTo (ringClassOrder (K := K) r hr.ne_zero).conductorModulus := by
    rw [mem_integralIdealsPrimeTo_conductorModulus_iff]
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.span_singleton_eq_bot]
      intro h
      apply hc0
      rw [← map_natCast (algebraMap (𝓞 K) K), h, map_zero]
    · obtain ⟨a, b, hab⟩ := exists_bezout (K := K) hr c hc
      rw [Ideal.eq_top_iff_one, ← hab, add_comm]
      exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
        (span_le_conductor_ringClassOrder r hr.ne_zero
          (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
  have heq : principalRayClass _ ⟨Units.mk0 (c : K) hc0, hx⟩ =
      idealClass (ringClassOrder (K := K) r hr.ne_zero).conductorModulus ⟨_, hJ⟩ := by
    rw [principalRayClass_apply, idealClass_apply]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [NumberFieldArithmetic.coe_principalIdealAway, NumberFieldArithmetic.coe_integralIdealsAwayHom]
    rw [coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton, Units.val_mk0,
      map_natCast (algebraMap (𝓞 K) K)]
  rw [heq, rayClassToPic_idealClass, picClass_eq_one_iff]
  exact ⟨(c : 𝓞 K), Subalgebra.natCast_mem _ c, rfl⟩

include hr hsplit hne in
/-- **Moving a unit from `𝔯'` to `𝔯`** (tex 3679–3681, "`(a, 1) ≡ (1, a⁻¹)` modulo the
diagonal"): the Picard class of a local unit `w` at `𝔯'` is the Picard class of a local unit at
`𝔯`. Approximate `w` by a natural number `c` modulo `𝔯'` (the residue field at `𝔯'` is `𝐅_r`); then
`w / c` is congruent to one at `𝔯'`, and the principal ideal `(c)`, generated by an element of
`ℤ + r𝒪_K`, gives `[c at 𝔯'] = [c⁻¹ at 𝔯]`. Kind: PROVED. -/
theorem exists_unitPic_eq (hK : Module.finrank ℚ K = 2) (w : (𝔯'.adicCompletion K)ˣ)
    (hw : Valued.v (w : 𝔯'.adicCompletion K) = 1) :
    ∃ c : Kˣ, 𝔯.valuation K (c : K) = 1 ∧
      unitPic r hr.ne_zero 𝔯' w = unitPic r hr.ne_zero 𝔯 (locUnit 𝔯 c)⁻¹ := by
  have hr𝔯 := natCast_mem_left hsplit
  have hr𝔯' := natCast_mem_right hsplit
  -- approximate `w` by an integer of `K`, then by a natural number
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valued_sub_le (K := K) 𝔯'
    ⟨(w : 𝔯'.adicCompletion K), (HeightOneSpectrum.mem_adicCompletionIntegers _ K 𝔯').mpr hw.le⟩ 1
  obtain ⟨c, hc⟩ := exists_natCast_eq_mk hr hsplit hK (Ideal.Quotient.mk 𝔯'.asIdeal a)
  have hac : a - (c : 𝓞 K) ∈ 𝔯'.asIdeal := Ideal.Quotient.eq.mp hc.symm
  have hac' : Valued.v (algebraMap (𝓞 K) (𝔯'.adicCompletion K) (a - (c : 𝓞 K))) ≤
      WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [valued_algebraMap_intValuation, HeightOneSpectrum.intValuation_le_pow_iff_dvd,
      pow_one, Ideal.dvd_span_singleton]
    exact hac
  have hwc : Valued.v ((w : 𝔯'.adicCompletion K) - (c : 𝔯'.adicCompletion K)) ≤
      WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have h1 : (w : 𝔯'.adicCompletion K) - (c : 𝔯'.adicCompletion K) =
        ((w : 𝔯'.adicCompletion K) - algebraMap (𝓞 K) (𝔯'.adicCompletion K) a) +
          algebraMap (𝓞 K) (𝔯'.adicCompletion K) (a - (c : 𝓞 K)) := by
      rw [map_sub, map_natCast]
      ring
    rw [h1]
    exact Valuation.map_add_le _ ha hac'
  have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hc𝔯' : (c : 𝓞 K) ∉ 𝔯'.asIdeal := by
    intro hmem
    have hcv : Valued.v (c : 𝔯'.adicCompletion K) < 1 := by
      rw [← map_natCast (algebraMap (𝓞 K) (𝔯'.adicCompletion K)),
        valued_algebraMap_intValuation, HeightOneSpectrum.intValuation_lt_one_iff_mem]
      exact hmem
    have hw1 : Valued.v (w : 𝔯'.adicCompletion K) < 1 := by
      have h1 : (w : 𝔯'.adicCompletion K) =
          ((w : 𝔯'.adicCompletion K) - (c : 𝔯'.adicCompletion K)) + (c : 𝔯'.adicCompletion K) := by
        ring
      rw [h1]
      exact Valuation.map_add_lt _ (hwc.trans_lt hlt) hcv
    rw [hw] at hw1
    exact lt_irrefl _ hw1
  have hc𝔯 : (c : 𝓞 K) ∉ 𝔯.asIdeal := fun h =>
    hc𝔯' ((natCast_mem_iff_dvd hr 𝔯' hr𝔯' c).mpr ((natCast_mem_iff_dvd hr 𝔯 hr𝔯 c).mp h))
  have hdvd : ¬ r ∣ c := fun h => hc𝔯' ((natCast_mem_iff_dvd hr 𝔯' hr𝔯' c).mpr h)
  have hc0 : (c : K) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    rintro rfl
    exact hc𝔯' (by simp)
  set cu : Kˣ := Units.mk0 (c : K) hc0 with hcu
  have hval : ∀ v : HeightOneSpectrum (𝓞 K), (c : 𝓞 K) ∉ v.asIdeal →
      v.valuation K ((cu : Kˣ) : K) = 1 := by
    intro v hv
    rw [hcu, Units.val_mk0, ← map_natCast (algebraMap (𝓞 K) K),
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hv
  have hv𝔯 := hval 𝔯 hc𝔯
  have hv𝔯' := hval 𝔯' hc𝔯'
  have hsupp : ∀ v : HeightOneSpectrum (𝓞 K),
      v.asIdeal ∣ (ringClassOrder (K := K) r hr.ne_zero).conductorModulus.finitePart →
        v = 𝔯 ∨ v = 𝔯' := fun v hv =>
    eq_or_eq_of_natCast_mem hsplit v (mem_of_dvd_conductor_ringClassOrder r hr.ne_zero v hv)
  have hx : cu ∈ primeToSubgroup (ringClassOrder (K := K) r hr.ne_zero).conductorModulus := by
    rw [mem_primeToSubgroup]
    intro v hv
    rcases hsupp v hv with rfl | rfl
    · exact hv𝔯
    · exact hv𝔯'
  have hloc : ((locUnit 𝔯' cu : (𝔯'.adicCompletion K)ˣ) : 𝔯'.adicCompletion K) =
      (c : 𝔯'.adicCompletion K) := by
    rw [Units.coe_map, hcu, Units.val_mk0]
    simp
  have hcne : (c : 𝔯'.adicCompletion K) ≠ 0 := hloc ▸ Units.ne_zero _
  have hcv : Valued.v (c : 𝔯'.adicCompletion K) = 1 := by
    rw [← hloc, valued_locUnit, hv𝔯']
  -- `w / c` is congruent to one at `𝔯'`
  have h1 : unitPic r hr.ne_zero 𝔯' w = unitPic r hr.ne_zero 𝔯' (locUnit 𝔯' cu) := by
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, unitPic, MonoidHom.comp_apply,
      ringClassIdeleQuotient_apply, rayClassQuotient_ofAdicCompletion_eq_one, map_one]
    · rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, valued_locUnit, hw, hv𝔯',
        inv_one, mul_one]
    · have h2 : ((w * (locUnit 𝔯' cu)⁻¹ : (𝔯'.adicCompletion K)ˣ) : 𝔯'.adicCompletion K) - 1 =
          ((w : 𝔯'.adicCompletion K) - (c : 𝔯'.adicCompletion K)) *
            (c : 𝔯'.adicCompletion K)⁻¹ := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, hloc]
        field_simp
      rw [h2, map_mul, map_inv₀, hcv, inv_one, mul_one]
      refine hwc.trans (WithZero.exp_le_exp.mpr ?_)
      have := exponent_conductorModulus_le_one hsplit hr.ne_zero hne
      omega
  -- the principal ideal `(c)` relates the two places
  have hP := principalRayClass_eq_rayClassQuotient _ (conductorModulus_infinitePart _) hne hsupp
    ⟨cu, hx⟩ hv𝔯 hv𝔯'
  have hK1 : (ringClassOrder (K := K) r hr.ne_zero).rayClassToPic
      (principalRayClass _ ⟨cu, hx⟩) = 1 :=
    rayClassToPic_principalRayClass_natCast hr c hdvd hc0 hx
  rw [hP, ← ringClassIdeleQuotient_apply, map_mul] at hK1
  refine ⟨cu, hv𝔯, h1.trans ?_⟩
  have h3 : unitPic r hr.ne_zero 𝔯 (locUnit 𝔯 cu)⁻¹ *
      (unitPic r hr.ne_zero 𝔯' (locUnit 𝔯' cu))⁻¹ = 1 := by
    rw [← map_inv (unitPic r hr.ne_zero 𝔯') (locUnit 𝔯' cu)]
    exact hK1
  exact (mul_inv_eq_one.mp h3).symm

include hr hsplit hne in
/-- **The kernel of `Gal(H_r/K) → Cl(K)` lies in the inertia group at `𝔯`** (tex 3679–3681). By
exactness the kernel is the image of the residue units: the principal ray class of an element `x`
prime to `r`, which is the class of the local idele `(x⁻¹ at 𝔯, x⁻¹ at 𝔯')`. The component at `𝔯'`
moves to `𝔯` (`exists_unitPic_eq`), so the class is that of a local unit at `𝔯`, whose Artin
symbol lies in inertia (`inertiaGal_eq_map_unitArtin`). Kind: PROVED. -/
theorem ker_galToClassGroup_le_inertiaGal (hK : Module.finrank ℚ K = 2)
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (r : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (galToClassGroup r hr.ne_zero S hS).ker ≤ inertiaGal r hr.ne_zero S hS 𝔯 := by
  rw [ker_galToClassGroup, inertiaGal_eq_map_unitArtin]
  rintro _ ⟨a, rfl⟩
  obtain ⟨x, hx⟩ := residueSignHom_surjective
    (ringClassOrder (K := K) r hr.ne_zero).conductorModulus (MonoidHom.inl _ _ a)
  have hsupp : ∀ v : HeightOneSpectrum (𝓞 K),
      v.asIdeal ∣ (ringClassOrder (K := K) r hr.ne_zero).conductorModulus.finitePart →
        v = 𝔯 ∨ v = 𝔯' := fun v hv =>
    eq_or_eq_of_natCast_mem hsplit v (mem_of_dvd_conductor_ringClassOrder r hr.ne_zero v hv)
  have hd𝔯 := dvd_conductor_ringClassOrder_left hr hsplit hne
  have hd𝔯' := dvd_conductor_ringClassOrder_left hr (𝔯 := 𝔯') (𝔯' := 𝔯)
    (by rw [hsplit, mul_comm]) hne.symm
  have hx𝔯 : 𝔯.valuation K ((x : Kˣ) : K) = 1 := mem_primeToSubgroup.mp x.2 𝔯 hd𝔯
  have hx𝔯' : 𝔯'.valuation K ((x : Kˣ) : K) = 1 := mem_primeToSubgroup.mp x.2 𝔯' hd𝔯'
  have hP := principalRayClass_eq_rayClassQuotient _ (conductorModulus_infinitePart _) hne hsupp
    x hx𝔯 hx𝔯'
  have hres : residuePic (ringClassOrder (K := K) r hr.ne_zero) a =
      unitPic r hr.ne_zero 𝔯 (locUnit 𝔯 (x : Kˣ))⁻¹ *
        unitPic r hr.ne_zero 𝔯' (locUnit 𝔯' (x : Kˣ))⁻¹ := by
    have h0 : residuePic (ringClassOrder (K := K) r hr.ne_zero) a =
        (ringClassOrder (K := K) r hr.ne_zero).rayClassToPic
          (residueSignRayClass _ (residueSignHom _ x)) := by
      rw [hx]
      rfl
    rw [h0, residueSignRayClass_residueSignHom, hP, ← ringClassIdeleQuotient_apply, map_mul]
    rfl
  have hw : Valued.v (((locUnit 𝔯' (x : Kˣ))⁻¹ : (𝔯'.adicCompletion K)ˣ) :
      𝔯'.adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, valued_locUnit, hx𝔯', inv_one]
  obtain ⟨c, hc, hcw⟩ := exists_unitPic_eq hr hsplit hne hK _ hw
  refine ⟨(locUnit 𝔯 (x : Kˣ))⁻¹ * (locUnit 𝔯 c)⁻¹,
    (HeightOneSpectrum.mem_unitFiltration_zero_adicCompletion_iff 𝔯).mpr ?_, ?_⟩
  · rw [Units.val_mul, map_mul,
      Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, map_inv₀, valued_locUnit,
      valued_locUnit, hx𝔯, hc, inv_one, mul_one]
  · change ringClassPicEquiv r hr.ne_zero S hS (unitPic r hr.ne_zero 𝔯 _) =
      ringClassPicEquiv r hr.ne_zero S hS (residuePic (ringClassOrder (K := K) r hr.ne_zero) a)
    rw [hres, hcw, map_mul]

end Main

end ZInQ.Contrib.CloudB3E1RingClass
