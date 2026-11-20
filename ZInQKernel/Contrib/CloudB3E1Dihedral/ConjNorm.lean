import ZInQKernel.Contrib.CloudB3E1RingClass.Conjugation
import ZInQKernel.Contrib.CloudB3E1RingClass.Decomposition

/-!
# `𝔭 · κ(𝔭) = (N𝔭)` in a quadratic field, and conjugate Artin classes

Manuscript `diophantine_zq.tex`, tex 2778–2795 (the conjugation inverts the ring-class
characters) and tex 3683–3684 ("`𝔭_j 𝔭̄_j = (p)` is rational principal, so `qbar = −q`").

Let `K` be a quadratic field and `σ` the nontrivial element of `Gal(K/ℚ)`.
* **`mul_smul_eq_span_absNorm`** (PROVED): every nonzero prime `𝔭` of `𝒪_K` satisfies
  `𝔭 · σ𝔭 = (N𝔭)`. There are three cases. If `σ𝔭 ≠ 𝔭`, the prime is split: `𝔭 σ𝔭 ∣ (p)`, and the
  norms force equality. If `σ𝔭 = 𝔭 = (p)`, it is inert. If `σ𝔭 = 𝔭 ≠ (p)`, it is ramified:
  `(p) = 𝔭²`, since every prime over `p` is `𝔭`. In each case the norm is read off.
* `ringEquivAlg κ`: a ring automorphism of `K` as an element of `Gal(K/ℚ)`;
  `map_mapRingEquiv_eq_smul`: `κ(J) = κ • J` on ideals of `𝒪_K`.
* `conjPlaceOf κ v`: the conjugate place `κ(v)`; `natCast_mem_conjPlaceOf`: it contains the same
  integers.
* **`artinClass_conjPlace`** (PROVED): for `κ ≠ 1` and a place `v ∤ f`,
  `Art(κ v) = Art(v)⁻¹` in `Gal(H_f/K)`. This holds for every such place (split, inert or
  ramified), not only for split pairs.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1Dihedral

open NumberField IsDedekindDomain Ideal
open ZInQ.Contrib.CloudB3E1RingClass
open scoped Pointwise

variable {K : Type} [Field K] [NumberField K]

/-! ### The norm of a prime and its conjugate -/

section Norm

variable (hK : Module.finrank ℚ K = 2) {σ : K ≃ₐ[ℚ] K}
  (hσ : ∀ τ : K ≃ₐ[ℚ] K, τ ≠ 1 → τ = σ)

include hK in
/-- `N(p) = p²` for an integer `p` in a quadratic field. Kind: PROVED. -/
theorem absNorm_span_intCast (p : ℤ) :
    absNorm (span {((p : ℤ) : 𝓞 K)}) = p.natAbs ^ 2 := by
  rw [absNorm_span_singleton]
  have h : Algebra.norm ℤ ((p : ℤ) : 𝓞 K) = p ^ 2 := by
    rw [show ((p : ℤ) : 𝓞 K) = algebraMap ℤ (𝓞 K) p from (eq_intCast _ p).symm,
      Algebra.norm_algebraMap, RingOfIntegers.rank, hK]
  rw [h, Int.natAbs_pow]

omit [NumberField K] in
/-- `span {(|p| : 𝒪_K)} = span {(p : 𝒪_K)}`. Kind: PROVED. -/
theorem span_natAbs (p : ℤ) :
    span {((p.natAbs : ℕ) : 𝓞 K)} = span {((p : ℤ) : 𝓞 K)} := by
  rcases Int.natAbs_eq p with h | h
  · conv_rhs => rw [h]
    simp
  · conv_rhs => rw [h]
    rw [Int.cast_neg, ← Ideal.span_singleton_neg]
    simp

include hK hσ in
/-- **Every prime over `p` is `𝔭` or `σ𝔭`.** Kind: PROVED. -/
theorem eq_or_eq_smul_of_liesOver (P Q : Ideal (𝓞 K)) [P.IsPrime] [Q.IsPrime] (p : ℤ)
    [P.LiesOver (span {p})] [Q.LiesOver (span {p})] : Q = P ∨ Q = σ • P := by
  have := isGalois_of_finrank_two hK
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (span {p}) P Q (K ≃ₐ[ℚ] K)
  by_cases h1 : τ = 1
  · left; rw [← hτ, h1, one_smul]
  · right; rw [← hτ, hσ τ h1]

/-- `N(σ𝔭) = N𝔭`. Kind: PROVED. -/
theorem absNorm_smul (τ : K ≃ₐ[ℚ] K) (I : Ideal (𝓞 K)) : absNorm (τ • I) = absNorm I := by
  rw [← absNorm_relNorm ℤ (𝓞 K) (τ • I), relNorm_smul, absNorm_relNorm]

include hK hσ in
/-- **`𝔭 · σ𝔭 = (N𝔭)`** for every nonzero prime `𝔭` of a quadratic field (tex 3683–3684).
Kind: PROVED. -/
theorem mul_smul_eq_span_absNorm (P : Ideal (𝓞 K)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) :
    P * (σ • P) = span {((absNorm P : ℕ) : 𝓞 K)} := by
  have hPmax : P.IsMaximal := hP.isMaximal hP0
  set p : ℤ := (absNorm (under ℤ P) : ℤ) with hp
  have : P.LiesOver (span {p}) := Int.liesOver_span_absNorm P
  have hpP : ((p : ℤ) : 𝓞 K) ∈ P := by
    rw [hp, Int.cast_natCast]; exact Int.absNorm_under_mem P
  -- `N𝔭 = |p|^f`, `f ≥ 1`
  have hNf : p.natAbs ^ P.inertiaDeg ℤ = absNorm P := natAbs_pow_inertiaDeg p P
  have hf : 0 < P.inertiaDeg ℤ := inertiaDeg_pos P ℤ
  have hp1 : 1 < p.natAbs := by
    have hP1 : absNorm P ≠ 1 := fun h => hP.ne_top (absNorm_eq_one_iff.mp h)
    have hP0' : absNorm P ≠ 0 := by
      rw [Ne, absNorm_eq_zero_iff]; exact hP0
    rcases Nat.lt_or_ge 1 p.natAbs with h | h
    · exact h
    · exfalso
      rcases (show p.natAbs = 0 ∨ p.natAbs = 1 by omega) with h0 | h1
      · rw [h0, zero_pow hf.ne'] at hNf; exact hP0' hNf.symm
      · rw [h1, one_pow] at hNf; exact hP1 hNf.symm
  have hspan : span {((p : ℤ) : 𝓞 K)} ≤ P := by
    rw [span_le, Set.singleton_subset_iff]; exact hpP
  -- `N𝔭² ∣ p²` forces `f = 1`
  have hf1 : ∀ J : Ideal (𝓞 K), span {((p : ℤ) : 𝓞 K)} = P * (σ • P) * J →
      P.inertiaDeg ℤ = 1 ∧ J = ⊤ := by
    intro J hJ
    have h := congrArg absNorm hJ
    rw [absNorm_span_intCast hK, map_mul, map_mul, absNorm_smul, ← hNf, ← pow_add] at h
    have hle : p.natAbs ^ (P.inertiaDeg ℤ + P.inertiaDeg ℤ) ∣ p.natAbs ^ 2 := ⟨absNorm J, h⟩
    have h2 := (Nat.pow_dvd_pow_iff_le_right hp1).mp hle
    have hf' : P.inertiaDeg ℤ = 1 := by omega
    refine ⟨hf', ?_⟩
    rw [hf'] at h
    have hJ1 : absNorm J = 1 := by
      have hpos : 0 < p.natAbs ^ 2 := by positivity
      have : p.natAbs ^ 2 * 1 = p.natAbs ^ 2 * absNorm J := by
        rw [mul_one]; exact h
      exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
    exact absNorm_eq_one_iff.mp hJ1
  have hNp : P.inertiaDeg ℤ = 1 → ((absNorm P : ℕ) : 𝓞 K) = ((p.natAbs : ℕ) : 𝓞 K) := by
    intro h; rw [← hNf, h, pow_one]
  have hσP : (σ • P).IsPrime := Ideal.IsPrime.smul σ
  have hσPmax : (σ • P).IsMaximal := hσP.isMaximal (by
    intro h; apply hP0
    have := congrArg (fun I => σ⁻¹ • I) h
    simpa using this)
  by_cases hs : σ • P = P
  · -- inert or ramified
    rw [hs]
    by_cases hin : P = span {((p : ℤ) : 𝓞 K)}
    · have hN : absNorm P = p.natAbs ^ 2 := by rw [hin, absNorm_span_intCast hK]
      rw [hN, Nat.cast_pow, ← Ideal.span_singleton_pow, span_natAbs, ← hin, sq]
    · obtain ⟨J, hJ⟩ := (Ideal.dvd_iff_le).mpr hspan
      have hJt : J ≠ ⊤ := by
        rintro rfl; rw [mul_top] at hJ; exact hin hJ.symm
      obtain ⟨Q, hQ, hJQ⟩ := Ideal.exists_le_maximal J hJt
      have hpQ : ((p : ℤ) : 𝓞 K) ∈ Q := by
        have hm : ((p : ℤ) : 𝓞 K) ∈ span {((p : ℤ) : 𝓞 K)} := Ideal.mem_span_singleton_self _
        rw [hJ] at hm
        exact hJQ (Ideal.mul_le_right (I := P) (J := J) hm)
      have : Q.LiesOver (span {p}) := by
        refine ⟨?_⟩
        have hmax : (span {p} : Ideal ℤ).IsMaximal := by
          rw [hp, Int.ideal_span_absNorm_eq_self]; exact Ideal.IsMaximal.under ℤ P
        refine (hmax.eq_of_le (Ideal.IsPrime.comap _).ne_top ?_)
        rw [span_le, Set.singleton_subset_iff]
        change algebraMap ℤ (𝓞 K) p ∈ Q
        simpa using hpQ
      have hQP : Q = P := by
        rcases eq_or_eq_smul_of_liesOver hK hσ P Q p with h | h
        · exact h
        · rw [h, hs]
      rw [hQP] at hJQ
      obtain ⟨J', hJ'⟩ := (Ideal.dvd_iff_le).mpr hJQ
      have h2 : span {((p : ℤ) : 𝓞 K)} = P * (σ • P) * J' := by
        rw [hs, hJ, hJ', mul_assoc]
      obtain ⟨hf', hJ't⟩ := hf1 J' h2
      rw [hNp hf', span_natAbs, h2, hJ't, mul_top, hs]
  · -- split
    obtain ⟨J, hJ⟩ := (Ideal.dvd_iff_le).mpr hspan
    have hσle : span {((p : ℤ) : 𝓞 K)} ≤ σ • P := by
      rw [span_le, Set.singleton_subset_iff]
      have h := Ideal.smul_mem_pointwise_smul σ _ P hpP
      rwa [show σ • ((p : ℤ) : 𝓞 K) = ((p : ℤ) : 𝓞 K) from
        map_intCast (MulSemiringAction.toRingHom (K ≃ₐ[ℚ] K) (𝓞 K) σ) p] at h
    have hPnle : ¬ P ≤ σ • P := fun h => hs (hPmax.eq_of_le hσP.ne_top h).symm
    have hJσ : J ≤ σ • P := by
      have hm : P * J ≤ σ • P := by rw [← hJ]; exact hσle
      rcases (Ideal.IsPrime.mul_le hσP).mp hm with h | h
      · exact absurd h hPnle
      · exact h
    obtain ⟨J', hJ'⟩ := (Ideal.dvd_iff_le).mpr hJσ
    have h2 : span {((p : ℤ) : 𝓞 K)} = P * (σ • P) * J' := by rw [hJ, hJ', mul_assoc]
    obtain ⟨hf', hJ't⟩ := hf1 J' h2
    rw [hNp hf', span_natAbs, h2, hJ't, mul_top]

end Norm

/-! ### Ring automorphisms and conjugate places -/

/-- A ring automorphism of `K` as an element of `Gal(K/ℚ)`. Kind: definition. -/
def ringEquivAlg (κ : K ≃+* K) : K ≃ₐ[ℚ] K :=
  AlgEquiv.ofRingEquiv (f := κ) fun q => by simp

theorem ringEquivAlg_apply (κ : K ≃+* K) (x : K) : ringEquivAlg κ x = κ x := rfl

/-- **`κ(J) = κ • J`** on ideals of `𝒪_K`. Kind: PROVED. -/
theorem map_mapRingEquiv_eq_smul (κ : K ≃+* K) (J : Ideal (𝓞 K)) :
    J.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) = ringEquivAlg κ • J := by
  rw [Ideal.pointwise_smul_def]
  congr 1

/-- **The conjugate place `κ(v)`.** Kind: definition. -/
def conjPlaceOf (κ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K)
  isPrime := by rw [map_mapRingEquiv_eq_smul]; exact Ideal.IsPrime.smul _
  ne_bot := fun h =>
    v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv κ).injective).mp h)

theorem conjPlaceOf_asIdeal (κ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) :
    (conjPlaceOf κ v).asIdeal = ringEquivAlg κ • v.asIdeal :=
  map_mapRingEquiv_eq_smul κ v.asIdeal

/-- `κ(v)` contains the same integers as `v`. Kind: PROVED. -/
theorem natCast_mem_conjPlaceOf (κ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    ((n : ℕ) : 𝓞 K) ∈ (conjPlaceOf κ v).asIdeal ↔ ((n : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have e : ∀ g : K ≃ₐ[ℚ] K, g • ((n : ℕ) : 𝓞 K) = n := fun g =>
    map_natCast (MulSemiringAction.toRingHom (K ≃ₐ[ℚ] K) (𝓞 K) g) n
  rw [conjPlaceOf_asIdeal]
  constructor
  · intro h
    have := Ideal.smul_mem_pointwise_smul (ringEquivAlg κ)⁻¹ _ _ h
    rwa [e, inv_smul_smul] at this
  · intro h
    have := Ideal.smul_mem_pointwise_smul (ringEquivAlg κ) _ _ h
    rwa [e] at this

/-! ### Conjugate Artin classes -/

variable (f : ℕ) (hf : f ≠ 0) (S : Set (HeightOneSpectrum (𝓞 K)))
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ S)

/-- **`Art(κ v) = Art(v)⁻¹`** for every place `v ∤ f` of a quadratic field, `κ ≠ 1`
(tex 2778–2795, 3683–3684). Kind: PROVED. -/
theorem artinClass_conjPlace (hK : Module.finrank ℚ K = 2) (κ : K ≃+* K)
    (hκ : ringEquivAlg κ ≠ 1) (v : HeightOneSpectrum (𝓞 K)) (hv : (f : 𝓞 K) ∉ v.asIdeal) :
    artinClass f hf S hS (primeToIdeal f hf (conjPlaceOf κ v)
        (fun h => hv ((natCast_mem_conjPlaceOf κ v f).mp h))) =
      (artinClass f hf S hS (primeToIdeal f hf v hv))⁻¹ := by
  obtain ⟨σ, -, hσ⟩ := exists_conj hK
  have hκσ : ringEquivAlg κ = σ := hσ _ hκ
  refine eq_inv_of_mul_eq_one_right (artinClass_mul_eq_one f hf S hS _ _
    ((absNorm v.asIdeal : ℕ) : ℤ) ?_)
  change v.asIdeal * (conjPlaceOf κ v).asIdeal = _
  rw [conjPlaceOf_asIdeal, hκσ, mul_smul_eq_span_absNorm hK hσ v.asIdeal v.ne_bot]
  simp

end ZInQ.Contrib.CloudB3E1Dihedral
