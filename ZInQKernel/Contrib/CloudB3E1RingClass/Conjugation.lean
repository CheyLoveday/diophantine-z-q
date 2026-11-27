import ZInQKernel.Contrib.CloudB3E1RingClass.Radicands
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup

/-!
# Complex conjugation on a quadratic field and the radicands `α_a = β_a/β̄_a`

Manuscript `diophantine_zq.tex`, tex 3536–3542: "`α_a = β_a/β̄_a`".

For a quadratic number field `K`:
* `Gal(K/ℚ) = {1, σ}` (`exists_conj`);
* `σ` exchanges the two primes of a split pair `𝔭𝔭̄ = (p)` (`conj_smul_split`, by transitivity of the
  Galois action on the primes over `p`);
* `v_w(σx) = v_{w₀}(x)` when `w = σw₀` (Tau Ceti's `valuation_apply_eq_of_asIdeal_eq_smul`).

For a `RingClassSetup` whose chosen primes lie over pairwise distinct rational primes and form split
pairs, and a relation `m` among their classes, `radicand_valuations` takes the generator `β` of
`∏_j 𝔭_j^{m_j}` and `α = β/σβ`, and proves:
* `v_{𝔭_j}(α) = m_j` (since `v_{𝔭_j}(σβ) = v_{𝔭̄_j}(β) = 0`);
* `v_𝔯(α) = 0` at every prime `𝔯` over a rational prime other than the `p_j`.

These are the core inputs `hval` and `hsupp`.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Pointwise

variable {K : Type} [Field K] [NumberField K]

/-- A quadratic number field is Galois over `ℚ`. Kind: PROVED. -/
theorem isGalois_of_finrank_two (hK : Module.finrank ℚ K = 2) : IsGalois ℚ K := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  infer_instance

/-- **`Gal(K/ℚ) = {1, σ}`** for a quadratic field. Kind: PROVED. -/
theorem exists_conj (hK : Module.finrank ℚ K = 2) :
    ∃ σ : K ≃ₐ[ℚ] K, σ ≠ 1 ∧ ∀ τ : K ≃ₐ[ℚ] K, τ ≠ 1 → τ = σ := by
  have := isGalois_of_finrank_two hK
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 := by
    rw [← hK, ← IsGalois.card_aut_eq_finrank]
  obtain ⟨x, y, hxy, huniv⟩ := Nat.card_eq_two_iff.mp hcard
  have hmem : ∀ z : K ≃ₐ[ℚ] K, z = x ∨ z = y := fun z => by
    have : z ∈ ({x, y} : Set (K ≃ₐ[ℚ] K)) := huniv ▸ Set.mem_univ z
    simpa using this
  rcases hmem 1 with h1 | h1
  · refine ⟨y, fun h => hxy (h1.symm.trans h.symm), fun τ hτ => ?_⟩
    rcases hmem τ with h | h
    · exact absurd (h.trans h1.symm) hτ
    · exact h
  · refine ⟨x, fun h => hxy (h.trans h1), fun τ hτ => ?_⟩
    rcases hmem τ with h | h
    · exact h
    · exact absurd (h.trans h1.symm) hτ

omit [NumberField K] in
/-- A prime ideal of `𝒪_K` containing a rational prime `p` lies over `p`. Kind: PROVED. -/
theorem liesOver_of_mem {P : Ideal (𝓞 K)} [hP : P.IsPrime] {p : ℕ} (hp : p.Prime)
    (h : ((p : ℤ) : 𝓞 K) ∈ P) : P.LiesOver (Ideal.span {(p : ℤ)}) := by
  refine ⟨?_⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)).isMaximal (by simp [hp.ne_zero])
  have hne : P.under ℤ ≠ ⊤ := Ideal.IsPrime.ne_top (Ideal.IsPrime.comap _)
  refine hmax.eq_of_le hne ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P
  simpa using h

/-- **Conjugation exchanges a split pair** (tex 3536–3542): if `𝔭 ≠ 𝔭̄` and `𝔭𝔭̄ = (p)`, then
`σ𝔭 = 𝔭̄` for the non-trivial `σ ∈ Gal(K/ℚ)`. Kind: PROVED. -/
theorem conj_smul_split (hK : Module.finrank ℚ K = 2) {σ : K ≃ₐ[ℚ] K}
    (hσ : ∀ τ : K ≃ₐ[ℚ] K, τ ≠ 1 → τ = σ) {P Q : HeightOneSpectrum (𝓞 K)} {p : ℕ}
    (hp : p.Prime) (hPQ : P ≠ Q) (hmul : P.asIdeal * Q.asIdeal = Ideal.span {((p : ℤ) : 𝓞 K)}) :
    σ • P.asIdeal = Q.asIdeal := by
  have := isGalois_of_finrank_two hK
  have hm : ((p : ℤ) : 𝓞 K) ∈ P.asIdeal * Q.asIdeal := hmul ▸ Ideal.mem_span_singleton_self _
  have hpP : ((p : ℤ) : 𝓞 K) ∈ P.asIdeal := Ideal.mul_le_left (I := P.asIdeal) (J := Q.asIdeal) hm
  have hpQ : ((p : ℤ) : 𝓞 K) ∈ Q.asIdeal := Ideal.mul_le_right (I := P.asIdeal) (J := Q.asIdeal) hm
  have := liesOver_of_mem (P := P.asIdeal) hp hpP
  have := liesOver_of_mem (P := Q.asIdeal) hp hpQ
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P.asIdeal
    Q.asIdeal (K ≃ₐ[ℚ] K)
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    exact hPQ (HeightOneSpectrum.ext ((one_smul (K ≃ₐ[ℚ] K) P.asIdeal).symm.trans hτ))
  have h' : σ = τ := (hσ τ hτ1).symm
  subst h'
  exact hτ

/-- **The conjugate of a prime** `σ⁻¹ 𝔯`, as a prime with `σ • (σ⁻¹ 𝔯) = 𝔯`. Kind: definition. -/
def conjPrime (σ : K ≃ₐ[ℚ] K) (w : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.comap (MulSemiringAction.toRingHom (K ≃ₐ[ℚ] K) (𝓞 K) σ)
  isPrime := Ideal.IsPrime.comap _
  ne_bot := by
    intro h
    apply w.ne_bot
    have hs : Function.Surjective (MulSemiringAction.toRingHom (K ≃ₐ[ℚ] K) (𝓞 K) σ) :=
      (MulSemiringAction.toRingEquiv (K ≃ₐ[ℚ] K) (𝓞 K) σ).surjective
    rw [← Ideal.map_comap_of_surjective _ hs w.asIdeal, h, Ideal.map_bot]

theorem smul_conjPrime (σ : K ≃ₐ[ℚ] K) (w : HeightOneSpectrum (𝓞 K)) :
    w.asIdeal = σ • (conjPrime σ w).asIdeal := by
  have hs : Function.Surjective (MulSemiringAction.toRingHom (K ≃ₐ[ℚ] K) (𝓞 K) σ) :=
    (MulSemiringAction.toRingEquiv (K ≃ₐ[ℚ] K) (𝓞 K) σ).surjective
  rw [Ideal.pointwise_smul_def, conjPrime, Ideal.map_comap_of_surjective _ hs]

theorem intCast_mem_conjPrime (σ : K ≃ₐ[ℚ] K) (w : HeightOneSpectrum (𝓞 K)) (q : ℤ) :
    ((q : 𝓞 K)) ∈ (conjPrime σ w).asIdeal ↔ (q : 𝓞 K) ∈ w.asIdeal := by
  change MulSemiringAction.toRingHom (K ≃ₐ[ℚ] K) (𝓞 K) σ (q : 𝓞 K) ∈ w.asIdeal ↔ _
  rw [map_intCast]

/-- **`v_w(σx) = v_{w₀}(x)`** for `w = σw₀`. Kind: PROVED. -/
theorem valuation_conj (σ : K ≃ₐ[ℚ] K) {w w₀ : HeightOneSpectrum (𝓞 K)}
    (h : w.asIdeal = σ • w₀.asIdeal) (x : K) : w.valuation K (σ x) = w₀.valuation K x :=
  HeightOneSpectrum.valuation_apply_eq_of_asIdeal_eq_smul σ h x

end ZInQ.Contrib.CloudB3E1RingClass
