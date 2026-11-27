import ZInQKernel.Contrib.CloudB3E1RingClass.Conjugation
import ZInQKernel.Contrib.CloudB3E1RingClass.DeltaWire

/-!
# The Kummer data from the relations: `hval` and `hsupp`

Manuscript `diophantine_zq.tex`, tex 3536–3542: "let `m^{(a)}` be a `ℤ`-basis of the relations, let
`(β_a) = ∏_j 𝔭_j^{m_j^{(a)}}` and `α_a = β_a/β̄_a ∈ K`; fix `2^n`-th roots `α_a^{1/2^n}` and a
primitive `2^n`-th root of unity `ζ`".

For `K = ℚ(s)` quadratic and a `RingClassSetup` whose primes lie over pairwise distinct rational
primes, with `𝔭_j ≠ 𝔭̄_j`:
* `radicand_valuations`: for a family of relations `m^{(a)}`, the radicands `α_a = β_a/σβ_a`
  satisfy `v_{𝔭_j}(α_a) = m_j^{(a)}`, and `v_𝔯(α_a) = 0` at every prime over a rational prime other
  than the `p_j`;
* `exists_kummerData`: the Kummer data `kd` with these radicands, with `hval` and `hsupp` in the
  form of `GenuineMovingCore`.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.TateWiring
open ZInQ.Contrib.ChebFD.C10 (Qbar)
open scoped nonZeroDivisors Pointwise

variable {s : Qbar} {S : ℕ}

theorem p_mem_𝔭 (C : RingClassSetup (quadField s) S) (j : Fin S) :
    ((max (C.p j) 1 : ℕ) : 𝓞 (quadField s)) ∈ (C.𝔭 j).asIdeal ∧
      ((max (C.p j) 1 : ℕ) : 𝓞 (quadField s)) ∈ (C.𝔭bar j).asIdeal := by
  have hm : (((C.p j : ℤ)) : 𝓞 (quadField s)) ∈ (C.𝔭 j).asIdeal * (C.𝔭bar j).asIdeal :=
    (C.𝔭_mul j) ▸ Ideal.mem_span_singleton_self _
  rw [max_eq_left (C.p_prime j).one_lt.le, ← Int.cast_natCast]
  exact ⟨Ideal.mul_le_left (I := (C.𝔭 j).asIdeal) (J := (C.𝔭bar j).asIdeal) hm,
    Ideal.mul_le_right (I := (C.𝔭 j).asIdeal) (J := (C.𝔭bar j).asIdeal) hm⟩

/-- With distinct rational primes, the chosen primes are pairwise distinct, and no conjugate
`𝔭̄_j` is a chosen prime. Kind: PROVED. -/
theorem 𝔭_injective_and_bar (C : RingClassSetup (quadField s) S) (hinj : Function.Injective C.p)
    (hne : ∀ j, C.𝔭 j ≠ C.𝔭bar j) :
    Function.Injective C.𝔭 ∧ ∀ j, C.𝔭bar j ∉ Set.range C.𝔭 := by
  refine ⟨fun j k hjk => ?_, fun j ⟨k, hk⟩ => ?_⟩
  · by_contra h
    have hp : C.p j ≠ C.p k := fun h' => h (hinj h')
    exact (not_mem_of_ne C k (C.p j) (C.p_prime j) hp).1 (hjk ▸ (p_mem_𝔭 C j).1)
  · by_cases h : k = j
    · subst h; exact hne k hk
    · have hp : C.p j ≠ C.p k := fun h' => h (hinj h').symm
      exact (not_mem_of_ne C k (C.p j) (C.p_prime j) hp).1 (hk ▸ (p_mem_𝔭 C j).2)

theorem not_mem_range_of_prime (C : RingClassSetup (quadField s) S) {q : ℕ} (hq : q.Prime)
    (hqp : ∀ j, q ≠ C.p j) {w : HeightOneSpectrum (𝓞 (quadField s))}
    (hw : ((q : ℤ) : 𝓞 (quadField s)) ∈ w.asIdeal) : w ∉ Set.range C.𝔭 := by
  rintro ⟨k, rfl⟩
  apply (not_mem_of_ne C k q hq (hqp k)).1
  rw [max_eq_left hq.one_lt.le, ← Int.cast_natCast]
  exact hw

/-- **The radicands and their valuations** (tex 3536–3542). Kind: PROVED. -/
theorem radicand_valuations (hK : Module.finrank ℚ (quadField s) = 2)
    (C : RingClassSetup (quadField s) S) (hinj : Function.Injective C.p)
    (hne : ∀ j, C.𝔭 j ≠ C.𝔭bar j) {t : ℕ} (m : Fin t → Fin S → ℤ)
    (hm : ∀ a, ∑ j, m a j • setupCls C j = 0) :
    ∃ α : Fin t → (quadField s)ˣ,
      (∀ j a, (C.𝔭 j).valuation (quadField s) (α a : quadField s) = WithZero.exp (-(m a j))) ∧
      ∀ a (𝔯 : HeightOneSpectrum (𝓞 (quadField s))) (q : ℕ), q.Prime → (∀ j, q ≠ C.p j) →
        ((q : ℤ) : 𝓞 (quadField s)) ∈ 𝔯.asIdeal →
          𝔯.valuation (quadField s) (α a : quadField s) = 1 := by
  obtain ⟨σ, -, hσ⟩ := exists_conj hK
  obtain ⟨hPinj, hbar⟩ := 𝔭_injective_and_bar C hinj hne
  have hβ : ∀ a, ∃ β : (quadField s)ˣ,
      toPrincipalIdeal (𝓞 (quadField s)) (quadField s) β = ∏ j, primeUnit (C.𝔭 j) ^ m a j :=
    fun a => exists_generator C.𝔭 (m a) (hm a)
  choose β hβ using hβ
  let α : Fin t → (quadField s)ˣ := fun a =>
    Units.mk0 ((β a : quadField s) / σ (β a : quadField s))
      (div_ne_zero (β a).ne_zero ((map_ne_zero σ).mpr (β a).ne_zero))
  have hval : ∀ a (w w₀ : HeightOneSpectrum (𝓞 (quadField s))), w.asIdeal = σ • w₀.asIdeal →
      w.valuation (quadField s) (α a : quadField s) =
        w.valuation (quadField s) (β a : quadField s) /
          w₀.valuation (quadField s) (β a : quadField s) := by
    intro a w w₀ h
    simp only [α, Units.val_mk0, map_div₀]
    rw [valuation_conj σ h]
  refine ⟨α, fun j a => ?_, fun a 𝔯 q hq hqp hq𝔯 => ?_⟩
  · have hsw : (C.𝔭 j).asIdeal = σ • (C.𝔭bar j).asIdeal :=
      (conj_smul_split hK hσ (C.p_prime j) (hne j).symm
        (by rw [mul_comm]; exact C.𝔭_mul j)).symm
    obtain ⟨h1, h2⟩ := valuation_generator_of_injective hPinj (m a) (β a) (hβ a)
    rw [hval a _ _ hsw, h1 j, h2 _ (hbar j), div_one]
  · obtain ⟨-, h2⟩ := valuation_generator_of_injective hPinj (m a) (β a) (hβ a)
    have hc : ((q : ℤ) : 𝓞 (quadField s)) ∈ (conjPrime σ 𝔯).asIdeal :=
      (intCast_mem_conjPrime σ 𝔯 q).mpr hq𝔯
    rw [hval a _ _ (smul_conjPrime σ 𝔯), h2 _ (not_mem_range_of_prime C hq hqp hq𝔯),
      h2 _ (not_mem_range_of_prime C hq hqp hc), div_one]

/-- **The Kummer data from the relations, with `hval` and `hsupp`** (tex 3536–3542): for any
`n`, Kummer data whose radicands are `α_a = β_a/σβ_a`, with `v_{𝔭_j}(α_a) = m_j^{(a)}` and
`v_𝔯(α_a) = 0` at every prime over a rational prime outside `Sexc ⊇ {p_j}`. Kind: PROVED. -/
theorem exists_kummerData (hK : Module.finrank ℚ (quadField s) = 2) (n : ℕ)
    (C : RingClassSetup (quadField s) S) (hinj : Function.Injective C.p)
    (hne : ∀ j, C.𝔭 j ≠ C.𝔭bar j) {t : ℕ} (m : Fin t → Fin S → ℤ)
    (hm : ∀ a, ∑ j, m a j • setupCls C j = 0) (Sexc : Finset ℕ) (p_mem : ∀ j, C.p j ∈ Sexc) :
    ∃ kd : KummerData s n t,
      (∀ j a, (C.𝔭 j).valuation (quadField s) ⟨kd.α a, kd.α_mem a⟩ = WithZero.exp (-(m a j))) ∧
      ∀ a (𝔯 : HeightOneSpectrum (𝓞 (quadField s))) (q : ℕ), q.Prime → q ∉ Sexc →
        ((q : ℤ) : 𝓞 (quadField s)) ∈ 𝔯.asIdeal →
          𝔯.valuation (quadField s) ⟨kd.α a, kd.α_mem a⟩ = 1 := by
  obtain ⟨α, hv, hs⟩ := radicand_valuations hK C hinj hne m hm
  obtain ⟨ζ, hζ⟩ := exists_primitive (2 ^ n) (pow_ne_zero _ two_ne_zero)
  have hγ : ∀ a, ∃ γ : Qbar, γ ^ 2 ^ n = ((α a : quadField s) : Qbar) := fun a =>
    IsAlgClosed.exists_pow_nat_eq _ (pow_pos two_pos n)
  choose γ hγ using hγ
  let kd : KummerData s n t :=
    { ζ := ζ
      hζ := hζ
      α := fun a => ((α a : quadField s) : Qbar)
      α_mem := fun a => (α a : quadField s).2
      γ := γ
      γ_pow := hγ
      γ_ne := fun a h => by
        have h0 := hγ a
        rw [h, zero_pow (pow_ne_zero _ two_ne_zero)] at h0
        exact (α a).ne_zero (Subtype.ext h0.symm) }
  refine ⟨kd, fun j a => hv j a, fun a 𝔯 q hq hqS h𝔯 => hs a 𝔯 q hq
    (fun j h => hqS (h ▸ p_mem j)) h𝔯⟩

end ZInQ.Contrib.CloudB3E1RingClass
