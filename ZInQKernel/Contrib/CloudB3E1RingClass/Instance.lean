import ZInQKernel.Contrib.CloudB3E1RingClass.FromPairs

/-!
# A concrete instance: `K = ℚ(√−7)`, `2N = 2`, an active pair over `11`

Manuscript `diophantine_zq.tex`, tex 2720, 3528–3534. Non-vacuity witness for
`exists_genuineMovingComplete`.

Take `K = ℚ(s)` with `s² = −7` and `ω = (1 + s)/2 ∈ 𝒪_K`, so `ω² = ω − 2`. For a prime `q ≠ 7` and an
integer `c` with `q ∣ c² − c + 2` and `2c − 1` invertible mod `q`, the ideals `𝔮 = (q, ω − c)` and
`𝔮̄ = (q, ω − (1 − c))` are distinct primes with `𝔮𝔮̄ = (q)` (`exists_split_pair`). This gives:
* the 2N pair over `2`, with `c = 0`;
* the active pair over `11`, with `c = 5`.

`K ≠ ℚ(i), ℚ(√−3)` (`no_sqrt_neg_one`, `no_cube_root`).

`exists_instance_neg7` is the instance. For every `E` and `n` it produces:
* the setup over `ℚ(√−7)`, whose 2N pair lies over `2` and whose active pair lies over `11`;
* a `GenuineMovingComplete` on it;
* `hP` for `P = {𝔭₂, 𝔭̄₂}`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain Polynomial
open ZInQ.Manuscript.RC.TateWiring
open ZInQ.Contrib.ChebFD.C10 (Qbar)
open scoped nonZeroDivisors

namespace Neg7

variable {s : Qbar} (hs : s ^ 2 = algebraMap ℚ Qbar (-7))

/-- `s ∈ ℚ(s)`. Kind: definition. -/
def g (s : Qbar) : quadField s := ⟨s, IntermediateField.mem_adjoin_simple_self ℚ s⟩

theorem not_sq_7 : ¬ IsSquare 7 := by
  rintro ⟨k, hk⟩
  have : k ≤ 3 := by nlinarith
  interval_cases k <;> omega

theorem not_sq_21 : ¬ IsSquare 21 := by
  rintro ⟨k, hk⟩
  have : k ≤ 5 := by nlinarith
  interval_cases k <;> omega

theorem not_isSquare_aux {r : ℚ} {m : ℕ} (hm : ¬ IsSquare m) (h : 7 * r ^ 2 = m / 7) : False := by
  apply hm
  have : IsSquare (m : ℚ) := ⟨7 * r, by linarith [show (7 * r) * (7 * r) = 7 * (7 * r ^ 2) by ring]⟩
  exact_mod_cast (Rat.isSquare_natCast_iff.mp this)

include hs

theorem g_sq : g s ^ 2 = -7 := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow]
  change s ^ 2 = ((-7 : quadField s) : Qbar)
  rw [hs]
  simp only [map_neg, map_ofNat, IntermediateField.coe_neg]
  norm_cast

theorem hK : Module.finrank ℚ (quadField s) = 2 :=
  finrank_quadField_of_neg hs (by norm_num)

/-- The non-trivial automorphism. Kind: definition. -/
def σ : quadField s ≃ₐ[ℚ] quadField s := conjσ (hK hs)

theorem σ_g : σ hs (g s) = -g s := by
  have h2 : (σ hs (g s)) ^ 2 = (g s) ^ 2 := by
    rw [← map_pow, g_sq hs, map_neg, map_ofNat]
  have h3 : (σ hs (g s) - g s) * (σ hs (g s) + g s) = 0 := by ring_nf; rw [h2]; ring
  rcases mul_eq_zero.mp h3 with h | h
  · exfalso
    have hσ1 : σ hs = 1 := by
      have : (σ hs).toAlgHom = (1 : quadField s ≃ₐ[ℚ] quadField s).toAlgHom :=
        IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := quadField s) (s := {s}) rfl
          (fun x hx => by
            obtain rfl := Set.mem_singleton_iff.mp hx
            change σ hs (g x) = g x
            exact sub_eq_zero.mp h)
      exact AlgEquiv.ext fun x => congrArg (fun φ : quadField s →ₐ[ℚ] quadField s => φ x) this
    have hne : σ hs ≠ 1 := by
      have := (exists_conj (hK hs)).choose_spec.1
      exact this
    exact hne hσ1
  · exact eq_neg_of_add_eq_zero_left h

/-- **Squares of rationals in `K`**: if `y² ∈ ℚ` then `y ∈ ℚ` or `y ∈ ℚs`. Kind: PROVED. -/
theorem sq_rat {y : quadField s} {a : ℚ} (hy : y ^ 2 = algebraMap ℚ (quadField s) a) :
    (∃ r : ℚ, y = algebraMap ℚ _ r) ∨ (∃ r : ℚ, y = algebraMap ℚ _ r * g s) := by
  have := isGalois_of_finrank_two (hK hs)
  have hfix : ∀ z : quadField s, σ hs z = z → z ∈ Set.range (algebraMap ℚ (quadField s)) := by
    intro z hz
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro f
    by_cases hf : f = 1
    · rw [hf]; rfl
    · rw [conjσ_spec (hK hs) f hf]; exact hz
  have h2 : (σ hs y) ^ 2 = y ^ 2 := by rw [← map_pow, hy, AlgEquiv.commutes]
  have h3 : (σ hs y - y) * (σ hs y + y) = 0 := by ring_nf; rw [h2]; ring
  have hg0 : g s ≠ 0 := fun h => by
    have := g_sq hs; rw [h, zero_pow two_ne_zero] at this; norm_num at this
  rcases mul_eq_zero.mp h3 with h | h
  · obtain ⟨r, hr⟩ := hfix y (sub_eq_zero.mp h)
    exact Or.inl ⟨r, hr.symm⟩
  · obtain ⟨r, hr⟩ := hfix (y / g s) (by
      rw [map_div₀, σ_g hs, eq_neg_of_add_eq_zero_left h, neg_div_neg_eq])
    refine Or.inr ⟨r, ?_⟩
    rw [hr, div_mul_cancel₀ _ hg0]

/-- `K ≠ ℚ(i)`. Kind: PROVED. -/
theorem no_sqrt_neg_one : ∀ x : quadField s, x ^ 2 ≠ -1 := by
  intro x hx
  have hy : x ^ 2 = algebraMap ℚ (quadField s) (-1) := by rw [hx]; simp
  rcases sq_rat hs hy with ⟨r, hr⟩ | ⟨r, hr⟩
  · rw [hr, ← map_pow] at hy
    have := (algebraMap ℚ (quadField s)).injective hy
    nlinarith [sq_nonneg r]
  · rw [hr, mul_pow, g_sq hs, ← map_pow] at hy
    have h7 : algebraMap ℚ (quadField s) (r ^ 2 * (-7)) = algebraMap ℚ (quadField s) (-1) := by
      rw [map_mul]; simpa using hy
    have := (algebraMap ℚ (quadField s)).injective h7
    exact not_isSquare_aux (r := r) (m := 7) not_sq_7 (by linarith)

/-- `K ≠ ℚ(√−3)`. Kind: PROVED. -/
theorem no_cube_root : ∀ x : quadField s, x ^ 2 + x + 1 ≠ 0 := by
  intro x hx
  have hy : (2 * x + 1) ^ 2 = algebraMap ℚ (quadField s) (-3) := by
    rw [map_neg, map_ofNat]; linear_combination 4 * hx
  rcases sq_rat hs hy with ⟨r, hr⟩ | ⟨r, hr⟩
  · rw [hr, ← map_pow] at hy
    have := (algebraMap ℚ (quadField s)).injective hy
    nlinarith [sq_nonneg r]
  · rw [hr, mul_pow, g_sq hs, ← map_pow] at hy
    have h7 : algebraMap ℚ (quadField s) (r ^ 2 * (-7)) = algebraMap ℚ (quadField s) (-3) := by
      rw [map_mul]; simpa using hy
    have := (algebraMap ℚ (quadField s)).injective h7
    exact not_isSquare_aux (r := r) (m := 21) not_sq_21 (by linarith)

/-! ### `ω = (1 + s)/2` and the split pairs -/

omit hs in
theorem coe_two : ((2 : 𝓞 (quadField s)) : quadField s) = 2 := rfl

omit hs in
theorem coe_seven : ((7 : 𝓞 (quadField s)) : quadField s) = 7 := rfl

theorem isIntegral_ω : IsIntegral ℤ ((1 + g s) / 2) := by
  refine ⟨X ^ 2 - X + C 2, by monicity!, ?_⟩
  simp only [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_ofNat, map_ofNat]
  linear_combination (1 / 4 : quadField s) * g_sq hs

/-- `ω = (1 + s)/2 ∈ 𝒪_K`. Kind: definition. -/
def ω : 𝓞 (quadField s) := ⟨(1 + g s) / 2, isIntegral_ω hs⟩

theorem coe_ω : ((ω hs : 𝓞 (quadField s)) : quadField s) = (1 + g s) / 2 := rfl

theorem ω_sq : ω hs ^ 2 = ω hs - 2 := by
  apply RingOfIntegers.ext
  push_cast [coe_ω, coe_two]
  linear_combination (1 / 4 : quadField s) * g_sq hs

theorem σ_ω : σ hs • ω hs = 1 - ω hs := by
  apply RingOfIntegers.ext
  change σ hs ((1 + g s) / 2) = _
  push_cast [coe_ω]
  rw [map_div₀, map_add, map_one, σ_g hs, map_ofNat]
  ring

theorem σ_intCast (n : ℤ) : σ hs • (n : 𝓞 (quadField s)) = n := by
  apply RingOfIntegers.ext
  change σ hs ((n : 𝓞 (quadField s)) : quadField s) = _
  have hc : ((n : 𝓞 (quadField s)) : quadField s) = (n : quadField s) := by simp
  rw [hc, map_intCast]

omit hs in
/-- An integral element of `K` that is rational is an integer. Kind: PROVED. -/
theorem rat_of_integral {K : Type} [Field K] [NumberField K] (x : 𝓞 K) {r : ℚ}
    (hx : (x : K) = algebraMap ℚ K r) : ∃ n : ℤ, (n : ℚ) = r := by
  have h1 : IsIntegral ℤ (algebraMap ℚ K r) := hx ▸ RingOfIntegers.isIntegral_coe x
  have h2 : IsIntegral ℤ r := by
    have hf : Function.Injective ((Algebra.ofId ℚ K).restrictScalars ℤ) :=
      (algebraMap ℚ K).injective
    exact (isIntegral_algHom_iff _ hf).mp h1
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  exact ⟨n, by simpa using hn⟩

theorem coe_sInt : ((2 * ω hs - 1 : 𝓞 (quadField s)) : quadField s) = g s := by
  push_cast [coe_ω, coe_two]; ring

/-- **`s ∉ q𝒪_K`** for a prime `q`. Kind: PROVED. -/
theorem sInt_not_mem {q : ℕ} (hq : q.Prime) :
    (2 * ω hs - 1 : 𝓞 (quadField s)) ∉ Ideal.span {(((q : ℤ)) : 𝓞 (quadField s))} := by
  intro h
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h
  have hq0 : ((q : ℚ) : quadField s) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hga : g s = (a : quadField s) * (q : quadField s) := by
    rw [← coe_sInt hs, ← ha]; push_cast; ring
  have ha2 : ((a ^ 2 : 𝓞 (quadField s)) : quadField s) =
      algebraMap ℚ (quadField s) (-7 / (q : ℚ) ^ 2) := by
    have hq0' : (q : quadField s) ≠ 0 := by exact_mod_cast hq.ne_zero
    rw [map_div₀, map_pow, map_neg, map_ofNat, map_natCast, eq_div_iff (pow_ne_zero _ hq0')]
    have hp : ((a ^ 2 : 𝓞 (quadField s)) : quadField s) = (a : quadField s) ^ 2 := by push_cast; rfl
    rw [hp, ← mul_pow, ← hga, g_sq hs]
  obtain ⟨n, hn⟩ := rat_of_integral _ ha2
  have hq0q : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hnq : (n : ℚ) * (q : ℚ) ^ 2 = -7 := by
    rw [hn]; field_simp
  have hnq' : n * (q : ℤ) ^ 2 = -7 := by exact_mod_cast hnq
  have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast hq.two_le
  rcases eq_or_lt_of_le hq2 with h2 | h3
  · rw [← h2] at hnq'; omega
  · have h3' : (3 : ℤ) ≤ q := h3
    rcases le_or_gt n 0 with hn0 | hn0
    · rcases eq_or_lt_of_le hn0 with hz | hneg
      · rw [hz] at hnq'; omega
      · nlinarith
    · nlinarith

omit hs in
/-- **`−7 ∉ q𝒪_K`** for a prime `q ≠ 7`. Kind: PROVED. -/
theorem neg7_not_mem {q : ℕ} (hq : q.Prime) (hq7 : q ≠ 7) :
    (-7 : 𝓞 (quadField s)) ∉ Ideal.span {(((q : ℤ)) : 𝓞 (quadField s))} := by
  intro h
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h
  have hq0' : (q : quadField s) ≠ 0 := by exact_mod_cast hq.ne_zero
  have ha' : ((a : 𝓞 (quadField s)) : quadField s) = algebraMap ℚ (quadField s) (-7 / (q : ℚ)) := by
    have h1 := congrArg (algebraMap (𝓞 (quadField s)) (quadField s)) ha
    rw [map_mul, map_neg, map_intCast, map_ofNat] at h1
    rw [map_div₀, map_neg, map_ofNat, map_natCast, eq_div_iff hq0']
    change algebraMap (𝓞 (quadField s)) (quadField s) a * _ = _
    rw [← h1]
    push_cast
    ring
  obtain ⟨n, hn⟩ := rat_of_integral _ ha'
  have hq0q : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hnq : (n : ℚ) * (q : ℚ) = -7 := by rw [hn]; field_simp
  have hnq' : n * (q : ℤ) = -7 := by exact_mod_cast hnq
  have hdvd : (q : ℤ) ∣ 7 := ⟨-n, by linarith⟩
  have hdvd' : q ∣ 7 := by exact_mod_cast hdvd
  rcases (Nat.prime_def.mp (by norm_num : Nat.Prime 7)).2 q hdvd' with h1 | h1
  · exact hq.one_lt.ne' h1
  · exact hq7 h1

theorem σ_mem_span {q : ℤ} {x : 𝓞 (quadField s)}
    (hx : x ∈ Ideal.span {((q : ℤ) : 𝓞 (quadField s))}) :
    σ hs • x ∈ Ideal.span {((q : ℤ) : 𝓞 (quadField s))} := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [smul_mul', σ_intCast hs]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- **The split pair `(q, ω − c)(q, ω − (1 − c)) = (q)`** for a prime `q ≠ 7` with
`q ∣ c² − c + 2` and `2c − 1` invertible mod `q`. Kind: PROVED. -/
theorem exists_split_pair {q : ℕ} (hq : q.Prime) (hq7 : q ≠ 7) (c k u t : ℤ)
    (hk : c ^ 2 - c + 2 = q * k) (hut : u * (2 * c - 1) + t * q = 1) :
    ∃ P Q : HeightOneSpectrum (𝓞 (quadField s)), P ≠ Q ∧
      P.asIdeal * Q.asIdeal = Ideal.span {(((q : ℤ)) : 𝓞 (quadField s))} := by
  set qq : 𝓞 (quadField s) := ((q : ℤ) : 𝓞 (quadField s))
  set a : 𝓞 (quadField s) := ω hs - c
  set b : 𝓞 (quadField s) := ω hs - (1 - c)
  have hk' : ((c : 𝓞 (quadField s))) ^ 2 - c + 2 = qq * k := by
    have := congrArg (fun z : ℤ => (z : 𝓞 (quadField s))) hk
    push_cast at this; exact this
  have hut' : (u : 𝓞 (quadField s)) * (2 * c - 1) + t * qq = 1 := by
    have := congrArg (fun z : ℤ => (z : 𝓞 (quadField s))) hut
    push_cast at this; exact this
  have hab : a * b = qq * (-k) := by
    simp only [a, b]
    linear_combination ω_sq hs - hk'
  have hsab : 2 * ω hs - 1 = a + b := by simp only [a, b]; ring
  have hσb : σ hs • b = -a := by
    simp only [a, b]
    rw [smul_sub, smul_sub, σ_ω hs, smul_one, σ_intCast hs]; ring
  have hσa : σ hs • a = -b := by
    simp only [a, b]
    rw [smul_sub, σ_ω hs, σ_intCast hs]; ring
  have hqmem : ∀ x : 𝓞 (quadField s), qq * x ∈ Ideal.span {qq} := fun x =>
    Ideal.mem_span_singleton'.mpr ⟨x, mul_comm _ _⟩
  let P : Ideal (𝓞 (quadField s)) := Ideal.span {qq, a}
  let Q : Ideal (𝓞 (quadField s)) := Ideal.span {qq, b}
  have hPQ : P * Q = Ideal.span {qq} := by
    simp only [P, Q]
    rw [Ideal.span_pair_mul_span_pair]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hqmem _
      · exact hqmem _
      · rw [mul_comm]; exact hqmem _
      · rw [hab]; exact hqmem _
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have h1 : qq = u * (qq * b - a * qq) + t * (qq * qq) := by
        simp only [a, b]; linear_combination (-qq) * hut'
      have hmem : u * (qq * b - a * qq) + t * (qq * qq) ∈
          Ideal.span {qq * qq, qq * b, a * qq, a * b} := by
        refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.sub_mem _ ?_ ?_))
          (Ideal.mul_mem_left _ _ ?_)
        · exact Ideal.subset_span (by simp)
        · exact Ideal.subset_span (by simp)
        · exact Ideal.subset_span (by simp)
      rw [SetLike.mem_coe]
      rwa [← h1] at hmem
  have hnot : ∀ x : 𝓞 (quadField s), x ∈ Ideal.span {qq} → σ hs • x ∈ Ideal.span {qq} :=
    fun x hx => σ_mem_span hs hx
  have hs_not := sInt_not_mem hs hq
  have hPtop : P ≠ ⊤ := by
    intro h
    have hQ : Q = Ideal.span {qq} := by rw [← hPQ, h, Ideal.top_mul]
    have hb : b ∈ Ideal.span {qq} := hQ ▸ Ideal.subset_span (by simp)
    have ha : a ∈ Ideal.span {qq} := by
      have := hnot b hb; rw [hσb] at this; exact (Ideal.neg_mem_iff _).mp this
    exact hs_not (hsab ▸ Ideal.add_mem _ ha hb)
  have hQtop : Q ≠ ⊤ := by
    intro h
    have hP : P = Ideal.span {qq} := by rw [← hPQ, h, Ideal.mul_top]
    have ha : a ∈ Ideal.span {qq} := hP ▸ Ideal.subset_span (by simp)
    have hb : b ∈ Ideal.span {qq} := by
      have := hnot a ha; rw [hσa] at this; exact (Ideal.neg_mem_iff _).mp this
    exact hs_not (hsab ▸ Ideal.add_mem _ ha hb)
  have hPneQ : P ≠ Q := by
    intro h
    have ha : a ∈ P := Ideal.subset_span (by simp)
    have hb : b ∈ P := h ▸ (Ideal.subset_span (by simp) : b ∈ Q)
    have hsP : 2 * ω hs - 1 ∈ P := hsab ▸ Ideal.add_mem _ ha hb
    have hsq : (2 * ω hs - 1) * (2 * ω hs - 1) ∈ Ideal.span {qq} := by
      rw [← hPQ, ← h]; exact Ideal.mul_mem_mul hsP (h ▸ hsP)
    have h7 : (2 * ω hs - 1) * (2 * ω hs - 1) = -7 := by
      linear_combination 4 * ω_sq hs
    exact neg7_not_mem hq hq7 (h7 ▸ hsq)
  -- the norms
  have hnorm : Ideal.absNorm P * Ideal.absNorm Q = q ^ 2 := by
    rw [← map_mul, hPQ, Ideal.absNorm_span_singleton,
      show qq = algebraMap ℤ (𝓞 (quadField s)) (q : ℤ) by simp [qq], Algebra.norm_algebraMap,
      RingOfIntegers.rank, hK hs, Int.natAbs_pow, Int.natAbs_natCast]
  have hP1 : Ideal.absNorm P ≠ 1 := fun h => hPtop (Ideal.absNorm_eq_one_iff.mp h)
  have hQ1 : Ideal.absNorm Q ≠ 1 := fun h => hQtop (Ideal.absNorm_eq_one_iff.mp h)
  have hPq : Ideal.absNorm P = q := by
    obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow hq).mp (Dvd.intro _ hnorm)
    interval_cases i
    · exact absurd (by simpa using hieq) hP1
    · simpa using hieq
    · exfalso
      rw [hieq] at hnorm
      have hpos : 0 < q ^ 2 := pow_pos hq.pos 2
      exact hQ1 (Nat.eq_of_mul_eq_mul_left hpos (hnorm.trans (mul_one _).symm))
  have hQq : Ideal.absNorm Q = q := by
    rw [hPq, pow_two] at hnorm
    exact Nat.eq_of_mul_eq_mul_left hq.pos hnorm
  have hPprime : P.IsPrime := Ideal.isPrime_of_irreducible_absNorm (hPq ▸ hq)
  have hQprime : Q.IsPrime := Ideal.isPrime_of_irreducible_absNorm (hQq ▸ hq)
  have hqq0 : qq ≠ 0 := by simp [qq, hq.ne_zero]
  have hP0 : P ≠ ⊥ := fun h => by
    have hm : qq ∈ P := Ideal.subset_span (by simp)
    rw [h] at hm; exact hqq0 ((Submodule.mem_bot _).mp hm)
  have hQ0 : Q ≠ ⊥ := fun h => by
    have hm : qq ∈ Q := Ideal.subset_span (by simp)
    rw [h] at hm; exact hqq0 ((Submodule.mem_bot _).mp hm)
  refine ⟨⟨P, hPprime, hP0⟩, ⟨Q, hQprime, hQ0⟩, fun h => hPneQ ?_, hPQ⟩
  exact congrArg HeightOneSpectrum.asIdeal h

end Neg7

/-! ### The instance -/

open Neg7 in
/-- **A concrete instance of the genuine moving data** (tex 2720, 3528–3534): over `K = ℚ(√−7)`,
a setup whose first two pairs are the 2N pair over `2` and an active pair over `11`, a
`GenuineMovingComplete` on it, and `hP` for `P = {𝔭₂, 𝔭̄₂}`. Kind: PROVED. -/
theorem exists_instance_neg7 (E : WeierstrassCurve ℚ) (n : ℕ) :
    ∃ (s : Qbar) (S : ℕ) (C : RingClassSetup (quadField s) S) (I : GenuineMovingComplete E n s C)
      (j₂ j₁₁ : Fin S), I.D = -7 ∧ C.p j₂ = 2 ∧ I.over2N j₂ ∧ ¬ I.act j₂ ∧
      C.p j₁₁ = 11 ∧ I.act j₁₁ ∧ ¬ I.over2N j₁₁ ∧
      ∀ v ∈ ({C.𝔭 j₂, C.𝔭bar j₂} : Set (HeightOneSpectrum (𝓞 (quadField s)))),
        ∃ j, I.over2N j ∧ (v = C.𝔭 j ∨ v = C.𝔭bar j) := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap ℚ Qbar (-7)) (by norm_num : 0 < 2)
  obtain ⟨P2, Q2, hne2, hmul2⟩ := exists_split_pair hs Nat.prime_two (by norm_num)
    0 1 (-1) 0 (by norm_num) (by norm_num)
  obtain ⟨P11, Q11, hne11, hmul11⟩ := exists_split_pair hs (by norm_num : Nat.Prime 11)
    (by norm_num) 5 2 5 (-4) (by norm_num) (by norm_num)
  let P₀ : Fin 2 → HeightOneSpectrum (𝓞 (quadField s)) := ![P2, P11]
  let Q₀ : Fin 2 → HeightOneSpectrum (𝓞 (quadField s)) := ![Q2, Q11]
  let p₀ : Fin 2 → ℕ := ![2, 11]
  have hp₀ : ∀ j, (p₀ j).Prime := fun j => by
    fin_cases j
    · exact Nat.prime_two
    · norm_num [p₀]
  have hinj₀ : Function.Injective p₀ := fun i j h => by
    fin_cases i <;> fin_cases j <;> simp_all [p₀]
  have hne₀ : ∀ j, P₀ j ≠ Q₀ j := fun j => by
    fin_cases j
    · exact hne2
    · exact hne11
  have hmul₀ : ∀ j, (P₀ j).asIdeal * (Q₀ j).asIdeal =
      Ideal.span {(((p₀ j : ℤ)) : 𝓞 (quadField s))} := fun j => by
    fin_cases j
    · exact hmul2
    · exact hmul11
  obtain ⟨S₁, C, I, hpre, -, hlab, -, -, hD⟩ :=
    exists_genuineMovingComplete E n hs (by norm_num) (no_sqrt_neg_one hs) (no_cube_root hs)
      P₀ Q₀ p₀ hp₀ hinj₀ hne₀ hmul₀ (fun j => j = 1) (fun j => j = 0)
      (fun j h1 h0 => by rw [h1] at h0; exact absurd h0 (by decide))
      (fun j hj => by rw [hj]; norm_num [p₀]) ∅ ∅ ∅ P2
  refine ⟨s, 2 + S₁, C, I, Fin.castAdd S₁ 0, Fin.castAdd S₁ 1, hD, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(hpre 0).2.2]; rfl
  · exact ((hlab 0).2).mpr rfl
  · exact fun h => absurd ((hlab 0).1.mp h) (by decide)
  · rw [(hpre 1).2.2]; rfl
  · exact ((hlab 1).1).mpr rfl
  · exact fun h => absurd ((hlab 1).2.mp h) (by decide)
  · intro v hv
    exact ⟨Fin.castAdd S₁ 0, ((hlab 0).2).mpr rfl, hv⟩

end ZInQ.Contrib.CloudB3E1RingClass
