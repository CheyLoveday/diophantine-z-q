import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Int
import Mathlib.NumberTheory.FundamentalDiscriminant

open NumberField

namespace ZInQ.BFHLeaf

/-- `p` splits in `K`: there are two distinct prime ideals of `𝓞 K` above `p`. -/
def SplitsIn (K : Type*) [Field K] [NumberField K] (p : ℕ) : Prop :=
  ∃ P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
    ∃ Q ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K), P ≠ Q

variable {K : Type*} [Field K] [NumberField K]

theorem ef_eq_one (hK : Module.finrank ℚ K = 2) {p : ℕ} [hp : Fact p.Prime] {P Q : Ideal (𝓞 K)}
    (hP : P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K))
    (hQ : Q ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) (hPQ : P ≠ Q) :
    P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1 := by
  set p' : Ideal ℤ := Ideal.span {(p : ℤ)} with hp'
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p' (𝓞 K)
  rw [RingOfIntegers.rank, hK] at hsum
  have hp0 : p' ≠ ⊥ := by
    rw [hp', Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.out.ne_zero
  have hpos : ∀ q : p'.primesOver (𝓞 K), 1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    intro q
    have h1 : 0 < q.1.ramificationIdx ℤ :=
      Ideal.ramificationIdx_pos_of_isDedekindDomain' (p := p') (q := q.1) hp0
    have h2 : 0 < q.1.inertiaDeg ℤ := Ideal.inertiaDeg_pos q.1 ℤ
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero h1.ne' h2.ne')
  have hne : (⟨P, hP⟩ : p'.primesOver (𝓞 K)) ≠ ⟨Q, hQ⟩ := fun h => hPQ (congrArg Subtype.val h)
  have hle := Finset.add_le_sum (f := fun q : p'.primesOver (𝓞 K) =>
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ) (fun i _ => Nat.zero_le _)
    (Finset.mem_univ ⟨P, hP⟩) (Finset.mem_univ ⟨Q, hQ⟩) hne
  have hQ1 := hpos ⟨Q, hQ⟩
  have hP1 := hpos ⟨P, hP⟩
  simp only at hle hQ1 hP1
  have hPe : P.ramificationIdx ℤ * P.inertiaDeg ℤ = 1 := by omega
  exact ⟨Nat.eq_one_of_mul_eq_one_right hPe, Nat.eq_one_of_mul_eq_one_left hPe⟩


theorem span_ne_bot {p : ℕ} [hp : Fact p.Prime] : Ideal.span {(p : ℤ)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.out.ne_zero

omit [NumberField K] in
/-- An integer lies in a prime above `p` iff `p` divides it. -/
theorem intCast_mem_iff {p : ℕ} {P : Ideal (𝓞 K)}
    (hP : P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) (n : ℤ) :
    (n : 𝓞 K) ∈ P ↔ (p : ℤ) ∣ n := by
  have := hP.2
  rw [← Ideal.mem_span_singleton, Ideal.over_def P (Ideal.span {(p : ℤ)}), Ideal.under,
    Ideal.mem_comap, eq_intCast]

/-- Residue degree one: every integer of `K` is congruent to a rational integer modulo `P`. -/
theorem exists_int_sub_mem (hK : Module.finrank ℚ K = 2) {p : ℕ} [hp : Fact p.Prime]
    {P Q : Ideal (𝓞 K)} (hP : P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K))
    (hQ : Q ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) (hPQ : P ≠ Q) (x : 𝓞 K) :
    ∃ n : ℤ, x - (n : 𝓞 K) ∈ P := by
  have hf := (ef_eq_one hK hP hQ hPQ).2
  have := hP.1; have := hP.2
  have : P.IsMaximal :=
    Ideal.IsPrime.isMaximal hP.1 (Ideal.ne_bot_of_liesOver_of_ne_bot (span_ne_bot (p := p)) P)
  let := Ideal.Quotient.field (Ideal.span {(p : ℤ)})
  let := Ideal.Quotient.field P
  rw [Ideal.inertiaDeg_eq_of_isMaximal (Ideal.span {(p : ℤ)}) P] at hf
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : 𝓞 K ⧸ P) one_ne_zero).mp hf
    (Ideal.Quotient.mk P x)
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨n, ?_⟩
  rw [← Ideal.Quotient.eq, ← hc, Algebra.smul_def, mul_one,
    Ideal.Quotient.algebraMap_mk_of_liesOver, eq_intCast]

/-- Ramification index one: `p ∉ P²`. -/
theorem natCast_not_mem_sq (hK : Module.finrank ℚ K = 2) {p : ℕ} [hp : Fact p.Prime]
    {P Q : Ideal (𝓞 K)} (hP : P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K))
    (hQ : Q ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) (hPQ : P ≠ Q) :
    (p : 𝓞 K) ∉ P ^ 2 := by
  have he := (ef_eq_one hK hP hQ hPQ).1
  have := hP.1; have := hP.2
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P (span_ne_bot (p := p))] at he
  intro hmem
  have hle : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ P ^ 2 := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    simpa using hmem
  have hbdd : BddAbove {n | Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ P ^ n} := by
    by_contra hnb
    have h0 := Nat.sSup_of_not_bddAbove hnb
    rw [Ideal.ramificationIdx', h0] at he
    exact absurd he (by norm_num)
  have h2 := le_csSup hbdd (show 2 ∈ _ from hle)
  rw [Ideal.ramificationIdx'] at he
  omega

omit [NumberField K] in
/-- If `p u ∈ P²` with `p ∤ u` and `p ∈ P`, then `p ∈ P²`. -/
theorem natCast_mem_sq_of_mul {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hpP : (p : 𝓞 K) ∈ P)
    {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) (h : ((p : ℤ) * u : 𝓞 K) ∈ P ^ 2) : (p : 𝓞 K) ∈ P ^ 2 := by
  obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hu
  have e : (p : 𝓞 K) = (b : 𝓞 K) * ((p : ℤ) * u : 𝓞 K) + (a : 𝓞 K) * ((p : 𝓞 K) * (p : 𝓞 K)) := by
    have := congrArg (fun z : ℤ => ((z * p : ℤ) : 𝓞 K)) hab
    simp only [Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_natCast] at this
    push_cast
    linear_combination -this
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h)
    (Ideal.mul_mem_left _ _ (by rw [pow_two]; exact Ideal.mul_mem_mul hpP hpP))

/-- An element of `K` satisfying a monic quadratic over `ℤ` is an integer of `K`. -/
theorem exists_ringOfIntegers_of_sq {x : K} {b c : ℤ} (h : x ^ 2 = b * x + c) :
    ∃ y : 𝓞 K, (y : K) = x := by
  have hint : IsIntegral ℤ x := by
    refine ⟨Polynomial.X ^ 2 - (Polynomial.C b * Polynomial.X + Polynomial.C c), ?_, ?_⟩
    · apply Polynomial.monic_X_pow_sub
      compute_degree!
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_X_pow, h]
      simp
  exact ⟨⟨x, hint⟩, rfl⟩

end ZInQ.BFHLeaf
