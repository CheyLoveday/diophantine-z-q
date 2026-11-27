import ZInQKernel.Contrib.CloudB3RC53.AuxFactor.Pieces
import ZInQKernel.Contrib.OneProof.RC.Symbols.Realization

/-!
# AuxFactor, part 2: the dummy anchors (App G)

Manuscript `diophantine_zq.tex`, App G, proof of Proposition `ex:app-rough-companion`, tex
10131–10139: "Prepare these sources and nonempty seeds for every total type at the fixed support.
There are finitely many.  A bounded supply of dummy anchors and reserves works for all of them.
For each `h` realize that supply by distinct primes avoiding the entire fixed support and `h`.
Put every dummy and every other already fixed forbidden prime in the exclusion set of the
preceding nonvanishing construction."

`dummy_realization` (`PROVED`, from lane RC2's `finite_realization_nat`: CRT and Dirichlet): for a
fixed number `A₀` of dummy labels, given as reduced residue classes modulo `m` (`2 ∣ m`), and for
every `h ≠ 0` and every finite exclusion set `X`, there are distinct primes `q_0, …, q_{A₀−1}` in
the prescribed classes avoiding `S`, `X` and the primes of `h`, and their product `a` is positive,
squarefree, with `ω(a) = A₀`, prime to `S ∪ X` and coprime to `h`: exactly the arithmetic part of
RC13's input `hdummy` of `roughCompanion`.  The remaining part of `hdummy` (the realized supply
makes `hk'` partitionable, for the total type that occurs) is `negative_partitionable`
(`Pieces.lean`) read through the coefficient dictionary.
-/

namespace ZInQ.Contrib.CloudB3RC53.AuxFactor

open ZInQ.Manuscript.RC.Symbols Finset

theorem cardDistinctFactors_eq_card (n : ℕ) :
    ArithmeticFunction.cardDistinctFactors n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

/-- **The dummy anchors** (tex 10131–10139), `PROVED`. -/
theorem dummy_realization (m : ℕ) (hm : 0 < m) (h2 : 2 ∣ m) (A₀ : ℕ) (cls : ℕ → ZMod m)
    (hcls : ∀ i, IsUnit (cls i)) (S X : Finset ℕ) (h : ℤ) :
    ∃ q : ℕ → ℕ, (∀ i < A₀, ∀ j < A₀, q i = q j → i = j) ∧
      (∀ i < A₀, (q i).Prime ∧ q i ∉ S ∧ q i ∉ X ∧ ¬ ((q i : ℤ) ∣ h ∧ h ≠ 0) ∧
        ((q i : ℕ) : ZMod m) = cls i) ∧
      0 < ∏ i ∈ range A₀, (q i : ℤ) ∧ Squarefree (∏ i ∈ range A₀, (q i : ℤ)) ∧
      ZInQ.Manuscript.RC.Nonvanishing.omega (∏ i ∈ range A₀, (q i : ℤ)) = A₀ ∧
      (∀ p ∈ S ∪ X, p.Prime → ¬ (p : ℤ) ∣ ∏ i ∈ range A₀, (q i : ℤ)) ∧
      (h ≠ 0 → IsCoprime (∏ i ∈ range A₀, (q i : ℤ)) h) := by
  classical
  obtain ⟨q, hinj, hq, -, -⟩ := finite_realization_nat m hm h2 ∅ (by simp)
    (S ∪ X ∪ h.natAbs.primeFactors) cls hcls (fun _ _ => 0) (fun _ _ => 0) A₀
  have hqP : ∀ i < A₀, (q i).Prime := fun i hi => (hq i hi).1
  have hqA : ∀ i < A₀, q i ∉ S ∪ X ∪ h.natAbs.primeFactors := fun i hi => (hq i hi).2.2.1
  set P : Finset ℕ := (range A₀).image q with hP
  have hPprime : ∀ p ∈ P, p.Prime := by
    intro p hp; obtain ⟨i, hi, rfl⟩ := mem_image.mp hp; exact hqP i (mem_range.mp hi)
  have hinjOn : Set.InjOn q (range A₀ : Set ℕ) := fun i hi j hj hij =>
    hinj i (mem_range.mp hi) j (mem_range.mp hj) hij
  have hprod : ∏ i ∈ range A₀, (q i : ℤ) = ((∏ p ∈ P, p : ℕ) : ℤ) := by
    rw [hP, prod_image (fun i hi j hj hij => hinjOn hi hj hij)]; push_cast; rfl
  have hfac : (∏ p ∈ P, p).primeFactors = P := Nat.primeFactors_prod hPprime
  have hcard : P.card = A₀ := by rw [hP, card_image_of_injOn hinjOn, card_range]
  have hpos : 0 < ∏ p ∈ P, p := prod_pos fun p hp => (hPprime p hp).pos
  have hsqN : Squarefree (∏ p ∈ P, p) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun a ha b hb hab => ?_)
      fun p hp => (hPprime p hp).squarefree
    simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hPprime a ha) (hPprime b hb)).mpr hab
  have hdvdP : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ ((∏ p ∈ P, p : ℕ) : ℤ) → p ∈ P := by
    intro p hp hd
    rw [← hfac]
    exact Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd_natCast.mp hd, hpos.ne'⟩
  refine ⟨q, hinj, fun i hi => ⟨hqP i hi, fun hS => hqA i hi (by simp [hS]),
    fun hX => hqA i hi (by simp [hX]), fun ⟨hd, hh⟩ => hqA i hi ?_, (hq i hi).2.2.2⟩, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp only [mem_union]
    exact Or.inr (Nat.mem_primeFactors.mpr ⟨hqP i hi, Int.natCast_dvd.mp hd,
      Int.natAbs_ne_zero.mpr hh⟩)
  · rw [hprod]; exact_mod_cast hpos
  · rw [hprod]; exact (Int.squarefree_natCast).mpr hsqN
  · rw [hprod, ZInQ.Manuscript.RC.Nonvanishing.omega, Int.natAbs_natCast,
      cardDistinctFactors_eq_card, hfac, hcard]
  · intro p hp hpp hd
    rw [hprod] at hd
    obtain ⟨i, hi, rfl⟩ := mem_image.mp (hdvdP p hpp hd)
    exact hqA i (mem_range.mp hi) (mem_union_left _ hp)
  · intro hh
    rw [hprod, Int.isCoprime_iff_gcd_eq_one]
    by_contra hg
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
    have h1 : (p : ℤ) ∣ ((∏ p ∈ P, p : ℕ) : ℤ) :=
      (Int.natCast_dvd_natCast.mpr hpg).trans (Int.gcd_dvd_left _ _)
    have h2' : (p : ℤ) ∣ h := (Int.natCast_dvd_natCast.mpr hpg).trans (Int.gcd_dvd_right _ _)
    obtain ⟨i, hi, rfl⟩ := mem_image.mp (hdvdP p hp h1)
    exact hqA i (mem_range.mp hi) (mem_union_right _
      (Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp h2', Int.natAbs_ne_zero.mpr hh⟩))

end ZInQ.Contrib.CloudB3RC53.AuxFactor
