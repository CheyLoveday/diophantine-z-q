import ZInQKernel.Contrib.OneProof.RC.EvenBudget.Source
import ZInQKernel.Contrib.OneProof.RC.ThetaCoeff.Forms

/-! Exact (O.9) and (O.11) for an integral even source, including
negative normalization exponents. No finite precision is used. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenBudget

open ZInQ.Manuscript.RC.Odd

variable {O K : Type} [CommRing O] [Field K] [CharZero K] [Algebra O K]
variable {δ : ℤ} {η : ℕ → O} {good adm : ℕ → Prop} {ap : ℕ → ℤ} {a : ℕ → O}

/-- Use a cutoff only as an argument of the existing division lemma. Here
it can exceed any requested exponent because the even bound is exact. -/
theorem raw_bound (H : ∀ t, SourceHyp t δ η good adm ap a)
    (J : List ℕ) (hJ : J.Nodup) (hg : ∀ p ∈ J, good p) (n : ℕ) :
    (2 : O) ^ (δ + J.length + (oddPart n \ J.toFinset).card).toNat ∣ TL η J a n := by
  let e : ℤ := δ + J.length + (oddPart n \ J.toFinset).card
  have h : e ≤ (e.toNat : ℤ) := by omega
  simpa only [e, min_eq_right h] using O9 (H e.toNat) J hJ hg n

theorem raw_shell_bound (H : ∀ t, SourceHyp t δ η good adm ap a)
    (J : List ℕ) (hJ : J.Nodup) (hg : ∀ p ∈ J, good p)
    (w : ℕ → ℤ) (hw : ∀ m, Odd m → Odd (w m))
    {d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0) (hmodd : Odd m)
    (hU : oddPart d ⊆ J.toFinset) (hmG : ∀ p ∈ m.primeFactors, good p) :
    (2 : O) ^ (δ + J.length + 1).toNat ∣
      TL η J a (d * m ^ 2) - TL η J a d * (η m * (w m : O)) := by
  let e : ℤ := δ + J.length + 1
  have h : e ≤ (e.toNat : ℤ) := by omega
  simpa only [e, min_eq_right h] using O11_theta (H e.toNat) J hJ hg w hw hd hm hmodd hU hmG

/-- An integer-power division performed in the coefficient ring. Negative
exponents require multiplication; nonnegative ones use divisibility. -/
theorem scaled_witness {e : ℤ} {x : O} (h : (2 : O) ^ e.toNat ∣ x) :
    ∃ y : O, algebraMap O K y = (2 : K) ^ (-e) * algebraMap O K x := by
  by_cases he : 0 ≤ e
  · obtain ⟨y, hy⟩ := h
    refine ⟨y, ?_⟩
    rw [hy, map_mul, map_pow, map_ofNat, ← zpow_natCast, Int.toNat_of_nonneg he,
      ← mul_assoc, ← zpow_add₀ (by norm_num : (2 : K) ≠ 0), neg_add_cancel, zpow_zero, one_mul]
  · exact ⟨(2 : O) ^ (-e).toNat * x, by
      rw [map_mul, map_pow, map_ofNat, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]⟩

/-- Where the squarefree kernel has at least two primes outside the
operators, the divided (O.11) coefficient is an integer two times an
integral coefficient. This is the Fourier input to the two-fresh test. -/
theorem normalized_double (H : ∀ t, SourceHyp t δ η good adm ap a)
    (J : List ℕ) (hJ : J.Nodup) (hg : ∀ p ∈ J, good p) {n : ℕ}
    (hweight : 2 ≤ (oddPart n \ J.toFinset).card) :
    ∃ y : O, (2 : K) ^ (-(δ + J.length + 1)) * algebraMap O K (TL η J a n) =
      2 * algebraMap O K y := by
  have hd := raw_bound H J hJ hg n
  have hh : (2 : O) ^ (δ + J.length + 2).toNat ∣ TL η J a n :=
    two_pow_dvd_of_le (by omega) hd
  obtain ⟨y, hy⟩ := scaled_witness (K := K) hh
  refine ⟨y, ?_⟩
  have hs : (2 : K) * (2 : K) ^ (-(δ + J.length + 2)) = (2 : K) ^ (-(δ + J.length + 1)) := by
    calc
      _ = (2 : K) ^ (1 : ℤ) * (2 : K) ^ (-(δ + J.length + 2)) := by rw [zpow_one]
      _ = _ := by
        rw [← zpow_add₀ (by norm_num : (2 : K) ≠ 0)]
        congr 1
        omega
  rw [hy, ← mul_assoc, hs]

/-- Distinct fresh primes avoiding the index give the two required weight
contributions. This is a finite set calculation (provenance (c)). -/
theorem two_fresh_weight {n q r : ℕ} {U : Finset ℕ} (hn : n ≠ 0)
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hqn : ¬ q ∣ n) (hrn : ¬ r ∣ n) (hqU : q ∉ U) (hrU : r ∉ U) :
    2 ≤ (oddPart (r * (q * n)) \ U).card := by
  have hrq : ¬ r ∣ q := fun h => hqr ((Nat.prime_dvd_prime_iff_eq hr hq).mp h).symm
  rw [oddPart_mul_prime hr (mul_ne_zero hq.ne_zero hn)
    (fun h => (hr.dvd_mul.mp h).elim hrq hrn), oddPart_mul_prime hq hn hqn]
  have hsub : ({q, r} : Finset ℕ) ⊆ insert r (insert q (oddPart n)) \ U := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [hqU, hrU]
  simpa [hqr] using Finset.card_le_card hsub

/-- Multiply by the ordinary theta series, retaining the exact integral
divisibility before reduction at the coefficient place. -/
theorem timesTheta_congr (H : ℕ → O) (n : ℕ) :
    (2 : O) ∣ ThetaCoeff.timesTheta H n - H n := by
  refine ⟨∑ k ∈ (Finset.Icc 1 n).filter (fun k => k ^ 2 ≤ n), H (n - k ^ 2), ?_⟩
  unfold ThetaCoeff.timesTheta
  ring

/-- At the coefficient level the parity-adjusted unary correction is
supported exactly on its sieved square shell. -/
def unaryCoeff (good : ℕ → Prop) (η : ℕ → O) (i : Fin 2) (j n : ℕ) : O := by
  classical
  exact if h : ∃ m : ℕ, m ≠ 0 ∧ (∀ p ∈ m.primeFactors, good p) ∧ n = j * m ^ 2
    then η h.choose * (ThetaCoeff.unaryWeight i h.choose : O) else 0

private theorem unary_shell (i : Fin 2) {j m : ℕ} (hj : 0 < j) (hm : m ≠ 0)
    (hgood : ∀ p ∈ m.primeFactors, good p) :
    unaryCoeff good η i j (j * m ^ 2) = η m * (ThetaCoeff.unaryWeight i m : O) := by
  classical
  let h : ∃ t : ℕ, t ≠ 0 ∧ (∀ p ∈ t.primeFactors, good p) ∧ j * m ^ 2 = j * t ^ 2 :=
    ⟨m, hm, hgood, rfl⟩
  rw [unaryCoeff, dite_eq_left h]
  have he : m = h.choose := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
    (Nat.eq_of_mul_eq_mul_left hj h.choose_spec.2.2)
  rw [← he]

private theorem unaryWeight_odd (i : Fin 2) (m : ℕ) (hm : Odd m) :
    Odd (ThetaCoeff.unaryWeight i m) := by
  have hg : Int.gcd (-1) (m : ℤ) = 1 := by simp [Int.gcd]
  rcases jacobiSym.eq_one_or_neg_one hg with h | h
  · simpa [ThetaCoeff.unaryWeight, h] using (show Odd (m : ℤ) by exact_mod_cast hm)
  · have ho : Odd (-1 : ℤ) := by decide
    simpa only [ThetaCoeff.unaryWeight, h] using (ho.pow.mul (show Odd (m : ℤ) by exact_mod_cast hm) :
      Odd ((-1 : ℤ) ^ i.val * (m : ℤ)))

private theorem raw_zero (hz : a 0 = 0) (J : List ℕ) : TL η J a 0 = 0 := by
  induction J with
  | nil => exact hz
  | cons p J ih => simp [TL_cons, Odd.Top, divCoeff, ih]

private theorem raw_support (hc : SourceCore η good adm ap a) {p : ℕ} (hp : p.Prime)
    (hbad : ¬ good p) (J : List ℕ) (hg : ∀ q ∈ J, good q) {n : ℕ} (hn : p ∣ n) :
    TL η J a n = 0 := by
  have ha : ∀ n, p ∣ n → a n = 0 := by
    intro n hd
    rcases eq_or_ne n 0 with rfl | h
    · exact hc.zero
    · exact hc.support n ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hd, h⟩, hbad⟩
  induction J generalizing n with
  | nil => exact ha n hn
  | cons q J ih =>
    have hq := hg q (by simp)
    have hqp : ¬ p ∣ q := fun hd => hbad
      (((Nat.prime_dvd_prime_iff_eq hp (hc.prime q hq)).mp hd).symm ▸ hq)
    have ht {m : ℕ} : p ∣ m → TL η J a m = 0 := ih (fun k hk => hg k (by simp [hk]))
    rw [TL_cons, Odd.Top, ht (dvd_mul_of_dvd_right hn _), divCoeff]
    split_ifs with hd
    · have hpn : p ∣ q * (n / q) := by rwa [Nat.mul_div_cancel' hd]
      rw [ht ((hp.dvd_mul.mp hpn).resolve_left hqp), mul_zero, sub_zero]
    · simp

def rawNumerator (good : ℕ → Prop) (η : ℕ → O) (a : ℕ → O)
    (i : Fin 2) (J : List ℕ) (n : ℕ) : O :=
  TL η J a n - ∑ j ∈ ThetaCoeff.subscripts J.toFinset, TL η J a j * unaryCoeff good η i j n

theorem rawNumerator_off (i : Fin 2) (J : List ℕ) (hp : ∀ p ∈ J, p.Prime)
    {n : ℕ} (hn : ¬ oddPart n ⊆ J.toFinset) :
    rawNumerator good η a i J n = TL η J a n := by
  unfold rawNumerator
  rw [Finset.sum_eq_zero, sub_zero]
  intro j hj
  rw [unaryCoeff, dite_eq_right, mul_zero]
  rintro ⟨m, hm, _, rfl⟩
  obtain ⟨hj, hjJ⟩ := (ThetaCoeff.mem_subscripts (fun p h => hp p (List.mem_toFinset.mp h)) j).mp hj
  exact hn (by simpa only [oddPart_mul_sq hj.ne_zero hm, oddPart_of_squarefree hj] using hjJ)

/-- The entire unary-subtracted numerator pays the exact power of the
integer two, including zero and the indices removed by the sieve. -/
theorem rawNumerator_dvd (H : ∀ t, SourceHyp t δ η good adm ap a)
    (i : Fin 2) (J : List ℕ) (hJ : J.Nodup) (hg : ∀ p ∈ J, good p) (n : ℕ) :
    (2 : O) ^ (δ + J.length + 1).toNat ∣ rawNumerator good η a i J n := by
  classical
  let hc := (H 0).toSourceCore
  have hmem := ThetaCoeff.mem_subscripts (U := J.toFinset)
    (fun p h => hc.prime p (hg p (List.mem_toFinset.mp h)))
  by_cases hn : n = 0
  · subst n
    unfold rawNumerator
    rw [raw_zero hc.zero, Finset.sum_eq_zero, sub_zero]
    · exact dvd_zero _
    · intro j hj
      rw [unaryCoeff, dite_eq_right, mul_zero]
      rintro ⟨m, hm, _, he⟩
      exact (mul_ne_zero ((hmem j).mp hj).1.ne_zero (pow_ne_zero _ hm)) he.symm
  by_cases hnJ : oddPart n ⊆ J.toFinset
  · obtain ⟨m, j, he, hj⟩ := exists_sq_mul_squarefree n
    rw [mul_comm] at he
    have hm : m ≠ 0 := by rintro rfl; simp at he; exact hn he.symm
    have hs : oddPart n = j.primeFactors := by rw [← he, oddPart_mul_sq hj.ne_zero hm, oddPart_of_squarefree hj]
    have hjJ : j ∈ ThetaCoeff.subscripts J.toFinset := (hmem j).mpr ⟨hj, hs ▸ hnJ⟩
    unfold rawNumerator
    rw [Finset.sum_eq_single j]
    · by_cases hmG : ∀ p ∈ m.primeFactors, good p
      · have hmOdd : Odd m := by
          rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
          intro hd
          have hh := hc.odd 2 (hmG 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd, hm⟩))
          exact (by decide : ¬ Odd (2 : ℤ)) (by simpa using hh)
        rw [← he, unary_shell i (Nat.pos_of_ne_zero hj.ne_zero) hm hmG]
        exact raw_shell_bound H J hJ hg (ThetaCoeff.unaryWeight i) (unaryWeight_odd i)
          hj.ne_zero hm hmOdd (by rwa [oddPart_of_squarefree hj, ← hs]) hmG
      · have hbad := hmG
        push Not at hbad
        obtain ⟨p, hp, hb⟩ := hbad
        have hpk := Nat.mem_primeFactors.mp hp
        rw [raw_support hc hpk.1 hb J hg
          (he ▸ dvd_mul_of_dvd_right (dvd_pow hpk.2.1 (by decide : (2 : ℕ) ≠ 0)) j),
          unaryCoeff, dite_eq_right]
        · simp
        · rintro ⟨t, _, ht, ht'⟩
          have e : m = t := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
            (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hj.ne_zero) (he.trans ht'))
          exact hmG (e ▸ ht)
    · intro l hl hlj
      rw [unaryCoeff, dite_eq_right, mul_zero]
      rintro ⟨t, ht, _, ht'⟩
      have hl' := ((hmem l).mp hl).1
      have h : oddPart n = l.primeFactors := by
        rw [ht', oddPart_mul_sq hl'.ne_zero ht, oddPart_of_squarefree hl']
      apply hlj
      rw [← Nat.prod_primeFactors_of_squarefree hl', ← Nat.prod_primeFactors_of_squarefree hj, ← h, hs]
    · exact fun h => (h hjJ).elim
  · rw [rawNumerator_off i J (fun p hp => hc.prime p (hg p hp)) hnJ]
    have hpos : 0 < (oddPart n \ J.toFinset).card := by
      rw [Finset.card_pos]
      obtain ⟨p, hp, hnot⟩ := Finset.not_subset.mp hnJ
      exact ⟨p, Finset.mem_sdiff.mpr ⟨hp, hnot⟩⟩
    exact two_pow_dvd_of_le (by omega) (raw_bound H J hJ hg n)

def dividedCoeff (H : ∀ t, SourceHyp t δ η good adm ap a)
    (i : Fin 2) (J : List ℕ) (hJ : J.Nodup) (hg : ∀ p ∈ J, good p) (n : ℕ) : O :=
  (2 : O) ^ (-(δ + J.length + 1)).toNat * (rawNumerator_dvd H i J hJ hg n).choose

theorem dividedCoeff_spec (H : ∀ t, SourceHyp t δ η good adm ap a)
    (i : Fin 2) (J : List ℕ) (hJ : J.Nodup) (hg : ∀ p ∈ J, good p) (n : ℕ) :
    algebraMap O K (dividedCoeff H i J hJ hg n) =
      (2 : K) ^ (-(δ + J.length + 1)) * algebraMap O K (rawNumerator good η a i J n) := by
  let e : ℤ := δ + J.length + 1
  let h := rawNumerator_dvd H i J hJ hg n
  change algebraMap O K ((2 : O) ^ (-e).toNat * h.choose) =
    (2 : K) ^ (-e) * algebraMap O K (rawNumerator good η a i J n)
  calc
    _ = (2 : K) ^ ((-e).toNat : ℤ) * algebraMap O K h.choose := by
      rw [map_mul, map_pow, map_ofNat, zpow_natCast]
    _ = (2 : K) ^ (-e) * ((2 : K) ^ e.toNat * algebraMap O K h.choose) := by
      rw [← zpow_natCast, ← mul_assoc, ← zpow_add₀ (by norm_num : (2 : K) ≠ 0)]
      congr 2
      omega
    _ = _ := by
      have hh := congrArg (algebraMap O K) h.choose_spec
      rw [map_mul, map_pow, map_ofNat] at hh
      exact congrArg ((2 : K) ^ (-e) * ·) hh.symm



end ZInQ.Manuscript.RC.EvenBudget
