import ZInQKernel.Contrib.OneProof.RC.EvenPlace.Source
import ZInQKernel.Contrib.OneProof.RC.KSplit.Coefficients

/-! The exact App G indexing of (O.9)–(O.11) at depth zero. The good-prime
domain and the unary cutoff use the same support, as at tex 9618–9632. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenPlace

open ZInQ.Manuscript.RC.Odd KSplit

private theorem shell_indices_unique {d J m t : ℕ} (hd : Squarefree d) (hJ : Squarefree J)
    (hm : m ≠ 0) (ht : t ≠ 0) (he : d * m ^ 2 = J * t ^ 2) :
    d = J ∧ m = t := by
  have h := congrArg oddPart he
  rw [oddPart_mul_sq hd.ne_zero hm, oddPart_mul_sq hJ.ne_zero ht,
    oddPart_of_squarefree hd, oddPart_of_squarefree hJ] at h
  have hdJ : d = J := by
    rw [← Nat.prod_primeFactors_of_squarefree hd, ← Nat.prod_primeFactors_of_squarefree hJ, h]
  subst J
  exact ⟨rfl, Nat.pow_left_injective (by decide : 2 ≠ 0)
    (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd.ne_zero) he)⟩

private theorem unary_on_shell (η : ℕ → ℂ) (M : ℕ) {J d m : ℕ}
    (hJ : Squarefree J) (hd : Squarefree d) (hm : m ≠ 0) :
    unaryTheta η M J (d * m ^ 2) =
      if J = d ∧ m.Coprime M then η m * (m : ℂ) else 0 := by
  classical
  by_cases h : J = d ∧ m.Coprime M
  · obtain ⟨rfl, hc⟩ := h
    rw [ite_eq_left ⟨rfl, hc⟩]
    exact unaryTheta_eq_single η M (Nat.pos_of_ne_zero hd.ne_zero) (Nat.pos_of_ne_zero hm)
      hc rfl (fun t ht he => (shell_indices_unique hd hd hm ht.ne' he.symm).2.symm)
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro t ht
    simp only [Finset.mem_filter] at ht
    obtain ⟨hdJ, hmt⟩ := shell_indices_unique hd hJ hm ht.2.1.ne' ht.2.2.2.symm
    exact (h ⟨hdJ.symm, hmt ▸ ht.2.2.1⟩).elim

private theorem mem_of_dvd {O : Subring ℂ} {e z : O} (he : (e : ℂ) ≠ 0)
    {b : ℂ} (h : e ∣ z) (hb : (e : ℂ) * b = (z : ℂ)) : b ∈ O := by
  obtain ⟨y, hy⟩ := h
  have h' : b = (y : ℂ) := mul_left_cancel₀ he (hb.trans (congrArg O.subtype hy))
  exact h' ▸ y.property

/-- The source produced by the shell recurrence can be used directly
with App G's exact singleton operators, at every index including zero.
The prime support of `M` is that of the Fourier sieve. -/
theorem singleton_divisions {O : Subring ℂ} {M p : ℕ} (hM : 2 ∣ M)
    {a χ : ℕ → O} {adm : ℕ → Prop} {ap : ℕ → ℤ}
    (H : SourceHyp 2 0 χ (fun q => q.Prime ∧ q.Coprime M) adm ap a)
    (hp : p.Prime) (hpM : p.Coprime M) (n : ℕ) :
    Bp (fun j => (a j : ℂ)) (χ p : ℂ) p n ∈ O ∧
    Hp (fun j => (a j : ℂ)) (fun j => (χ j : ℂ)) M p n ∈ O := by
  classical
  let A := fun j : ℕ => (a j : ℂ)
  let E := fun j : ℕ => (χ j : ℂ)
  let B := Bp A (E p) p
  let T := TL χ [p] a
  change B n ∈ O ∧ Hp A E M p n ∈ O
  have hL : ∀ q ∈ ([p] : List ℕ), q.Prime ∧ q.Coprime M := by
    simpa using And.intro hp hpM
  have hnd : ([p] : List ℕ).Nodup := by simp
  have he (j : ℕ) : (2 : ℂ) * B j = (T j : ℂ) := by
    change 2 * ((A (p * j) - E p * (if p ∣ j then A (j / p) else 0)) / 2) =
      O.subtype (a (p * j) - χ p * divCoeff a p j)
    rw [map_sub, map_mul, ← divCoeff_map]
    change 2 * ((A (p * j) - E p * (if p ∣ j then A (j / p) else 0)) / 2) =
      A (p * j) - E p * divCoeff A p j
    unfold divCoeff
    ring
  have hb (j : ℕ) : (2 : O) ∣ T j := by
    have h := O9 H [p] hnd hL j
    have hle : 1 ≤ (min (2 : ℤ)
        (0 + ([p] : List ℕ).length + (oddPart j \ ([p] : List ℕ).toFinset).card)).toNat := by
      simp only [List.length_singleton, Nat.cast_one, zero_add]
      omega
    simpa only [pow_one] using (pow_dvd_pow (2 : O) hle).trans h
  refine ⟨mem_of_dvd (by norm_num : ((2 : O) : ℂ) ≠ 0) (hb n) (he n), ?_⟩
  have hh : (4 : ℂ) * Hp A E M p n =
      (T n : ℂ) - (T 1 : ℂ) * unaryTheta E M 1 n - (T p : ℂ) * unaryTheta E M p n := by
    unfold Hp
    change 4 * ((B n - B 1 * unaryTheta E M 1 n - B p * unaryTheta E M p n) / 2) = _
    linear_combination he n - unaryTheta E M 1 n * he 1 - unaryTheta E M p n * he p
  have hfour : ((4 : O) : ℂ) = 4 := by
    exact map_ofNat O.subtype 4
  have hTzero : T 0 = 0 := by simp [T, TL, Odd.Top, divCoeff, H.zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hθ (J : ℕ) (hJ : J ≠ 0) : unaryTheta E M J 0 = 0 :=
      unaryTheta_eq_zero E M fun m hm => mul_ne_zero hJ (pow_ne_zero _ hm.ne')
    rw [hTzero, hθ 1 one_ne_zero, hθ p hp.ne_zero] at hh
    exact mem_of_dvd (by norm_num : ((4 : O) : ℂ) ≠ 0) (dvd_zero (4 : O))
      (by simpa using hh)
  obtain ⟨m, d, hdm, hd⟩ := exists_sq_mul_squarefree n
  have hm : m ≠ 0 := fun hz => hn.ne' (by simpa [hz] using hdm.symm)
  have hdm' : d * m ^ 2 = n := (mul_comm _ _).trans hdm
  rw [← hdm'] at hh ⊢
  rw [unary_on_shell E M squarefree_one hd hm, unary_on_shell E M hp.squarefree hd hm] at hh
  have hgood (hc : m.Coprime M) : ∀ q ∈ m.primeFactors, q.Prime ∧ q.Coprime M := by
    intro q hq
    obtain ⟨hq, hdq, _⟩ := Nat.mem_primeFactors.mp hq
    exact ⟨hq, hc.coprime_dvd_left hdq⟩
  have hmodd (hc : m.Coprime M) : Odd m :=
    Nat.not_even_iff_odd.mp (even_iff_two_dvd.not.mpr (fun hd =>
      (Nat.prime_two.coprime_iff_not_dvd.mp (hc.coprime_dvd_left hd)) hM))
  have hdvd (hc : m.Coprime M) (hJ : oddPart d ⊆ ([p] : List ℕ).toFinset) :
      (4 : O) ∣ T (d * m ^ 2) - T d * (χ m * (m : O)) := by
    have h := O11_theta H [p] hnd hL (fun m => (m : ℤ)) (fun _ h => by exact_mod_cast h)
      hd.ne_zero hm (hmodd hc) hJ (hgood hc)
    simpa [T, show (2 : O) ^ 2 = 4 by norm_num] using h
  have hcast : ((χ m * (m : O) : O) : ℂ) = E m * (m : ℂ) := by simp [E]
  by_cases hc : m.Coprime M
  · by_cases h1 : d = 1
    · subst d
      rw [ite_eq_left ⟨rfl, hc⟩, ite_eq_right (fun h => hp.ne_one h.1)] at hh
      refine mem_of_dvd (by norm_num : ((4 : O) : ℂ) ≠ 0) (hdvd hc (by simp [oddPart])) ?_
      change O.subtype 4 * Hp A E M p (1 * m ^ 2) =
        O.subtype (T (1 * m ^ 2) - T 1 * (χ m * (m : O)))
      rw [map_sub, map_mul]
      simpa only [Subring.coe_subtype, hfour, hcast, mul_zero, sub_zero] using hh
    · by_cases hdp : d = p
      · subst d
        rw [ite_eq_right (fun h => hp.ne_one h.1.symm), ite_eq_left ⟨rfl, hc⟩] at hh
        refine mem_of_dvd (by norm_num : ((4 : O) : ℂ) ≠ 0)
          (hdvd hc (by simp [oddPart_of_squarefree hp.squarefree, hp.primeFactors])) ?_
        change O.subtype 4 * Hp A E M p (p * m ^ 2) =
          O.subtype (T (p * m ^ 2) - T p * (χ m * (m : O)))
        rw [map_sub, map_mul]
        simpa only [Subring.coe_subtype, hfour, hcast, mul_zero, sub_zero] using hh
      · have hj : ¬ oddPart (d * m ^ 2) ⊆ ([p] : List ℕ).toFinset := by
          rw [oddPart_mul_sq hd.ne_zero hm, oddPart_of_squarefree hd]
          intro h
          by_cases h' : p ∈ d.primeFactors
          · have heq : d.primeFactors = {p} :=
              Finset.Subset.antisymm (by simpa using h) (Finset.singleton_subset_iff.mpr h')
            apply hdp
            rw [← Nat.prod_primeFactors_of_squarefree hd, heq, Finset.prod_singleton]
          · apply h1
            have heq : d.primeFactors = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun q hq => by
              have he : q = p := by simpa using h hq
              exact h' (he ▸ hq))
            rw [← Nat.prod_primeFactors_of_squarefree hd, heq, Finset.prod_empty]
        have h := O11_offJ H [p] hnd hL hj
        have hdv : (4 : O) ∣ T (d * m ^ 2) := by
          simpa [T, show (2 : O) ^ 2 = 4 by norm_num] using h
        exact mem_of_dvd (by norm_num : ((4 : O) : ℂ) ≠ 0) hdv
          (by simpa [hfour, Ne.symm h1, Ne.symm hdp] using hh)
  · have hgcd : m.gcd M ≠ 1 := fun h => hc ((Nat.coprime_iff_gcd_eq_one).mpr h)
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hgcd
    have hqM := hqd.trans (Nat.gcd_dvd_right m M)
    have hqm := hqd.trans (Nat.gcd_dvd_left m M)
    have hqn : q ∣ d * m ^ 2 :=
      dvd_mul_of_dvd_right (hqm.trans (dvd_pow_self m (by decide))) d
    have az (j : ℕ) (hj : q ∣ j) : a j = 0 := by
      by_cases hzero : j = 0
      · rw [hzero, H.zero]
      exact H.support j ⟨q, Nat.mem_primeFactors.mpr ⟨hq, hj, hzero⟩,
        fun hg => (hq.coprime_iff_not_dvd.mp hg.2) hqM⟩
    have ht : T (d * m ^ 2) = 0 := by
      have hn' : ¬ q ∣ p := fun h =>
        (hp.coprime_iff_not_dvd.mp hpM) (((Nat.prime_dvd_prime_iff_eq hq hp).mp h) ▸ hqM)
      simp only [T, TL, Odd.Top, divCoeff, az _ (dvd_mul_of_dvd_right hqn p)]
      split_ifs with hpd
      · have he := Nat.mul_div_cancel' hpd
        have hw : q ∣ p * (d * m ^ 2 / p) := he.symm ▸ hqn
        rw [az _ ((hq.dvd_mul.mp hw).resolve_left hn'), mul_zero, sub_zero]
      · simp
    simp only [hc, and_false, ite_false, ht, ZeroMemClass.coe_zero, mul_zero, sub_zero] at hh
    exact mem_of_dvd (by norm_num : ((4 : O) : ℂ) ≠ 0) (dvd_zero (4 : O)) hh

/-- The direct singleton handoff on complex Fourier coefficients.
The recurrence may be supplied by `evenCoeff_shell`; its squarefree
factor is the ordinary depth-zero bound, with no no-unit hypothesis. -/
theorem singleton_of_shell {O : Subring ℂ} {M : ℕ} (hM : 2 ∣ M)
    {a η : ℕ → ℂ} {adm : ℕ → Prop} {ap : ℕ → ℤ}
    (hη : ∀ n, η n ∈ O) (hηmul : ∀ x y, η (x * y) = η x * η y) (hηone : η 1 = 1)
    (hap : ∀ p, p.Prime → p.Coprime M → ap p ≡ p + 1 [ZMOD 4])
    (hzero : a 0 = 0)
    (hsupp : ∀ n, ¬ n.Coprime M → a n = 0)
    (hoff : ∀ n, Squarefree n → ¬ adm n → a n = 0)
    (hbase : ∀ n, Squarefree n → adm n → ∃ y ∈ O, a n = (2 : ℂ) ^ n.primeFactors.card * y)
    (hrec : ∀ (q : ℕ) (hq : q.Prime), q.Coprime M →
      let : Fact q.Prime := ⟨hq⟩
      ShellRecurrence a (η q) (η q * ((legendreSym q (-1) : ℤ) : ℂ)) (ap q) q)
    {p : ℕ} (hp : p.Prime) (hpM : p.Coprime M) (n : ℕ) :
    Bp a (η p) p n ∈ O ∧ Hp a η M p n ∈ O := by
  have hodd : ∀ q : ℕ, q.Prime ∧ q.Coprime M → Odd (q : ℤ) := by
    rintro q ⟨hq, hqM⟩
    exact_mod_cast hq.odd_of_ne_two (fun he => (hq.coprime_iff_not_dvd.mp hqM) (he ▸ hM))
  have hbad : ∀ j, (∃ q ∈ j.primeFactors, ¬ (q.Prime ∧ q.Coprime M)) → a j = 0 := by
    rintro j ⟨q, hq, hn⟩
    obtain ⟨hq, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    exact hsupp j (fun h => hn ⟨hq, h.coprime_dvd_left hqd⟩)
  have hsf : ∀ j, Squarefree j → adm j → ∃ y ∈ O,
      a j = (2 : ℂ) ^ (0 + ArithmeticFunction.cardDistinctFactors j : ℤ).toNat * y := by
    intro j hj ha
    simpa [← card_oddPart_of_squarefree hj, oddPart_of_squarefree hj] using hbase j hj ha
  have hr : ∀ (q : ℕ) (hq : q.Prime), (q.Prime ∧ q.Coprime M) → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      @RecAt ℂ _ q ⟨hq⟩ (η q) ε (ap q) a := by
    intro q hq hg
    let : Fact q.Prime := ⟨hq⟩
    have hm : ((-1 : ℤ) : ZMod q) ≠ 0 := by simp
    have hε := legendreSym.eq_one_or_neg_one q hm
    refine ⟨legendreSym q (-1), hε, fun j => ?_⟩
    have h := hrec q hq hg.2 j
    rw [h]
    unfold divCoeff
    push_cast
    ring
  obtain ⟨b, χ, hb, hχ, H⟩ := sourceHyp_of_complex O hη hηmul hηone
    (fun _ hg => hg.1) hodd (fun j hj => hap j hj.1 hj.2) hzero hbad hoff hsf hr
  rw [← funext hb, ← funext hχ]
  exact singleton_divisions hM (H 2) hp hpM n

end ZInQ.Manuscript.RC.EvenPlace
