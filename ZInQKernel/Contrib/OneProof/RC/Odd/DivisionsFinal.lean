import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Odd.DivisionsMain

/-!
# Lane RC12-odd: (O.9) and (O.11) as statements; the fresh reading; the omission coefficient

Manuscript (11/5), Appendix F, proof of Proposition `ex:app-coefficient-rules`:
* (O.9) (tex 9570–9584) — `O9`;
* (O.11) (tex 9618–9636) — `O11_cong`, `O11_offJ`, `O11_theta`;
* the fresh coefficient-one reading `B_U[q] = 2^{−n_U} a(uq)`, `H_U[q] = 2^{−n_U−1} a(uq)`
  (tex 9681–9687) — `TL_fresh`, `theta_index_ne_fresh`;
* the omission coefficient `H_U[pr] ≡ η(p) C_p(vr) 2^{−n_V−1} a(vr)`, an equality before reduction
  for the even source (tex 9905–9918) — `TL_omission`.
All statements are PROVED.
-/

namespace ZInQ.Manuscript.RC.Odd

variable {R : Type*} [CommRing R]

/-- `∏_{p∈U}(U_p − η(p)V_p)` applied to `a`, for a list `U` of primes (by `Top_comm` the result
depends only on the set when the primes are distinct). -/
def TL (χ : ℕ → R) : List ℕ → (ℕ → R) → (ℕ → R)
  | [], a => a
  | p :: L, a => Top p (χ p) (TL χ L a)

@[simp] theorem TL_nil (χ : ℕ → R) (a : ℕ → R) : TL χ [] a = a := rfl
@[simp] theorem TL_cons (χ : ℕ → R) (p : ℕ) (L : List ℕ) (a : ℕ → R) :
    TL χ (p :: L) a = Top p (χ p) (TL χ L a) := rfl

variable {T : ℕ} {δ : ℤ} {χ : ℕ → R} {G : ℕ → Prop} {adm : ℕ → Prop} {ap : ℕ → ℤ} {a : ℕ → R}

/-- **PROVED (the depth at every Fourier index; tex 9471–9476, 9558–9569, 9607–9613).** From the depth
at the squarefree parameters of the stage support, the vanishing off the support and the recurrence
(O.6) at the good primes: `v₂ a(n) ≥ min(T, δ + |oddPart n|)` at every index `n`. A square of a good
prime is removed by the shell formulas (`rec_even`, `rec_odd`), which do not change the primes with
odd exponent; an index divisible by a prime of the support, or a squarefree index outside the stage
support, has coefficient zero. This is the reading of "Its depth bound" in tex 9610–9613 for the
squarefree input `D` of an index. -/
theorem SourceHyp.depth_all (H : SourceHyp T δ χ G adm ap a) (n : ℕ) :
    (2 : R) ^ (min (T : ℤ) (δ + (oddPart n).card)).toNat ∣ a n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [H.zero]; exact dvd_zero _
  by_cases hsq : Squarefree n
  · by_cases hadm : adm n
    · have := H.depth n hsq hadm
      rwa [← card_oddPart_of_squarefree hsq] at this
    · rw [H.support_adm n hsq hadm]; exact dvd_zero _
  obtain ⟨p, hp, hp2⟩ : ∃ p, p.Prime ∧ p * p ∣ n := by
    have := Nat.squarefree_iff_prime_squarefree.not.mp hsq
    push Not at this
    exact this
  by_cases hpG : G p
  · obtain ⟨ε, hε, hrec⟩ := H.recur p hpG
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, n', hpn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.ne_one
    have hn' : n' ≠ 0 := by rintro rfl; simp at hn
    have hk2 : 2 ≤ k := by
      by_contra hk
      interval_cases k
      · rw [pow_zero, one_mul] at hp2
        exact hpn' (dvd_trans (dvd_mul_left p p) hp2)
      · rw [pow_one] at hp2
        exact hpn' (Nat.dvd_of_mul_dvd_mul_left hp.pos hp2)
    have hp1 : 1 < p := hp.one_lt
    obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' k
    · rw [rec_even hrec hpn' s, oddPart_pow_even_mul hp hn' hpn']
      apply dvd_mul_of_dvd_right
      apply ih n'
      have : 1 < p ^ (2 * s) := Nat.one_lt_pow (by omega) hp1
      have hn'0 : 0 < n' := Nat.pos_of_ne_zero hn'
      nlinarith
    · rw [rec_odd hrec hpn' s, oddPart_pow_odd_mul hp hn' hpn', ← oddPart_mul_prime hp hn' hpn']
      apply dvd_mul_of_dvd_right
      apply ih (p * n')
      have : p < p ^ (2 * s + 1) := by
        calc p = p ^ 1 := (pow_one p).symm
          _ < p ^ (2 * s + 1) := Nat.pow_lt_pow_right hp1 (by omega)
      have hn'0 : 0 < n' := Nat.pos_of_ne_zero hn'
      nlinarith
  · rw [H.support]
    · exact dvd_zero _
    · refine ⟨p, ?_, hpG⟩
      rw [Nat.mem_primeFactors]
      exact ⟨hp, dvd_trans (dvd_mul_left p p) hp2, hn.ne'⟩

/-- The base: one good prime (tex 9562–9566, 9598–9599). -/
theorem SourceHyp.single (H : SourceHyp T δ χ G adm ap a) {q : ℕ} (hq : G q) {n : ℕ}
    (hn : n ≠ 0) (hqn : q ∉ oddPart n) (t : ℕ) :
    (2 : R) ^ (min (T : ℤ) (δ + (oddPart n).card + 1)).toNat ∣
      a (n * (q ^ t) ^ 2) - χ q ^ t * a n := by
  obtain ⟨ε, hε, hrec⟩ := H.recur q hq
  have : Fact q.Prime := ⟨H.prime q hq⟩
  obtain ⟨k, n'', hqn'', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q (H.prime q hq).ne_one
  have hn'' : n'' ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [oddPart_pow_even_mul (H.prime q hq) hn'' hqn'']
    have hidx : q ^ (2 * s) * n'' * (q ^ t) ^ 2 = q ^ (2 * (s + t)) * n'' := by ring
    rw [hidx, rec_even hrec hqn'' (s + t), rec_even hrec hqn'' s]
    have hκ := legendreSym_neg_eq_one_or hqn'' hε
    have ho1 := odd_shell_kappa_unit hκ (H.odd q hq) (H.ap_mod q hq) (s + t)
    have ho2 := odd_shell_kappa_unit hκ (H.odd q hq) (H.ap_mod q hq) s
    set κ := ε * legendreSym q (-(n'' : ℤ))
    have hev : Even (shell (ap q) q κ (s + t) - shell (ap q) q κ s) := Odd.sub_odd ho1 ho2
    have hexp : χ q ^ (s + t) * (shell (ap q) q κ (s + t) : R) * a n'' -
        χ q ^ t * (χ q ^ s * (shell (ap q) q κ s : R) * a n'') =
        χ q ^ (s + t) * (((shell (ap q) q κ (s + t) - shell (ap q) q κ s : ℤ) : R) * a n'') := by
      push_cast; ring
    rw [hexp]
    exact dvd_mul_of_dvd_right (two_pow_dvd_of_le (by omega)
      (two_pow_dvd_intCast_even_mul hev (H.depth_all n''))) _
  · exfalso; apply hqn
    rw [oddPart_pow_odd_mul (H.prime q hq) hn'' hqn'']
    exact Finset.mem_insert_self _ _

/-- **PROVED.** The invariant holds for the source itself (`U = ∅`). -/
theorem SourceHyp.divInv (H : SourceHyp T δ χ G adm ap a) : DivInv T δ χ G ∅ a := by
  refine ⟨H.zero, fun n => by simpa using H.depth_all n, ?_⟩
  intro n m hn hm hgood hcop
  simp only [Finset.sdiff_empty, Finset.card_empty, Nat.cast_zero, add_zero]
  simp only [Finset.sdiff_empty] at hcop
  have key : ∀ m, m ≠ 0 → (∀ q ∈ m.primeFactors, G q) → ∀ n, n ≠ 0 →
      (∀ q ∈ oddPart n, ¬ q ∣ m) →
      (2 : R) ^ (min (T : ℤ) (δ + (oddPart n).card + 1)).toNat ∣ a (n * m ^ 2) - χ m * a n := by
    intro m
    induction m using Nat.recOnPrimePow with
    | zero => intro h; exact absurd rfl h
    | one => intro _ _ n _ _; simp [H.one]
    | prime_pow_mul m₁ q t hq hqm₁ ht ih =>
      intro hm hgood n hn hcop
      have hm₁ : m₁ ≠ 0 := by rintro rfl; simp at hm
      have hqG : G q := hgood q (by
        rw [Nat.primeFactors_mul (pow_ne_zero _ hq.ne_zero) hm₁, Nat.primeFactors_prime_pow
          (by omega) hq]
        simp)
      have hqn : q ∉ oddPart n := fun h' =>
        hcop q h' (dvd_mul_of_dvd_left (dvd_pow_self q (by omega)) _)
      have hidx : n * (q ^ t * m₁) ^ 2 = (n * (q ^ t) ^ 2) * m₁ ^ 2 := by ring
      have hnq : n * (q ^ t) ^ 2 ≠ 0 := mul_ne_zero hn (pow_ne_zero _ (pow_ne_zero _ hq.ne_zero))
      have h1 := ih hm₁ (fun r hr => hgood r (by
        rw [Nat.primeFactors_mul (pow_ne_zero _ hq.ne_zero) hm₁]
        exact Finset.mem_union_right _ hr)) (n * (q ^ t) ^ 2) hnq (by
        intro r hr hrm
        rw [oddPart_mul_sq hn (pow_ne_zero _ hq.ne_zero)] at hr
        exact hcop r hr (dvd_mul_of_dvd_right hrm _))
      rw [oddPart_mul_sq hn (pow_ne_zero _ hq.ne_zero)] at h1
      have h2 := H.single hqG hn hqn t
      rw [hidx, H.mul, H.pow]
      have : a (n * (q ^ t) ^ 2 * m₁ ^ 2) - χ q ^ t * χ m₁ * a n =
          (a (n * (q ^ t) ^ 2 * m₁ ^ 2) - χ m₁ * a (n * (q ^ t) ^ 2)) +
          χ m₁ * (a (n * (q ^ t) ^ 2) - χ q ^ t * a n) := by ring
      rw [this]
      exact dvd_add h1 (dvd_mul_of_dvd_right h2 _)
  exact key m hm hgood n hn hcop

/-- **PROVED.** The invariant after `∏_{p∈U}(U_p − η(p)V_p)` for a list `U` of distinct good
primes, together with the twisted recurrence at every other good prime. -/
theorem SourceHyp.divInv_TL (H : SourceHyp T δ χ G adm ap a) (L : List ℕ) (hnd : L.Nodup)
    (hL : ∀ p ∈ L, G p) :
    DivInv T δ χ G L.toFinset (TL χ L a) ∧
      ∀ q (hq : G q), q ∉ L → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        @RecAt R _ q ⟨H.prime q hq⟩ (χ q) ε (ap q) (TL χ L a) := by
  induction L with
  | nil => exact ⟨by simpa using H.divInv, fun q hq _ => by simpa using H.recur q hq⟩
  | cons p L ih =>
    have hpL : p ∉ L := (List.nodup_cons.mp hnd).1
    obtain ⟨hinv, hrecs⟩ := ih (List.nodup_cons.mp hnd).2 (fun q hq => hL q (by simp [hq]))
    have hpG : G p := hL p (by simp)
    have : Fact p.Prime := ⟨H.prime p hpG⟩
    obtain ⟨ε, hε, hrec⟩ := hrecs p hpG hpL
    refine ⟨?_, ?_⟩
    · rw [List.toFinset_cons, TL_cons]
      exact hinv.step (by simpa using hpL) (H.odd p hpG) hε (H.ap_mod p hpG) hrec H.mul H.one
    · intro q hq hqpL
      have hqL : q ∉ L := fun h' => hqpL (by simp [h'])
      have hqp : p ≠ q := fun e => hqpL (by simp [e])
      obtain ⟨εq, hεq, hrecq⟩ := hrecs q hq hqL
      have : Fact q.Prime := ⟨H.prime q hq⟩
      refine ⟨εq * legendreSym q p, ?_, ?_⟩
      · have hpq : ¬ q ∣ p := fun h' =>
          hqp ((Nat.prime_dvd_prime_iff_eq (H.prime q hq) (H.prime p hpG)).mp h').symm
        have := legendreSym_neg_eq_one_or (n := p) hpq hεq
        have hneg : legendreSym q (-(p : ℤ)) = legendreSym q (-1) * legendreSym q p := by
          rw [← legendreSym.mul]; ring_nf
        have h0 : ((p : ℤ) : ZMod q) ≠ 0 := by
          intro h0; apply hpq
          exact Int.natCast_dvd_natCast.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h0)
        rcases legendreSym.eq_one_or_neg_one q h0 with h | h <;> rcases hεq with rfl | rfl <;>
          simp [h]
      · rw [TL_cons]; exact hrecq.top hqp (χ p)

/-- **(O.9) (tex 9570–9584), PROVED.** For a list `U` of distinct good primes, at every Fourier
index `n`: `2^{min T (δ + |U| + ω(r))} ∣ (∏_{p∈U}(U_p − η(p)V_p) g)[n]`, where
`ω(r) = #(oddPart n ∖ U)` counts the primes of the squarefree kernel `J r` of `n` outside `U`
(so `v₂ B_U[Jrm²] ≥ ω(r)` with `n_U = δ + |U|`, truncated at `T` for an odd stage). -/
theorem O9 (H : SourceHyp T δ χ G adm ap a) (L : List ℕ) (hnd : L.Nodup) (hL : ∀ p ∈ L, G p)
    (n : ℕ) :
    (2 : R) ^ (min (T : ℤ) (δ + L.length + (oddPart n \ L.toFinset).card)).toNat ∣ TL χ L a n := by
  have := (H.divInv_TL L hnd hL).1.bound n
  rwa [List.toFinset_card_of_nodup hnd] at this

/-- **(O.11), the shell congruence (tex 9626–9627), PROVED.** In matching parity, for `n = J m₁²`
with `J ⊆ U` (i.e. `oddPart n ⊆ U`) and every good `m`:
`B_U[n m²] − η(m) B_U[n] ∈ 2𝒪`, undivided: `2^{min T (n_U + 1)}` divides the difference. -/
theorem O11_cong (H : SourceHyp T δ χ G adm ap a) (L : List ℕ) (hnd : L.Nodup)
    (hL : ∀ p ∈ L, G p) {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hJ : oddPart n ⊆ L.toFinset)
    (hgood : ∀ q ∈ m.primeFactors, G q) :
    (2 : R) ^ (min (T : ℤ) (δ + L.length + 1)).toNat ∣ TL χ L a (n * m ^ 2) - χ m * TL χ L a n := by
  have hsd : oddPart n \ L.toFinset = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hJ
  have := (H.divInv_TL L hnd hL).1.cong n m hn hm hgood (by simp [hsd])
  rwa [hsd, Finset.card_empty, Nat.cast_zero, add_zero, List.toFinset_card_of_nodup hnd] at this

/-- **(O.11), off the unary support (tex 9628–9632), PROVED.** If the squarefree kernel of `n` is
not contained in `U`, then `ω(r) ≥ 1` and `2^{min T (n_U + 1)} ∣ (∏(U_p − η(p)V_p) g)[n]`. -/
theorem O11_offJ (H : SourceHyp T δ χ G adm ap a) (L : List ℕ) (hnd : L.Nodup)
    (hL : ∀ p ∈ L, G p) {n : ℕ} (hJ : ¬ oddPart n ⊆ L.toFinset) :
    (2 : R) ^ (min (T : ℤ) (δ + L.length + 1)).toNat ∣ TL χ L a n := by
  have hpos : 0 < (oddPart n \ L.toFinset).card := by
    rw [Finset.card_pos]
    obtain ⟨q, hq, hqL⟩ := Finset.not_subset.mp hJ
    exact ⟨q, Finset.mem_sdiff.mpr ⟨hq, hqL⟩⟩
  exact two_pow_dvd_of_le (by omega) (O9 H L hnd hL n)

/-- **(O.11), integrality of `H_U = (B_U − ∑_J B_U[J] Θ_J)/2` (tex 9618–9632), PROVED.** For the
unary series `Θ_J = ∑ η(m) χ_{−4}(m)^i m q^{J m²}`, whose coefficient `θ(m)` at `J m²` is an odd
integer times `η(m)`: at every index `J m²` (`J ⊆ U`, `m` good) the undivided numerator of `H_U` is
divisible by `2^{min T (n_U + 1)}`. -/
theorem O11_theta (H : SourceHyp T δ χ G adm ap a) (L : List ℕ) (hnd : L.Nodup)
    (hL : ∀ p ∈ L, G p) (θ : ℕ → ℤ) (hθ : ∀ m, Odd m → Odd (θ m))
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hmodd : Odd m) (hJ : oddPart n ⊆ L.toFinset)
    (hgood : ∀ q ∈ m.primeFactors, G q) :
    (2 : R) ^ (min (T : ℤ) (δ + L.length + 1)).toNat ∣
      TL χ L a (n * m ^ 2) - TL χ L a n * (χ m * (θ m : R)) := by
  have h1 := O11_cong H L hnd hL hn hm hJ hgood
  have h2 := O9 H L hnd hL n
  rw [Finset.sdiff_eq_empty_iff_subset.mpr hJ, Finset.card_empty, Nat.cast_zero, add_zero] at h2
  have hev : Even (1 - θ m) := Odd.sub_odd odd_one (hθ m hmodd)
  have : TL χ L a (n * m ^ 2) - TL χ L a n * (χ m * (θ m : R)) =
      (TL χ L a (n * m ^ 2) - χ m * TL χ L a n) +
        ((1 - θ m : ℤ) : R) * (χ m * TL χ L a n) := by push_cast; ring
  rw [this]
  exact dvd_add h1 (two_pow_dvd_of_le (by omega)
    (two_pow_dvd_intCast_even_mul hev (dvd_mul_of_dvd_right h2 _)))

/-- **The fresh reading (tex 9681–9686), PROVED.** For an index `n` prime to every `p ∈ U`:
`(∏_{p∈U}(U_p − η(p)V_p) g)[n] = a(u n)`, `u = ∏_{p∈U} p` (every term containing a `V_p` vanishes);
so `B_U[q] = 2^{−n_U} a(uq)` at a fresh prime `q`. -/
theorem TL_fresh (χ : ℕ → R) (a : ℕ → R) (L : List ℕ) (hL : ∀ p ∈ L, p.Prime) (hnd : L.Nodup)
    {n : ℕ} (hn : ∀ p ∈ L, ¬ p ∣ n) : TL χ L a n = a (L.prod * n) := by
  induction L generalizing n with
  | nil => simp
  | cons p L ih =>
    have hp : p.Prime := hL p (by simp)
    rw [TL_cons, Top_of_not_dvd _ (hn p (by simp)), ih (fun q hq => hL q (by simp [hq]))
      (List.nodup_cons.mp hnd).2]
    · rw [List.prod_cons]; ring_nf
    · intro q hq hqd
      have hqp : q ≠ p := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hq)
      rcases (Nat.Prime.dvd_mul (hL q (by simp [hq]))).mp hqd with h | h
      · exact hqp ((Nat.prime_dvd_prime_iff_eq (hL q (by simp [hq])) hp).mp h)
      · exact hn q (by simp [hq]) h

/-- **PROVED (tex 9682–9683).** No unary index `J m²` with `J ⊆ U` equals a fresh prime `q ∉ U`:
`oddPart (J m²) ⊆ U` fails at `q`. -/
theorem theta_index_ne_fresh {q : ℕ} (hq : q.Prime) {U : Finset ℕ} (hqU : q ∉ U) :
    ¬ oddPart q ⊆ U := by
  intro h
  apply hqU
  apply h
  rw [mem_oddPart, hq.factorization_self]
  exact odd_one

/-- **The omission coefficient (tex 9905–9916), PROVED.** For `U = {p} ∪ V` (`p` applied last),
a fresh prime `r` (prime to `p` and to `V`): the coefficient at `pr` is
`(∏_{U}(U_p − η(p)V_p) g)[pr] = η(p) (a_p − (ψ/η)(p)(−vr/p) − 1) a(vr) = η(p)·2C_p(vr)·a(vr)`,
an equality before reduction; dividing by `2^{n_U + 1} = 2^{n_V + 2}` gives
`H_U[pr] = η(p) C_p(vr) 2^{−n_V−1} a(vr)`. -/
theorem TL_omission (χ : ℕ → R) (a : ℕ → R) {p : ℕ} [hp : Fact p.Prime] {ε app : ℤ}
    (hrec : RecAt p (χ p) ε app a) (V : List ℕ) (hV : ∀ q ∈ V, q.Prime) (hnd : V.Nodup)
    (hpV : p ∉ V) {r : ℕ} (hpr : ¬ p ∣ r) (hVr : ∀ q ∈ V, ¬ q ∣ r) :
    TL χ (p :: V) a (p * r) =
      χ p * ((app - ε * legendreSym p (-((V.prod * r : ℕ) : ℤ)) - 1 : ℤ) : R) * a (V.prod * r) := by
  have hp0 : 0 < p := hp.out.pos
  have hcopV : ∀ q ∈ V, ¬ q ∣ p := fun q hq h' =>
    hpV (((Nat.prime_dvd_prime_iff_eq (hV q hq) hp.out).mp h') ▸ hq)
  have hpVr : ¬ p ∣ V.prod * r := by
    intro h'
    rcases (Nat.Prime.dvd_mul hp.out).mp h' with h1 | h1
    · obtain ⟨q, hq, hpq⟩ := (Prime.dvd_prod_iff hp.out.prime).mp h1
      exact hcopV q hq (by rw [(Nat.prime_dvd_prime_iff_eq hp.out (hV q hq)).mp hpq])
    · exact hpr h1
  rw [TL_cons]
  simp only [Top]
  rw [divCoeff_mul_left _ hp0]
  rw [TL_fresh χ a V hV hnd hVr, TL_fresh χ a V hV hnd (by
    intro q hq hqd
    rcases (Nat.Prime.dvd_mul (hV q hq)).mp hqd with h1 | h1
    · exact hcopV q hq h1
    · rcases (Nat.Prime.dvd_mul (hV q hq)).mp h1 with h2 | h2
      · exact hcopV q hq h2
      · exact hVr q hq h2)]
  rw [show V.prod * (p * (p * r)) = p ^ 2 * (V.prod * r) by ring, hrec (V.prod * r),
    divCoeff_of_not_dvd a (not_sq_dvd_of_not_dvd hpVr)]
  push_cast; ring

/-! ### Transport along ring homomorphisms -/

/-- **PROVED.** `divCoeff` commutes with a ring homomorphism. -/
theorem divCoeff_map {R' : Type*} [CommRing R'] (f : R →+* R') (b : ℕ → R) (d n : ℕ) :
    divCoeff (fun k => f (b k)) d n = f (divCoeff b d n) := by
  unfold divCoeff; split_ifs <;> simp

/-- **PROVED.** The source hypotheses (without depth) are transported by a ring homomorphism
`f : R → R'` (e.g. the reduction `𝒪 → 𝒪/2^M𝒪`). -/
theorem SourceCore.map {R' : Type*} [CommRing R'] (f : R →+* R') (H : SourceCore χ G adm ap a) :
    SourceCore (fun n => f (χ n)) G adm ap (fun n => f (a n)) where
  prime := H.prime
  odd := H.odd
  ap_mod := H.ap_mod
  recur q hq := by
    obtain ⟨ε, hε, hrec⟩ := H.recur q hq
    refine ⟨ε, hε, fun n => ?_⟩
    have := congrArg f (hrec n)
    rw [divCoeff_map]
    simpa using this
  zero := by simp [H.zero]
  support n hn := by simp [H.support n hn]
  support_adm D hD hadm := by simp [H.support_adm D hD hadm]
  mul x y := by simp [H.mul]
  one := by simp [H.one]

/-- **PROVED.** The source hypotheses with depth are transported by a ring homomorphism. -/
theorem SourceHyp.map {R' : Type*} [CommRing R'] (f : R →+* R') (H : SourceHyp T δ χ G adm ap a) :
    SourceHyp T δ (fun n => f (χ n)) G adm ap (fun n => f (a n)) :=
  { toSourceCore := H.toSourceCore.map f
    depth := fun D hD hadm => by
      have h := map_dvd f (H.depth D hD hadm)
      rwa [map_pow, map_ofNat] at h }

/-! ### Non-vacuity of `SourceCore` / `SourceHyp` -/

/-- The phase character of the non-vacuity example: `χ(1) = 1`, `χ(n) = 0` otherwise. -/
def exChi : ℕ → ℤ := fun n => if n = 1 then 1 else 0

/-- The coefficient function of the non-vacuity example: `a(1) = 1`, `a(3) = 2`, `0` otherwise. -/
def exCoeff : ℕ → ℤ := fun n => if n = 1 then 1 else if n = 3 then 2 else 0

/-- **PROVED (non-vacuity of the restated source hypotheses).** Over `ℤ`, with the one good prime
`3`, the stage support `{1, 3}`, `a_3 = 0`, depth `δ = 0` and truncation `T = 3`, the coefficient
function `a(1) = 1`, `a(3) = 2` satisfies every field of `SourceHyp` (recurrence, support, depth),
is nonzero, and the depth bound is attained at `D = 3`: `v₂ a(3) = 1 = δ + ω(3)`. -/
theorem sourceHyp_example :
    SourceHyp 3 0 exChi (fun q => q = 3) (fun D => D = 1 ∨ D = 3) (fun _ => 0) exCoeff ∧
      exCoeff 3 ≠ 0 ∧ ¬ (2 : ℤ) ^ 2 ∣ exCoeff 3 := by
  refine ⟨⟨⟨fun q hq => hq ▸ Nat.prime_three, fun q hq => by subst hq; decide,
    fun q hq => by subst hq; decide, fun q hq => ?_, by simp [exCoeff], ?_, ?_, ?_, ?_⟩, ?_⟩,
    by decide, by decide⟩
  · subst hq
    refine ⟨1, Or.inl rfl, fun n => ?_⟩
    have h1 : ¬ 9 * n = 1 := by omega
    have h3 : ¬ 9 * n = 3 := by omega
    simp [exCoeff, exChi, h1, h3]
  · rintro n ⟨q, hq, hq3⟩
    simp only [exCoeff]
    split_ifs with h1 h3
    · subst h1; simp at hq
    · subst h3
      rw [Nat.prime_three.primeFactors, Finset.mem_singleton] at hq
      exact absurd hq hq3
    · rfl
  · intro D _ hD
    simp only [exCoeff]
    split_ifs with h1 h3
    · exact absurd (Or.inl h1) hD
    · exact absurd (Or.inr h3) hD
    · rfl
  · intro x y
    simp only [exChi]
    by_cases hx : x = 1
    · subst hx; simp
    · have hxy : x * y ≠ 1 := fun h => hx (Nat.eq_one_of_mul_eq_one_right h)
      simp [hx, hxy]
  · simp [exChi]
  · intro D _ hD
    rcases hD with rfl | rfl
    · simp [exCoeff]
    · rw [ArithmeticFunction.cardDistinctFactors_apply_prime Nat.prime_three]
      simp [exCoeff]

/-- **PROVED (non-vacuity of `DivInv`).** The invariant holds for the example source at `U = ∅`. -/
theorem divInv_example :
    DivInv 3 0 exChi (fun q => q = 3) ∅ exCoeff :=
  sourceHyp_example.1.divInv

end ZInQ.Manuscript.RC.Odd
