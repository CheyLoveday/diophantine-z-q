import ZInQKernel.Contrib.OneProof.RC.KSplitSeed.Valuation
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.SymShell

/-! The transported source's actual Fourier sieve and its good-prime shell. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KSplitSeed

open Finset AppE EvenReading AddressGenuine Wiring PrintsAnalytic
open ZInQ.Manuscript.RC.Even KSplit
open ZInQ.Contrib.CloudB3RC53

/-- The all-index unit-square sieve in Appendix E/F, at reference 1. Its
restriction to positive squarefree indices is exactly `S0Filter S 1`. -/
def evenUnitSieve (S : Finset ℕ) (n : ℕ) : Prop :=
  (∀ q ∈ S, ¬ q ∣ n) ∧
    ∀ q ∈ S, (q = 2 → n % 8 = 1) ∧ (q ≠ 2 → IsSquare (n : ZMod q))

/-- The normalized Fourier coefficients after the manuscript's sieve
(tex 9471–9479, 10291–10295, 10350–10353). Keep the square shells. -/
def evenCoeff {ℓ : ℕ} {C : CentralNormalization (Ecurve ℓ)} {k : ℤ}
    {hk : k < 0} {S : Finset ℕ} (G : GenuineEvenSource C hk S) (n : ℕ) : ℂ := by
  classical
  exact if evenUnitSieve S n then hiwCoeff G.P.g n / hiwCoeff G.P.g 1 else 0

open Classical in
theorem evenCoeff_squarefree {ℓ : ℕ} {C : CentralNormalization (Ecurve ℓ)} {k : ℤ}
    {hk : k < 0} {S : Finset ℕ} (G : GenuineEvenSource C hk S) {n : ℕ}
    (hn : Squarefree n) :
    evenCoeff G n = if S0Filter S 1 n then G.P.z n * (G.r n : ℂ) else 0 := by
  classical
  have hnf : 0 < n := Nat.pos_of_ne_zero (fun h => by subst n; simp at hn)
  have hiff : evenUnitSieve S n ↔ S0Filter S 1 n := by
    simp [evenUnitSieve, S0Filter, hnf, hn]
  by_cases h : S0Filter S 1 n
  · simpa [evenCoeff, h, hiff.mpr h] using (G.coeff_eq n h).1
  · simp [evenCoeff, h, show ¬ evenUnitSieve S n from fun e => h (hiff.mp e)]

theorem evenCoeff_one {ℓ : ℕ} {C : CentralNormalization (Ecurve ℓ)} {k : ℤ}
    {hk : k < 0} {S : Finset ℕ} (G : GenuineEvenSource C hk S) :
    evenCoeff G 1 = 1 := by
  have hs : evenUnitSieve S 1 := by
    simpa [evenUnitSieve, S0Filter] using G.P.D₀_filter
  simp [evenCoeff, hs, G.P.ha₀]

/-- The sieve is constant across good square shells. This is the
coefficient-level commutation used at tex 8151–8152 and 9477–9479. -/
theorem evenUnitSieve_mul_sq {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    (h2S : 2 ∈ S) {p : ℕ} (hp : p.Prime) (hpS : p ∉ S) (n : ℕ) :
    evenUnitSieve S (p ^ 2 * n) ↔ evenUnitSieve S n := by
  have hqnp (q : ℕ) (hq : q ∈ S) : ¬ q ∣ p := fun hd =>
    hpS (((Nat.prime_dvd_prime_iff_eq (hS q hq) hp).mp hd) ▸ hq)
  have hd (q : ℕ) (hq : q ∈ S) : q ∣ p ^ 2 * n ↔ q ∣ n := by
    refine ⟨fun h => ((hS q hq).dvd_mul.mp h).resolve_left
      (fun h => hqnp q hq ((hS q hq).dvd_of_dvd_pow h)), fun h => dvd_mul_of_dvd_right h _⟩
  have hod := Nat.odd_iff.mp (hp.odd_of_ne_two (fun h => hpS (by simpa only [h] using h2S)))
  have hmod8 : p ^ 2 % 8 = 1 := by
    have hm : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
    rw [Nat.pow_mod]
    rcases hm with h | h | h | h <;> rw [h]
  have hm : p ^ 2 * n % 8 = n % 8 := by
    rw [Nat.mul_mod, hmod8, one_mul, Nat.mod_mod]
  have hs (q : ℕ) (hq : q ∈ S) :
      IsSquare ((p ^ 2 * n : ℕ) : ZMod q) ↔ IsSquare (n : ZMod q) := by
    have : Fact q.Prime := ⟨hS q hq⟩
    have hpn : (p : ZMod q) ≠ 0 := fun h => hqnp q hq ((ZMod.natCast_eq_zero_iff p q).mp h)
    push_cast
    have hsqp : IsSquare ((p : ZMod q) ^ 2) := ⟨p, by ring⟩
    constructor
    · intro h
      have h' := h.div hsqp
      rwa [mul_comm ((p : ZMod q) ^ 2), mul_div_cancel_right₀ _ (pow_ne_zero 2 hpn)] at h'
    · exact hsqp.mul
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun q hq hn => h1 q hq ((hd q hq).mpr hn), fun q hq =>
      ⟨fun h => hm ▸ (h2 q hq).1 h, fun h => (hs q hq).mp ((h2 q hq).2 h)⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun q hq hn => h1 q hq ((hd q hq).mp hn), fun q hq =>
      ⟨fun h => hm.symm ▸ (h2 q hq).1 h, fun h => (hs q hq).mpr ((h2 q hq).2 h)⟩⟩

/-- The actual normalization and sieve preserve (E.12), with the character
convention of the positive twist and the elliptic trace used by the leaf. -/
theorem evenCoeff_shell {ℓ : ℕ} {W : WData ℓ}
    {C : CentralNormalization (Ecurve ℓ)} {hk : W.kfin < 0} {S : Finset ℕ}
    (G : GenuineEvenSource C hk S) {p : ℕ} [hp : Fact p.Prime] (hpS : p ∉ S) :
    ShellRecurrence (evenCoeff G) (G.P.η p)
      (G.P.η p * ((legendreSym p (-1) : ℤ) : ℂ)) (apk W p) p := by
  classical
  have hpN : ¬ p ∣ G.P.N := fun hd => hpS (G.P.hNS p hp.out hd)
  have hr := GlueSweep.Sym.shellRecurrence_of_eigenspace G.P.hN G.P.ψ G.P.η
    (Or.inl (rfl : (1 : ℤ) = 1)) G.P.hψη G.P.hg hpN
  rw [GlueSweep.Sym.psi_eq_eta_mul_legendre G.P.hN G.P.ψ G.P.η G.P.hψη hpN] at hr
  simp only [qtwist_Ecurve_eq] at hr
  intro n
  have hs := evenUnitSieve_mul_sq G.P.hS₀ G.P.two_mem hp.out hpS n
  by_cases hn : evenUnitSieve S n
  · have h := hr n
    have hf₁ : evenUnitSieve S (p ^ 2 * n) := hs.mpr hn
    by_cases hd : p ^ 2 ∣ n
    · have hh : p ^ 2 * (n / p ^ 2) = n := Nat.mul_div_cancel' hd
      have hf₂ : evenUnitSieve S (n / p ^ 2) :=
        (evenUnitSieve_mul_sq G.P.hS₀ G.P.two_mem hp.out hpS (n / p ^ 2)).mp (by rw [hh]; exact hn)
      simp only [evenCoeff, ite_eq_left hf₁, ite_eq_left hn, ite_eq_left hd, ite_eq_left hf₂, apk]
      rw [ite_eq_left hd] at h
      rw [h]
      ring
    · simp only [evenCoeff, ite_eq_left hf₁, ite_eq_left hn, ite_eq_right hd, apk]
      rw [ite_eq_right hd] at h
      rw [h]
      ring
  · have hf₁ : ¬ evenUnitSieve S (p ^ 2 * n) := fun hf => hn (hs.mp hf)
    by_cases hd : p ^ 2 ∣ n
    · have hh : p ^ 2 * (n / p ^ 2) = n := Nat.mul_div_cancel' hd
      have hf₂ : ¬ evenUnitSieve S (n / p ^ 2) := by
        intro e
        have he := (evenUnitSieve_mul_sq G.P.hS₀ G.P.two_mem hp.out hpS _).mpr e
        rw [hh] at he
        exact hn he
      simp [evenCoeff, hf₁, hn, hd, hf₂]
    · simp [evenCoeff, hf₁, hn, hd]

/-- Transport the lower bound from the retained old coefficients at the
actual companion and its positive multiples (tex 10296–10314). -/
theorem transported_lower_of_old_unit {ℓ : ℕ} {C : CentralNormalization (Ecurve ℓ)}
    {k : ℤ} {hk : k < 0} {S : Finset ℕ} (G : GenuineEvenSource C hk S)
    (hS : k.natAbs.primeFactors ⊆ S) (old : ℕ → ℚ) (Lref : ℚ) (δ : ℤ)
    (hLref : Lref ≠ 0) (hLk : C.Lstar k ≠ 0)
    (hOldk : old k.natAbs ^ 2 = C.Lstar k / Lref)
    (hUnit : padicValRat 2 (old k.natAbs) = (omegaN k.natAbs : ℤ) + δ)
    (hOld : ∀ n, S0Filter S 1 n →
      old (k.natAbs * n) ^ 2 = C.Lstar ((n : ℤ) * k) / Lref)
    (hOldLow : ∀ n, S0Filter S 1 n → old (k.natAbs * n) ≠ 0 →
      (omegaN (k.natAbs * n) : ℤ) + δ ≤ padicValRat 2 (old (k.natAbs * n))) :
    ∀ n, S0Filter S 1 n → G.r n ≠ 0 → (omegaN n : ℤ) ≤ padicValRat 2 (G.r n) := by
  intro n hf hr
  have hcop : k.natAbs.Coprime n := by
    refine Nat.coprime_iff_gcd_eq_one.mpr ?_
    by_contra hn
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (n := k.natAbs.gcd n) hn
    have hk0 : k.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hk.ne
    exact hf.2.2.1 q (hS (Nat.mem_primeFactors.mpr
      ⟨hq, hqd.trans (Nat.gcd_dvd_left _ _), hk0⟩)) (hqd.trans (Nat.gcd_dvd_right _ _))
  have he := (G.coeff_eq n hf).2
  have hval := transport_valuation hr hLref hLk he (hOld n hf) hOldk
  have hneq : old (k.natAbs * n) ≠ 0 := by
    intro h
    have hL : C.Lstar ((n : ℤ) * k) = 0 :=
      (div_eq_zero_iff.mp (by simpa [h] using (hOld n hf).symm)).resolve_right hLref
    exact (pow_ne_zero 2 hr) (by simpa [hL] using he)
  have hlow := hOldLow n hf hneq
  have hω : omegaN (k.natAbs * n) = omegaN k.natAbs + omegaN n := by
    simp only [omegaN, hcop.primeFactors_mul, Finset.card_union_of_disjoint hcop.disjoint_primeFactors]
  rw [hω] at hlow
  push_cast at hlow
  omega

end ZInQ.Manuscript.RC.KSplitSeed
