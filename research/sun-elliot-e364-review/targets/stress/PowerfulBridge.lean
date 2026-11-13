import Mathlib

/-!
E364 powerfulness, denominator divisibility, and the unit defect.

This is an independent coefficientwise stress proof, not an import from a
mutable sibling checkout. Pairwise coprimality is used only to split product
valuations back to the three actual source terms.
-/

namespace SunElliotE364.Targets.Stress

/-- No prime occurs to exponent exactly one in this natural number. -/
def NoExponentOne (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → n.factorization p ≠ 1

lemma factorization_mul_at {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (p : ℕ) :
    (a * b).factorization p = a.factorization p + b.factorization p := by
  simp only [Nat.factorization_mul ha hb, Finsupp.add_apply]

lemma prime_of_factorization_eq_one {n p : ℕ} (hfac : n.factorization p = 1) : p.Prime := by
  by_contra hp
  have hz := Nat.factorization_eq_zero_of_not_prime n hp
  omega

lemma not_dvd_of_coprime_of_prime {a b p : ℕ} (hp : p.Prime)
    (hab : Nat.Coprime a b) (hpa : p ∣ a) : ¬p ∣ b := by
  intro hpb
  have hg : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
  rw [hab.gcd_eq_one] at hg
  exact hp.ne_one (Nat.dvd_one.mp hg)

/-- At powerfulness level, a product splits if and only if both coprime
factors have no exponent-one prime. -/
theorem noExponentOne_mul_iff {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : Nat.Coprime a b) :
    NoExponentOne (a * b) ↔ NoExponentOne a ∧ NoExponentOne b := by
  have hone_sided : ∀ {x y : ℕ}, x ≠ 0 → y ≠ 0 → Nat.Coprime x y →
      NoExponentOne (x * y) → NoExponentOne x := by
    intro x y hx hy hxy hprod p hp hpx
    have hpy : ¬p ∣ y := by
      apply not_dvd_of_coprime_of_prime hp hxy
      exact Nat.dvd_of_factorization_pos (by omega)
    have hyfac : y.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpy
    have hfac := factorization_mul_at hx hy p
    rw [hpx, hyfac] at hfac
    exact hprod p hp (by omega)
  constructor
  · intro hprod
    constructor
    · exact hone_sided ha hb hab hprod
    · apply hone_sided hb ha hab.symm
      simpa [Nat.mul_comm] using hprod
  · rintro ⟨ha1, hb1⟩ p hp hsum
    have hfac := factorization_mul_at ha hb p
    rcases Nat.eq_zero_or_pos (a.factorization p) with ha0 | hapos
    · rw [ha0] at hfac
      have hb_eq : b.factorization p = 1 := by omega
      exact hb1 p hp hb_eq
    · have ha_eq : a.factorization p = 1 := by omega
      exact ha1 p hp ha_eq

/-- The squarefree decomposition forces `D ∣ s` exactly when the represented
natural has no exponent-one prime. Non-prime indices are harmless. -/
theorem dvd_square_factor_iff_noExponentOne {T D s : ℕ}
    (hD : D ≠ 0) (hs : s ≠ 0) (hDsf : Squarefree D) (hdecomp : T = D * s ^ 2) :
    D ∣ s ↔ NoExponentOne T := by
  have hdecomp_fac : ∀ p : ℕ,
      T.factorization p = D.factorization p + 2 * s.factorization p := by
    intro p
    calc
      T.factorization p = (D * s ^ 2).factorization p := by rw [hdecomp]
      _ = D.factorization p + (s ^ 2).factorization p := by
        simp only [Nat.factorization_mul hD (pow_ne_zero 2 hs), Finsupp.add_apply]
      _ = D.factorization p + (s.factorization p + s.factorization p) := by
        rw [pow_two, factorization_mul_at hs hs p]
      _ = D.factorization p + 2 * s.factorization p := by ring
  constructor
  · intro hDvd
    have hle := (Nat.factorization_le_iff_dvd hD hs).mpr hDvd
    intro p hp hTone
    have hleD := (Nat.squarefree_iff_factorization_le_one hD).mp hDsf p
    have hle_p := hle p
    have hfac := hdecomp_fac p
    omega
  · intro hT
    apply (Nat.factorization_le_iff_dvd hD hs).mp
    intro p
    by_cases hp : p.Prime
    · have hfac := hdecomp_fac p
      have hne := hT p hp
      have hleD := (Nat.squarefree_iff_factorization_le_one hD).mp hDsf p
      omega
    · rw [Nat.factorization_eq_zero_of_not_prime D hp]
      exact Nat.zero_le _

/-- Product splitting for the three consecutive source terms. -/
theorem noExponentOne_triple {N : ℕ} (hN : 2 ≤ N)
    (hc0 : Nat.Coprime (N - 1) N) (hc1 : Nat.Coprime N (N + 1))
    (hc2 : Nat.Coprime (N - 1) (N + 1)) :
    NoExponentOne ((N - 1) * N * (N + 1)) ↔
      NoExponentOne (N - 1) ∧ NoExponentOne N ∧ NoExponentOne (N + 1) := by
  have hm : N - 1 ≠ 0 := by omega
  have hn : N ≠ 0 := by omega
  have hp : N + 1 ≠ 0 := by omega
  have hmn : (N - 1) * N ≠ 0 := mul_ne_zero hm hn
  constructor
  · intro hprod
    have hsplit := (noExponentOne_mul_iff hmn hp (Nat.Coprime.mul_left hc2 hc1)).mp hprod
    have hleft := (noExponentOne_mul_iff hm hn hc0).mp hsplit.1
    exact ⟨hleft.1, hleft.2, hsplit.2⟩
  · rintro ⟨h0, h1, h2⟩
    exact (noExponentOne_mul_iff hmn hp (Nat.Coprime.mul_left hc2 hc1)).mpr
      ⟨(noExponentOne_mul_iff hm hn hc0).mpr ⟨h0, h1⟩, h2⟩

/-- **Stress target passed by the Lean proof below when compiled.** The three
actual factors are powerful exactly when the squarefree denominator parameter
clears into `s`. -/
theorem powerful_terms_iff_D_dvd_s {N D s : ℕ} (hN : 2 ≤ N)
    (hD : D ≠ 0) (hs : s ≠ 0) (hDsf : Squarefree D)
    (hdecomp : (N - 1) * N * (N + 1) = D * s ^ 2)
    (hc0 : Nat.Coprime (N - 1) N) (hc1 : Nat.Coprime N (N + 1))
    (hc2 : Nat.Coprime (N - 1) (N + 1)) :
    (NoExponentOne (N - 1) ∧ NoExponentOne N ∧ NoExponentOne (N + 1)) ↔ D ∣ s := by
  rw [dvd_square_factor_iff_noExponentOne hD hs hDsf hdecomp]
  exact (noExponentOne_triple hN hc0 hc1 hc2).symm

/-- The quotient defect attached to `D` and `s`. -/
def denominatorDefect (D s : ℕ) : ℕ := D / Nat.gcd D s

/-- Positivity makes the unit-defect condition literally a divisibility
condition, not merely a similar valuation statistic. -/
theorem denominatorDefect_eq_one_iff_dvd {D s : ℕ} (hD : D ≠ 0) :
    denominatorDefect D s = 1 ↔ D ∣ s := by
  constructor
  · intro hdefect
    have hgcd : Nat.gcd D s = D := by
      have hrec := Nat.div_mul_cancel (Nat.gcd_dvd_left D s)
      unfold denominatorDefect at hdefect
      rw [hdefect, one_mul] at hrec
      exact hrec
    rw [← hgcd]
    exact Nat.gcd_dvd_right D s
  · intro hDvd
    have hgcd : Nat.gcd D s = D := by
      apply Nat.dvd_antisymm (Nat.gcd_dvd_left D s)
      exact Nat.dvd_gcd (dvd_refl D) hDvd
    simp [denominatorDefect, hgcd, Nat.div_self (Nat.pos_of_ne_zero hD)]

/-- The three-factor powerfulness claim is also equivalent to unit denominator
quadrant defect. -/
theorem powerful_terms_iff_defect_eq_one {N D s : ℕ} (hN : 2 ≤ N)
    (hD : D ≠ 0) (hs : s ≠ 0) (hDsf : Squarefree D)
    (hdecomp : (N - 1) * N * (N + 1) = D * s ^ 2)
    (hc0 : Nat.Coprime (N - 1) N) (hc1 : Nat.Coprime N (N + 1))
    (hc2 : Nat.Coprime (N - 1) (N + 1)) :
    (NoExponentOne (N - 1) ∧ NoExponentOne N ∧ NoExponentOne (N + 1)) ↔
      denominatorDefect D s = 1 := by
  rw [denominatorDefect_eq_one_iff_dvd hD]
  exact powerful_terms_iff_D_dvd_s hN hD hs hDsf hdecomp hc0 hc1 hc2

/-- Natural-number form of the denominator-base presentation `2D ∣ 2s`. -/
theorem powerful_terms_iff_twoD_dvd_two_s {N D s : ℕ} (hN : 2 ≤ N)
    (hD : D ≠ 0) (hs : s ≠ 0) (hDsf : Squarefree D)
    (hdecomp : (N - 1) * N * (N + 1) = D * s ^ 2)
    (hc0 : Nat.Coprime (N - 1) N) (hc1 : Nat.Coprime N (N + 1))
    (hc2 : Nat.Coprime (N - 1) (N + 1)) :
    (NoExponentOne (N - 1) ∧ NoExponentOne N ∧ NoExponentOne (N + 1)) ↔
      2 * D ∣ 2 * s := by
  rw [powerful_terms_iff_D_dvd_s hN hD hs hDsf hdecomp hc0 hc1 hc2]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by ring⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by nlinarith⟩

#print axioms powerful_terms_iff_D_dvd_s
#print axioms powerful_terms_iff_defect_eq_one
#print axioms powerful_terms_iff_twoD_dvd_two_s

end SunElliotE364.Targets.Stress
