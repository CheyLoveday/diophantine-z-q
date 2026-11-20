import ZInQKernel.Contrib.OneProof.RC.StageSelector.Forms

/-! The primitive Heegner form of conductor `|h|` for the companion in
tex 2411–2416, 2428–2431. Scaling the conductor-one form at a level prime
to the conductor is an on-the-spot construction (c). -/

noncomputable section

open NumberField ZInQ.Progressions ZInQ.Contrib.CloudB3RC53
  ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.Gz34Instance

/-- Scaling the middle and last coefficients by `c` and `c²` preserves
primitivity when the leading coefficient is the level, prime to `c`. -/
theorem exists_ringHeegnerForm {N c : ℕ} {d : ℤ} (hN : 0 < N) (hsq : Squarefree d)
    (hloc : ∀ p : ℕ, p.Prime → p ∣ 2 * N → SquareAt p d) (hNc : N.Coprime c) :
    ∃ B C : ℤ, IsHeegnerForm N (d * c ^ 2) N B C := by
  obtain ⟨B, C, hA, hdiv, hdisc, hprim⟩ := StageSelector.exists_heegnerForm hN hsq hloc
  refine ⟨(c : ℤ) * B, (c : ℤ) ^ 2 * C, hA, hdiv, ?_, ?_⟩
  · rw [← hdisc]
    ring
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  have hg : (p : ℤ) ∣ (Int.gcd (Int.gcd (N : ℤ) ((c : ℤ) * B)) ((c : ℤ) ^ 2 * C) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hpg
  have hgab := hg.trans (Int.gcd_dvd_left _ _)
  have hpN : (p : ℤ) ∣ (N : ℤ) := hgab.trans (Int.gcd_dvd_left _ _)
  have hpc : ¬ (p : ℤ) ∣ (c : ℤ) := by
    intro h
    have h1 := Nat.dvd_gcd (Int.natCast_dvd_natCast.mp hpN) (Int.natCast_dvd_natCast.mp h)
    rw [hNc.gcd_eq_one] at h1
    exact hp.not_dvd_one h1
  have hpp := Nat.prime_iff_prime_int.mp hp
  have hpB : (p : ℤ) ∣ B :=
    (hpp.dvd_mul.mp (hgab.trans (Int.gcd_dvd_right _ _))).resolve_left hpc
  have hpC : (p : ℤ) ∣ C := by
    rcases hpp.dvd_mul.mp (hg.trans (Int.gcd_dvd_right _ _)) with h | h
    · exact (hpc (hpp.dvd_of_dvd_pow h)).elim
    · exact h
  have h1 := Int.dvd_gcd (Int.natCast_dvd_natCast.mpr (Int.dvd_gcd hpN hpB)) hpC
  rw [hprim] at h1
  exact hp.not_dvd_one h1

/-- A prepared parameter is prime to the level, and its companion supplies
the local square at every prime of twice the level. -/
theorem companion_formConditions {E : WeierstrassCurve ℚ} {Lat : PeriodPair} {s h k : ℤ}
    (hp : Prepared E s h) (hk : Companion E Lat s h k) :
    (newformLevel E).Coprime h.natAbs ∧
      ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel E → SquareAt p k := by
  refine ⟨Nat.coprime_of_dvd (fun p hpp hpN hph => ?_), fun p hpp hpN => ?_⟩
  · exact (hp.2.2.1 p hpp (dvd_mul_of_dvd_right hpN 2)).1 (Int.natCast_dvd.mpr hph)
  · have hh : (p : ℤ) ∣ ((2 * newformLevel E : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hpN
    exact hk.2.2.2.1 p hpp (by push_cast at hh; exact dvd_mul_of_dvd_left hh h)

/-- Each companion has a primitive form of the required discriminant. -/
theorem exists_companion_form {E : WeierstrassCurve ℚ} {Lat : PeriodPair} {s h k : ℤ}
    (hN : 0 < newformLevel E) (hp : Prepared E s h) (hk : Companion E Lat s h k) :
    ∃ B C : ℤ, IsHeegnerForm (newformLevel E) (k * h.natAbs ^ 2) (newformLevel E) B C :=
  exists_ringHeegnerForm hN hk.2.2.1 (companion_formConditions hp hk).2
    (companion_formConditions hp hk).1


end ZInQ.Manuscript.RC.Gz34Instance
