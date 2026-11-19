import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.GenusLower
import ZInQKernel.Contrib.CloudB3RC53.Companion.Disc
import ZInQKernel.Contrib.OneProof.RC.AppE.Phase
import ZInQKernel.Progressions.QuadField.Signature
import ZInQKernel.Progressions.QuadField.Discriminant

/-! The field and the conductor-one form in (O.1), tex 8209–8217.
The choice of the form with leading coefficient equal to the level, using the
prime-power lifting and CRT already used in Appendix E, is on-the-spot (c). -/

noncomputable section

open NumberField ZInQ.Progressions ZInQ.Contrib.CloudB3RC53
  ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.StageSelector

/-- The prepared parameter and its genus partner give the negative odd squarefree
discriminant and the local squares at every prime of twice the level. -/
theorem prepared_discriminant {E : WeierstrassCurve ℚ} {D hstar : ℤ}
    (hprep : Prepared E hstar D) (hgp : GenusPartner E hstar) :
    D * hstar < 0 ∧ Squarefree (D * hstar) ∧
      (∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel E → SquareAt p (D * hstar)) := by
  obtain ⟨hD, hDsq, hDloc, hcop⟩ := hprep
  obtain ⟨hs, -, hssq, -, hsloc, -⟩ := hgp
  exact ⟨mul_neg_of_pos_of_neg hD hs, squarefree_mul_iff.mpr
    ⟨hcop.isRelPrime, hDsq, hssq⟩, fun p hp hN => (hDloc p hp hN).mul (hsloc p hp hN) hp⟩

/-- The chosen quadratic field has exactly the indicated discriminant. -/
theorem qsqrt_discr {d : ℤ} [Fact (¬ IsSquare (d : ℚ))]
    (hd : d < 0) (hsq : Squarefree d) (h4 : d % 4 = 1) : discr (Qsqrt d) = d :=
  Companion.discr_eq_of_sq Qsqrt.finrank hsq h4 (by omega)
    (by simpa using Qsqrt.ringHom_omega_sq (RingHom.id (Qsqrt d)))

/-- Local unit squares at the primes of `2N` give a primitive Heegner form
of discriminant `d` with leading coefficient exactly `N`. -/
theorem exists_heegnerForm {N : ℕ} {d : ℤ} (hN : 0 < N) (hsq : Squarefree d)
    (hloc : ∀ p : ℕ, p.Prime → p ∣ 2 * N → SquareAt p d) :
    ∃ B C : ℤ, IsHeegnerForm N d N B C := by
  let a := (d % (8 * (N : ℤ))).toNat
  have h8N : (0 : ℤ) < 8 * N := by positivity
  have ha : (a : ℤ) = d % (8 * (N : ℤ)) := Int.toNat_of_nonneg (Int.emod_nonneg _ h8N.ne')
  have hae : (a : ℤ) ≡ d [ZMOD 8 * (N : ℤ)] := by
    rw [ha]
    exact Int.mod_modEq _ _
  have hp2N {p : ℕ} (hp : p.Prime) (hpN : p ∣ 4 * N) : p ∣ 2 * N := by
    rcases hp.dvd_mul.mp hpN with hp4 | h
    · have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (n := 2) (by simpa using hp4)
      exact dvd_mul_of_dvd_left hp2 N
    · exact dvd_mul_of_dvd_right h 2
  have h8 : a % 8 = 1 := by
    have h := hae.of_dvd (dvd_mul_right (8 : ℤ) (N : ℤ))
    change (a : ℤ) % 8 = d % 8 at h
    rw [(hloc 2 Nat.prime_two (dvd_mul_right 2 N)).2.1 rfl] at h
    exact_mod_cast h
  have hcast (p : ℕ) (hp : p ∣ 4 * N) : (a : ZMod p) = (d : ZMod p) := by
    have hp' : (p : ℤ) ∣ 8 * (N : ℤ) := by
      exact_mod_cast (show p ∣ 8 * N from by
        rw [show 8 * N = (4 * N) * 2 by omega]
        exact dvd_mul_of_dvd_left hp 2)
    have h := Int.modEq_iff_dvd.mp (hae.of_dvd hp')
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (d - (a : ℤ)) p).mpr h
    push_cast at hz
    exact (sub_eq_zero.mp hz).symm
  have hcop : a.Coprime (4 * N) := by
    refine Nat.coprime_of_dvd fun p hp hpa hpN => (hloc p hp (hp2N hp hpN)).1 ?_
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← hcast p hpN]
    exact (ZMod.natCast_eq_zero_iff a p).mpr hpa
  obtain ⟨b, hb⟩ := AppE.isSquare_zmod_of_local a (4 * N) (by omega) hcop
    (fun p hp hpN => ⟨fun _ => h8, fun hne => hcast p hpN ▸ (hloc p hp (hp2N hp hpN)).2.2 hne⟩)
  obtain ⟨B, hB⟩ := ZMod.intCast_surjective b
  have hdiv : (4 * (N : ℤ)) ∣ B ^ 2 - d := by
    have hcast' : (a : ZMod (4 * N)) = (d : ZMod (4 * N)) := hcast _ dvd_rfl
    have hz : ((B ^ 2 - d : ℤ) : ZMod (4 * N)) = 0 := by
      push_cast
      rw [hB, ← hcast', hb, sq, sub_self]
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  obtain ⟨C, hC⟩ := hdiv
  have hdisc : B ^ 2 - 4 * N * C = d := by linarith
  refine ⟨B, C, by exact_mod_cast hN, dvd_rfl, hdisc, ?_⟩
  set g := Int.gcd (Int.gcd (N : ℤ) B) C
  have hAB : (g : ℤ) ∣ (Int.gcd (N : ℤ) B : ℤ) := Int.gcd_dvd_left _ _
  have hgN : (g : ℤ) ∣ (N : ℤ) := hAB.trans (Int.gcd_dvd_left _ _)
  have hgB : (g : ℤ) ∣ B := hAB.trans (Int.gcd_dvd_right _ _)
  have hgC : (g : ℤ) ∣ C := Int.gcd_dvd_right _ _
  have hgd : (g : ℤ) * g ∣ d := by
    rw [← hdisc, sq, mul_assoc]
    exact dvd_sub (mul_dvd_mul hgB hgB) (dvd_mul_of_dvd_right (mul_dvd_mul hgN hgC) 4)
  exact Nat.isUnit_iff.mp (by exact_mod_cast hsq _ hgd)

#print axioms prepared_discriminant
#print axioms qsqrt_discr
#print axioms exists_heegnerForm

end ZInQ.Manuscript.RC.StageSelector
