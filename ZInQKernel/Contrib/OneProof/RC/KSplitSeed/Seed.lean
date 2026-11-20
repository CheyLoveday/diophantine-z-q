import ZInQKernel.Contrib.OneProof.RC.KSplitSeed.Sieve

/-! Appendix G's mod-eight argument on the selected transported source. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KSplitSeed

open Finset AppE EvenReading AddressGenuine Wiring PrintsAnalytic
open ZInQ.Manuscript.RC.Even KSplit
open ZInQ.Contrib.CloudB3RC53

/-- A rational coefficient of integral depth is divisible by the specified
integer power of two in the chosen coefficient ring. Only its restriction
to rational odd denominators is used here. -/
theorem ratCast_pow_two_factor (O : Subring ℂ)
    (hodd : ∀ d : ℕ, ¬ 2 ∣ d → (d : ℂ)⁻¹ ∈ O) {x : ℚ} {e : ℕ}
    (hx : x ≠ 0) (hv : (e : ℤ) ≤ padicValRat 2 x) :
    ∃ y ∈ O, (x : ℂ) = 2 ^ e * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let y := x / 2 ^ e
  have hy : 0 ≤ padicValRat 2 y := by
    dsimp only [y]
    have htwo : padicValRat 2 (2 : ℚ) = 1 := by
      simpa only [Nat.cast_ofNat] using (padicValRat.self (p := 2) Nat.prime_two.one_lt)
    rw [padicValRat.div hx (by positivity), padicValRat.pow, htwo, mul_one]
    omega
  have hden : ¬ 2 ∣ (y : ℚ).den := by
    intro hd
    have hn : ¬ 2 ∣ y.num.natAbs := fun h =>
      (by decide : ¬ 2 ∣ 1) (y.reduced ▸ Nat.dvd_gcd h hd)
    have h0 : padicValNat 2 y.num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hn
    have h1 := one_le_padicValNat_of_dvd y.den_ne_zero hd
    rw [padicValRat, padicValInt, h0] at hy
    omega
  refine ⟨(y : ℂ), ?_, ?_⟩
  · rw [Rat.cast_def, div_eq_mul_inv]
    exact O.mul_mem (intCast_mem O _) (hodd _ hden)
  · dsimp only [y]
    push_cast
    field_simp

/-- No unit plus the ordinary bound supplies the extra integer two, for
exactly the same reading. Off the squarefree filter the actual sieve gives zero. -/
theorem evenCoeff_factor_of_no_reading {ℓ : ℕ} {C : CentralNormalization (Ecurve ℓ)} {k : ℤ}
    {hk : k < 0} {S U : Finset ℕ} (G : GenuineEvenSource C hk S) (O : Subring ℂ)
    (hodd : ∀ d : ℕ, ¬ 2 ∣ d → (d : ℂ)⁻¹ ∈ O)
    (hz : ∀ n, S0Filter S 1 n → G.P.z n ∈ O)
    (hlow : ∀ n, S0Filter S 1 n → G.r n ≠ 0 → (omegaN n : ℤ) ≤ padicValRat 2 (G.r n))
    (hU : ∀ p ∈ U, p.Prime) (hzero : RevGen S G.r U = 0) :
    ∃ y ∈ O, evenCoeff G (∏ p ∈ U, p) = 2 ^ (U.card + 1) * y := by
  classical
  let n := ∏ p ∈ U, p
  have hn : Squarefree n := RealizeAux.squarefree_prod_primes _ hU
  rw [evenCoeff_squarefree G hn]
  by_cases hf : S0Filter S 1 n
  · rw [ite_eq_left hf]
    by_cases hr : G.r n = 0
    · exact ⟨0, O.zero_mem, by simp [hr]⟩
    have hlow' := hlow n hf hr
    rw [omegaN_prod_primes U hU] at hlow'
    have hv := succ_le_padicValRat_of_revGen_zero hU hf hr hlow' hzero
    obtain ⟨y, hy, he⟩ := ratCast_pow_two_factor O hodd hr (e := U.card + 1) (by exact_mod_cast hv)
    exact ⟨G.P.z n * y, O.mul_mem (hz n hf) hy, by rw [he]; ring⟩
  · rw [ite_eq_right hf]
    exact ⟨0, O.zero_mem, by simp⟩

/-- At a unit residue the inverse of the character value is another
value of the same character. -/
theorem dirichletValue_unit_of_coprime {N p : ℕ} (hN : N ≠ 0)
    (η : DirichletCharacter ℂ N) (hpN : p.Coprime N) (O : Subring ℂ)
    (hO : ∀ n : ℕ, η n ∈ O) : η p ≠ 0 ∧ (η p)⁻¹ ∈ O := by
  let : NeZero N := ⟨hN⟩
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime p N).mpr hpN
  have hv : (u : ZMod N) * (↑u⁻¹ : ZMod N) = 1 := u.mul_inv
  have hm := (map_mul η (u : ZMod N) (↑u⁻¹ : ZMod N)).symm
  rw [hv, map_one, hu] at hm
  have hη0 : η p ≠ 0 := fun h => by simp [h] at hm
  refine ⟨hη0, ?_⟩
  have hc := hO (↑u⁻¹ : ZMod N).val
  rw [ZMod.natCast_zmod_val] at hc
  have he : η (↑u⁻¹ : ZMod N) = (η p)⁻¹ := by
    apply mul_left_cancel₀ hη0
    rw [hm, mul_inv_cancel₀ hη0]
  exact he ▸ hc

set_option maxHeartbeats 1000000 in
/-- The source-dependent part of the one-prime calculation. The trace
assumptions are the identity at `p²` and its good-prime approximation from
tex 10326–10333 and 10437–10441. The determinant data concern the same
singleton forms, in characteristic zero. -/
theorem eight_dvd_of_trace_match {ℓ : ℕ} {W : WData ℓ} (D : LabelData W)
    {C : CentralNormalization (Ecurve ℓ)} {hk : W.kfin < 0} {S : Finset ℕ}
    (G : GenuineEvenSource C hk S) (O : Subring ℂ)
    (hodd : ∀ d : ℕ, ¬ 2 ∣ d → (d : ℂ)⁻¹ ∈ O)
    (hz : ∀ n, S0Filter S 1 n → G.P.z n ∈ O)
    (hhalf : (2 : ℂ)⁻¹ ∉ O)
    (hlow : ∀ n, S0Filter S 1 n → G.r n ≠ 0 → (omegaN n : ℤ) ≤ padicValRat 2 (G.r n))
    {p p' : ℕ} [hp : Fact p.Prime] (hpM : p.Coprime D.m₂) (hp'M : p'.Coprime D.m₂)
    (hp' : p'.Prime) (hne : p' ≠ p)
    (hkp : jacobiSym W.kfin p = 1) (hkp' : jacobiSym W.kfin p' = 1)
    (hpS : p ∉ S) (hηO : ∀ n : ℕ, G.P.η n ∈ O)
    (hH : ∀ n, Hp (evenCoeff G) (fun n => G.P.η n) D.m₂ p n ∈ O)
    {tf df : ℕ → ℂ} {δB δ1 δp : ℂ}
    (hδ : δB = δp) (hδO : δp ∈ O) (hδdiff : InTwoO O (δp - δ1))
    (hdf : DphiBlocks df (evenCoeff G) (fun n => G.P.η n) D.m₂ p δB δ1 δp)
    (htrace : tf (p ^ 2) = thetaMul (Hp (evenCoeff G) (fun n => G.P.η n) D.m₂ p) (p ^ 3) + df p)
    (hmatch : InTwoO O (tf (p ^ 2) -
      thetaMul (Hp (evenCoeff G) (fun n => G.P.η n) D.m₂ p) (p ^ 2 * p')))
    (hno : ∀ U : Finset ℕ, U.Nonempty →
      (∀ q ∈ U, q.Prime ∧ Nat.Coprime q D.m₂ ∧ jacobiSym W.kfin q = 1) → RevGen S G.r U = 0) :
    (8 : ℤ) ∣ (p : ℤ) + 1 - apk W p := by
  classical
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hpM) (dvd_trans (by decide : 2 ∣ 8) D.eight₂)
  have hpN : ¬ p ∣ G.P.N := fun hd => hpS (G.P.hNS p hp.out hd)
  have hN : G.P.N ≠ 0 := fun e => hpN (by rw [e]; exact dvd_zero _)
  obtain ⟨hη0, hηinv⟩ :=
    dirichletValue_unit_of_coprime hN G.P.η (hp.out.coprime_iff_not_dvd.mpr hpN) O hηO
  have hrec := evenCoeff_shell G hpS
  have hη1 : G.P.η ((1 : ℕ) : ZMod G.P.N) = 1 := by simp
  have hsingle : ∀ q ∈ ({p} : Finset ℕ), q.Prime ∧ q.Coprime D.m₂ ∧ jacobiSym W.kfin q = 1 := by
    simpa using (show p.Prime ∧ p.Coprime D.m₂ ∧ jacobiSym W.kfin p = 1 from ⟨hp.out, hpM, hkp⟩)
  have hpair : ∀ q ∈ ({p, p'} : Finset ℕ), q.Prime ∧ q.Coprime D.m₂ ∧ jacobiSym W.kfin q = 1 := by
    intro q hq
    simp only [mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact ⟨hp.out, hpM, hkp⟩
    · exact ⟨hp', hp'M, hkp'⟩
  have hb₀ := evenCoeff_factor_of_no_reading G O hodd hz hlow
    (fun q hq => (hsingle q hq).1) (hno {p} (by simp) hsingle)
  have hb₁ : InTwoO O (Bp (evenCoeff G) (G.P.η p) p 1) := by
    apply G4a_of_improved_bound hp.out.ne_one
    left
    simpa [show (2 : ℂ) ^ 2 = 4 by norm_num] using hb₀
  have hpp := evenCoeff_factor_of_no_reading G O hodd hz hlow
    (fun q hq => (hpair q hq).1) (hno {p, p'} (by simp) hpair)
  have hpp' : ∃ y ∈ O, evenCoeff G (p * p') = 8 * y := by
    have hne' : p ∉ ({p'} : Finset ℕ) := by simpa only [mem_singleton] using hne.symm
    simpa [Finset.card_insert_of_notMem hne', Finset.prod_insert hne', show (2 : ℂ) ^ 3 = 8 by norm_num] using hpp
  have hd : InTwoO O (df p) :=
    dphi_p_inTwoO_of_det (O := O) (p := p) hp.out hη1 hηO hdf hδ hδO hδdiff hb₁.mem hH
  have h3 : InTwoO O (Hp (evenCoeff G) (fun n => G.P.η n) D.m₂ p (p ^ 3)) :=
    Hp_p_cube_inTwoO (S := D.m₂) hrec hp' hne hH (hηO p) htrace hmatch hd hpp'
  have h3value :=
    Hp_p_cube (a := evenCoeff G) (η := fun n : ℕ => G.P.η n)
      (p := p) (ap := apk W p) (S := D.m₂) hrec (evenCoeff_one G) rfl hpM
  have h3' : InTwoO O ((G.P.η (p : ℕ)) ^ 2 * ((apk W p : ℂ) - 1) *
      ((apk W p : ℂ) - (p : ℂ) - 1) / 4) := h3value ▸ h3

  have h4 : (4 : ℤ) ∣ (p : ℤ) + 1 - apk W p :=
    Int.modEq_iff_dvd.mp (apModFour_curve (W.kfin * ℓ) D.m₂ D.bad₂ p hp.out hpM)
  have hflip (x : ℤ) : -((p : ℤ) + 1 - x) = x - p - 1 := by ring
  have h4' := dvd_neg.mpr h4
  rw [hflip] at h4'
  have h8 := cong_eight_of_inTwoO (p := p) (ap := apk W p) (ηp := G.P.η (p : ℕ))
    hhalf hηinv hη0 (hp.out.odd_of_ne_two hp2) h4' h3'
  apply dvd_neg.mp
  rwa [hflip]

/-- Assembly into the existing App G implication for the selected reading.
The singleton operators are supplied before the no-unit assumption, at all
fresh `K`-split primes of the coordinated even support. -/
theorem kSplitSeed_of_singleton_trace {ℓ : ℕ} {W : WData ℓ} (D : LabelData W)
    {C : CentralNormalization (Ecurve ℓ)} {hk : W.kfin < 0} {S : Finset ℕ}
    (G : GenuineEvenSource C hk S) (O : Subring ℂ)
    (hodd : ∀ d : ℕ, ¬ 2 ∣ d → (d : ℂ)⁻¹ ∈ O)
    (hz : ∀ n, S0Filter S 1 n → G.P.z n ∈ O)
    (hhalf : (2 : ℂ)⁻¹ ∉ O)
    (hηO : ∀ n : ℕ, G.P.η n ∈ O)
    (hlow : ∀ n, S0Filter S 1 n → G.r n ≠ 0 → (omegaN n : ℤ) ≤ padicValRat 2 (G.r n))
    (hpacket : ∀ p : ℕ, ∀ hp : p.Prime, letI : Fact p.Prime := ⟨hp⟩
      p ∉ S → p.Coprime D.m₂ → jacobiSym W.kfin p = 1 →
      (∀ n, Hp (evenCoeff G) (fun n => G.P.η n) D.m₂ p n ∈ O) ∧
      ∃ (p' : ℕ) (tf df : ℕ → ℂ) (δB δ1 δp : ℂ),
        p'.Prime ∧ p' ≠ p ∧ p'.Coprime D.m₂ ∧ jacobiSym W.kfin p' = 1 ∧
        δB = δp ∧ δp ∈ O ∧ InTwoO O (δp - δ1) ∧
        DphiBlocks df (evenCoeff G) (fun n => G.P.η n) D.m₂ p δB δ1 δp ∧
        tf (p ^ 2) = thetaMul (Hp (evenCoeff G) (fun n => G.P.η n) D.m₂ p) (p ^ 3) + df p ∧
        InTwoO O (tf (p ^ 2) -
          thetaMul (Hp (evenCoeff G) (fun n => G.P.η n) D.m₂ p) (p ^ 2 * p'))) :
    AddressGenuine.KSplitSeed W D (RevGen S G.r) := by
  refine ⟨S ∪ D.m₂.primeFactors, fun hno p hp hpS _ hkp => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hpM : p.Coprime D.m₂ := hp.coprime_iff_not_dvd.mpr fun hd =>
    hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, hd, D.m₂_pos.ne'⟩))
  have hS : p ∉ S := fun hs => hpS (Finset.mem_union_left _ hs)
  obtain ⟨hH, p', tf, df, δB, δ1, δp, hp', hne, hp'M, hkp',
    hδ, hδO, hδdiff, hdf, ht, hm⟩ := hpacket p hp hS hpM hkp
  rw [qtwist_Ecurve_eq]
  exact eight_dvd_of_trace_match D G O hodd hz hhalf hlow hpM hp'M hp' hne hkp hkp'
    hS hηO hH hδ hδO hδdiff hdf ht hm hno

end ZInQ.Manuscript.RC.KSplitSeed
