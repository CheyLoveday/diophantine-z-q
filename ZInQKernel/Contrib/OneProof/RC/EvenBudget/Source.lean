import ZInQKernel.Contrib.OneProof.RC.AuxInputs.Assembly
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.TypeSupport

/-! The fixed even source, before choosing any operator pool (tex
7793–7810, 8156–8189, 9471–9483). The mask calculation is provenance (c).
There is no moving prime in this source. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenBudget

open AddressGenuine AuxInputs PrintsAnalytic Wiring
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)}

theorem good_iff (hS : SupportSpec W) (p : ℕ) :
    (evenTypes W.S hS.1).Good p ↔ p.Prime ∧ p ∉ W.S := by
  change (p.Prime ∧ p.Coprime (conductor W.S)) ↔ _
  constructor
  · rintro ⟨hp, hc⟩
    exact ⟨hp, fun hs => (hp.coprime_iff_not_dvd.mp hc) ((conductor_support hS.1 hS.2.1 hp).mpr hs)⟩
  · rintro ⟨hp, hs⟩
    exact ⟨hp, hp.coprime_iff_not_dvd.mpr (fun h => hs ((conductor_support hS.1 hS.2.1 hp).mp h))⟩

theorem fixed_support (hS : SupportSpec W) :
    (evenTypes W.S hS.1).m.primeFactors = W.S := by
  ext p
  change p ∈ (conductor W.S).primeFactors ↔ _
  rw [Nat.mem_primeFactors]
  exact ⟨fun ⟨hp, hd, _⟩ => (conductor_support hS.1 hS.2.1 hp).mp hd,
    fun hp => ⟨hS.1 p hp, (conductor_support hS.1 hS.2.1 (hS.1 p hp)).mpr hp,
      (conductor_pos hS.1).ne'⟩⟩

theorem fresh_domains (P : EvenSource W L τ) (hS : SupportSpec W)
    {p : ℕ} {U : Finset ℕ} (hp : (evenTypes W.S hS.1).Good p) (hU : p ∉ U) :
    p ∉ W.S ∪ U ∧ p.Coprime P.phaseData.N := by
  have hout := ((good_iff hS p).mp hp).2
  exact ⟨fun h => (Finset.mem_union.mp h).elim hout hU,
    hp.1.coprime_iff_not_dvd.mpr (fun hd => hout (P.phaseData.hNS p hp.1 hd))⟩

theorem stationary_radicals (hS : SupportSpec W) :
    letI : NeZero (conductor W.S) := ⟨(conductor_pos hS.1).ne'⟩
    TraceLimits.TypeDetectsRadicals (L := SqClass (conductor W.S)) (typChar (conductor W.S)) W.S := by
  letI : NeZero (conductor W.S) := ⟨(conductor_pos hS.1).ne'⟩
  apply TraceLimits.typChar_detects_radicals
  · exact (show (4 : ℕ) ∣ 8 by decide).trans (eight_dvd_conductor W.S)
  · intro p hp
    by_cases h : p = 2
    · subst p
      exact eight_dvd_conductor W.S
    · exact (Nat.mul_dvd_mul (show (4 : ℕ) ∣ 8 by decide)
        (Finset.dvd_prod_of_mem id (Finset.mem_erase.mpr ⟨h, hp⟩)))

/-- The support and type mask is invariant under multiplication by a good
square, including the zero index. -/
theorem keep_mul_sq (S : Finset ℕ) (τ : SqClass (conductor S)) (n m : ℕ)
    (hm : m ≠ 0) (hc : m.Coprime (conductor S)) :
    (n * m ^ 2 ≠ 0 ∧ (n * m ^ 2).Coprime (conductor S) ∧
      sqClassOf (conductor S) ((n * m ^ 2 : ℕ) : ℤ) = τ) ↔
    (n ≠ 0 ∧ n.Coprime (conductor S) ∧ sqClassOf (conductor S) (n : ℤ) = τ) := by
  have hm₂ : (m ^ 2).Coprime (conductor S) := hc.pow_left 2
  have hc' : (n * m ^ 2).Coprime (conductor S) ↔ n.Coprime (conductor S) :=
    Nat.coprime_mul_iff_left.trans (and_iff_left hm₂)
  have htyp (hn : n.Coprime (conductor S)) :
      sqClassOf (conductor S) ((n * m ^ 2 : ℕ) : ℤ) = sqClassOf (conductor S) (n : ℤ) := by
    rw [Nat.cast_mul, sqClassOf_mul (isUnit_natCast_of_coprime hn)
      (isUnit_natCast_of_coprime hm₂), Nat.cast_pow, pow_two,
      sqClassOf_mul (isUnit_natCast_of_coprime hc) (isUnit_natCast_of_coprime hc),
      sqClass_add_self]
    exact _root_.add_zero (sqClassOf (conductor S) (n : ℤ))
  constructor
  · rintro ⟨hn, hnC, ht⟩
    exact ⟨left_ne_zero_of_mul hn, hc'.mp hnC, (htyp (hc'.mp hnC)).symm.trans ht⟩
  · rintro ⟨hn, hnC, ht⟩
    exact ⟨mul_ne_zero hn (pow_ne_zero _ hm), hc'.mpr hnC, (htyp hnC).trans ht⟩

theorem squarefree_phase (P : EvenSource W L τ) (hS : SupportSpec W)
    {D : ℕ} (hD : evenFilter W.S τ D) :
    P.sievedCoeff D = P.phaseData.z D * (P.r D : ℂ) ∧
      ∃ k : ℕ, P.phaseData.z D ^ (2 ^ k) = 1 := by
  have hr := P.phaseData.filter_mem D
    ((s0Filter_iff_type hS.1 hS.2.1 P.reference.2.2.1).mpr
      ⟨hD.1, hD.2.1, hD.2.2.1, hD.2.2.2.trans P.reference.2.2.2.symm⟩)
  refine ⟨?_, P.phaseData.z_root D hr⟩
  have hk : D ≠ 0 ∧ D.Coprime (conductor W.S) ∧ sqClassOf (conductor W.S) (D : ℤ) = τ :=
    ⟨hD.1.ne', hD.2.2⟩
  simpa only [EvenSource.sievedCoeff, ite_eq_left hk] using (P.coeff D hD).1

theorem sieved_off_squarefree (P : EvenSource W L τ) {D : ℕ}
    (hD : Squarefree D) (hoff : ¬ evenFilter W.S τ D) :
    P.sievedCoeff D = 0 := by
  apply ite_eq_right
  intro h
  exact hoff ⟨Nat.pos_of_ne_zero h.1, hD, h.2⟩

/-- Exact signed recurrence for the normalized and sieved complex
coefficients. At negative sign the ratio of the characters is trivial. -/
theorem sieved_recurrence (P : EvenSource W L τ) (hS : SupportSpec W)
    {p : ℕ} (hp : (evenTypes W.S hS.1).Good p) :
    letI : Fact p.Prime := ⟨hp.1⟩
    RecAt p (P.phaseData.η p) 1 ((Ecurve ℓ).LFunction p) P.sievedCoeff := by
  classical
  letI : Fact p.Prime := ⟨hp.1⟩
  have hpN := (fresh_domains P hS (U := ∅) hp (Finset.notMem_empty p)).2
  have hψ : P.phaseData.ψ p = P.phaseData.η p := by
    have h := P.phaseData.hψη p hpN
    simpa [kronecker, kroneckerTwo] using h.symm
  intro n
  have he := E12_of_eigenspace P.phaseData.hN P.phaseData.ψ P.phaseData.η
    (Or.inr rfl : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1)
    P.phaseData.hψη P.phaseData.hg hp.1 (hp.1.coprime_iff_not_dvd.mp hpN) n
  rw [hψ, ← jacobiSym.legendreSym.to_jacobiSym] at he
  let keep := fun n : ℕ => n ≠ 0 ∧ n.Coprime (conductor W.S) ∧
    sqClassOf (conductor W.S) (n : ℤ) = τ
  have hk (n : ℕ) : keep (p ^ 2 * n) ↔ keep n := by
    rw [mul_comm]
    exact keep_mul_sq W.S τ n p hp.1.ne_zero hp.2
  have hd (h : p ^ 2 ∣ n) : keep (n / p ^ 2) ↔ keep n := by
    have hh := hk (n / p ^ 2)
    rw [Nat.mul_div_cancel' h] at hh
    exact hh.symm
  change P.sievedCoeff (p ^ 2 * n) =
    (P.phaseData.η p * (((Ecurve ℓ).LFunction p : ℤ) - 1 * legendreSym p (-(n : ℤ)) : ℤ) : ℂ) *
      P.sievedCoeff n - (p : ℂ) * P.phaseData.η p ^ 2 * divCoeff P.sievedCoeff (p ^ 2) n
  have hc (n : ℕ) : P.sievedCoeff n =
      if keep n then hiwCoeff P.phaseData.g n / hiwCoeff P.phaseData.g P.D₀ else 0 := rfl
  rw [hc (p ^ 2 * n), hc n, divCoeff]
  by_cases hn : keep n
  · by_cases h : p ^ 2 ∣ n
    · rw [ite_eq_left ((hk n).mpr hn), ite_eq_left hn, ite_eq_left h, hc, ite_eq_left ((hd h).mpr hn), he, ite_eq_left h]
      simp only [lcoeff, Int.cast_sub, one_mul]
      ring
    · rw [ite_eq_left ((hk n).mpr hn), ite_eq_left hn, ite_eq_right h, he, ite_eq_right h]
      simp only [lcoeff, Int.cast_sub, one_mul]
      ring
  · by_cases h : p ^ 2 ∣ n
    · rw [ite_eq_right (fun h => hn ((hk n).mp h)), ite_eq_right hn, ite_eq_left h, hc, ite_eq_right (fun e => hn ((hd h).mp e))]
      simp
    · rw [ite_eq_right (fun h => hn ((hk n).mp h)), ite_eq_right hn, ite_eq_right h]
      simp

theorem even_level_ne_zero (P : EvenSource W L τ) : P.phaseData.N ≠ 0 := by
  obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (W.S.sup id + 1)
  intro hN
  have hs := P.phaseData.hNS p hp (hN ▸ dvd_zero p)
  have h := Finset.le_sup (f := id) hs
  exact (Nat.not_succ_le_self _) (hle.trans h)

theorem sieved_mem_Qbar (P : EvenSource W L τ) (hS : SupportSpec W) (n : ℕ) :
    P.sievedCoeff n ∈ AppE.Qbar := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hzero : n = 0
    · subst n
      simpa [EvenSource.sievedCoeff] using (zero_mem AppE.Qbar)
    by_cases hs : Squarefree n
    · by_cases hn : evenFilter W.S τ n
      · obtain ⟨he, k, hk⟩ := squarefree_phase P hS hn
        rw [he]
        exact mul_mem (AppE.mem_Qbar_of_pow_eq_one (by positivity) hk) (AppE.Qbar.algebraMap_mem (P.r n))
      · rw [sieved_off_squarefree P hs hn]
        exact zero_mem _
    have hsq := Nat.squarefree_iff_prime_squarefree.not.mp hs
    push Not at hsq
    obtain ⟨p, hp, hpd⟩ := hsq
    have hd : p ^ 2 ∣ n := by simpa [pow_two] using hpd
    by_cases hpS : p ∈ W.S
    · have hnC : ¬ n.Coprime (conductor W.S) := fun hc =>
        (coprime_conductor hS.1 hS.2.1 n).mp hc p hpS
          ((dvd_pow_self p (by decide : 2 ≠ 0)).trans hd)
      simpa [EvenSource.sievedCoeff, hnC] using (zero_mem AppE.Qbar)
    have hgood := (good_iff hS p).mpr ⟨hp, hpS⟩
    letI : Fact p.Prime := ⟨hp⟩
    letI : NeZero P.phaseData.N := ⟨even_level_ne_zero P⟩
    let m := n / p ^ 2
    have hm : m < n :=
      Nat.div_lt_self (Nat.pos_of_ne_zero hzero) (Nat.one_lt_pow (by decide) hp.one_lt)
    have hh := (sieved_recurrence P hS hgood) m
    rw [Nat.mul_div_cancel' hd] at hh
    rw [hh]
    have hη := AppE.dirichlet_mem_Qbar P.phaseData.η (p : ZMod P.phaseData.N)
    apply sub_mem (mul_mem (mul_mem hη (intCast_mem _ _)) (ih m hm))
    apply mul_mem (mul_mem (natCast_mem _ _) (pow_mem hη _))
    unfold divCoeff
    split_ifs
    · exact ih _ ((Nat.div_le_self m _).trans_lt hm)
    · exact zero_mem _

/-- All the normalized coefficients belong to one algebraic field with a
fixed complex map, uniformly in the operator budget. -/
def algebraicCoeff (P : EvenSource W L τ) (hS : SupportSpec W) (n : ℕ) : AppE.Qbar :=
  ⟨P.sievedCoeff n, sieved_mem_Qbar P hS n⟩

theorem algebraicCoeff_complex (P : EvenSource W L τ) (hS : SupportSpec W) (n : ℕ) :
    (algebraicCoeff P hS n : ℂ) = P.sievedCoeff n :=
  rfl



end ZInQ.Manuscript.RC.EvenBudget
