import ZInQKernel.Contrib.RC53Assist.DiskOrders.Limit.Transitions

/-!
# Exactness and the two-power Kummer limit

The finite statement is Silverman, *The Arithmetic of Elliptic Curves*, second
edition, Theorem X.4.2. The page locator remains UNVERIFIED: it was not checked.
The limiting statement is a consequence, not a literal quotation of that theorem.

The passage to the limit is proved on representatives. Every continuous cocycle
has bounded two-power exponent; the finite-to-infinite maps commute with point
cohomology and preserve all local conditions. Finite exactness gives the image
and the kernel. The transition on point quotients is multiplication by two, so
every limiting Kummer class has a half. Two-primary torsion then permits division
by every nonzero integer, by the coprime-exponent identity.

Kinds: PROVED. No new arithmetic input is used beyond the finite-level PRINT.
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.DiskOrders

open TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Manuscript.RC53Assist.QuadraticDescent

namespace Limit

/-- A multiple coprime to an exponent is invertible on elements killed by that exponent.
Kind: PROVED; the integer Bézout identity. -/
theorem exists_nsmul_eq_of_coprime_exponent {A : Type*} [AddCommGroup A]
    {n m : ℕ} (hcop : n.Coprime m) (y : A) (hy : m • y = 0) :
    ∃ z : A, n • z = y := by
  have h := Nat.gcd_eq_gcd_ab n m
  rw [hcop.gcd_eq_one, Nat.cast_one] at h
  have hs := congrArg (fun a : ℤ => a • y) h
  simp only [one_smul, add_smul, mul_smul, Nat.cast_smul_eq_nsmul] at hs
  have hzero : m • ((n.gcdB m) • y) = 0 := by
    rw [smul_comm, hy, smul_zero]
  rw [hzero, add_zero] at hs
  exact ⟨(n.gcdA m) • y, hs.symm⟩

/-- A two-primary group divisible by two is divisible by every nonzero natural number.
Kind: PROVED; strong induction and the coprime-exponent identity. -/
theorem divisible_of_twoPrimary {A : Type*} [AddCommGroup A]
    (hprimary : ∀ y : A, ∃ k : ℕ, (2 ^ k) • y = 0)
    (htwo : ∀ y : A, ∃ z : A, (2 : ℕ) • z = y) :
    ∀ (y : A) (n : ℕ), n ≠ 0 → ∃ z : A, n • z = y := by
  have hall : ∀ n : ℕ, n ≠ 0 → ∀ y : A, ∃ z : A, n • z = y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn y
      by_cases heven : 2 ∣ n
      · obtain ⟨m, hm⟩ := heven
        have hmpos : 0 < m := by omega
        have hmn : m < n := by omega
        obtain ⟨z, hz⟩ := htwo y
        obtain ⟨w, hw⟩ := ih m hmn (Nat.ne_of_gt hmpos) z
        exact ⟨w, by rw [hm, mul_smul, hw, hz]⟩
      · obtain ⟨k, hk⟩ := hprimary y
        exact exists_nsmul_eq_of_coprime_exponent
          (((Nat.prime_two.coprime_iff_not_dvd).2 heven).symm.pow_right k) y hk
  exact fun y n hn => hall n hn y

/-- Finite exactness identifies every infinite kernel class with a finite Kummer class.
Kind: PROVED; finite cocycle image and exactness at the finite Selmer term. -/
theorem kernel_class_from_point (hlevels : SilvermanX42TwoPowerLevelPrint)
    (k : ℤ) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (y : H1 (galK (sqrtK k)) (TwoPowerCoeff E)) (hy : inclK (sqrtK k) E y = 0) :
    ∃ (n : ℕ) (P : pointsK (sqrtK k) E),
      levelToInfinite (sqrtK k) E n (levelDelta (sqrtK k) E n P) = y := by
  obtain ⟨n, c, hc⟩ := infinite_class_from_level (sqrtK k) E y
  have hc0 : levelIncl (sqrtK k) E n c = 0 := by
    rw [← inclK_levelToInfinite, hc, hy]
  have hcS : c ∈ selmerLevelK (sqrtK k) E n := by
    change levelIncl (sqrtK k) E n c ∈ shaK (sqrtK k) E
    rw [hc0]
    exact zero_mem _
  have hcSha : levelToSha (sqrtK k) E n ⟨c, hcS⟩ = 0 :=
    Subtype.ext (Subtype.ext hc0)
  obtain ⟨Q, hQ⟩ := ((hlevels k E inferInstance n).2.1 ⟨c, hcS⟩).1 hcSha
  obtain ⟨P, hP⟩ := QuotientAddGroup.mk_surjective Q
  have hPc : levelDelta (sqrtK k) E n P = c := by
    have h := congrArg Subtype.val hQ
    rw [← hP] at h
    exact h
  exact ⟨n, P, by rw [hPc]; exact hc⟩

/-- Every infinite kernel class has a half still in that kernel.
Kind: PROVED; the finite Kummer identification and the commuting transition square. -/
theorem kernel_two_divisible (hlevels : SilvermanX42TwoPowerLevelPrint)
    (k : ℤ) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (y : H1 (galK (sqrtK k)) (TwoPowerCoeff E)) (hy : inclK (sqrtK k) E y = 0) :
    ∃ z, inclK (sqrtK k) E z = 0 ∧ (2 : ℕ) • z = y := by
  obtain ⟨n, P, hP⟩ := kernel_class_from_point hlevels k E y hy
  exact ⟨levelToInfinite (sqrtK k) E (n + 1) (levelDelta (sqrtK k) E (n + 1) P),
    inclK_infinite_levelDelta (sqrtK k) E (n + 1) P,
    (infinite_levelDelta_half (sqrtK k) E n P).trans hP⟩

/-- The image of infinite Selmer is exactly the two-primary Shafarevich–Tate subgroup.
Kind: PROVED; finite-level surjectivity and finite cocycle images. -/
theorem image_eq_primary_of_levels (hlevels : SilvermanX42TwoPowerLevelPrint)
    (k : ℤ) (E : WeierstrassCurve ℚ) [E.IsElliptic] (x : shaK (sqrtK k) E) :
    x ∈ AddCommGroup.primaryComponent (shaK (sqrtK k) E) 2 ↔
      ∃ y ∈ selmerK (sqrtK k) E, inclK (sqrtK k) E y = x := by
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := AddCommGroup.mem_primaryComponent.1 hx
    obtain ⟨c, hc⟩ := (hlevels k E inferInstance n).2.2
      ⟨x, AddSubgroup.torsionBy.nsmul_iff.2 hn⟩
    have hc' : levelIncl (sqrtK k) E n c = (x : H1 (galK (sqrtK k)) E.PointCoeff) :=
      congrArg (fun z : shaLevelK (sqrtK k) E n =>
        ((z : shaK (sqrtK k) E) : H1 (galK (sqrtK k)) E.PointCoeff)) hc
    exact ⟨levelToInfinite (sqrtK k) E n c,
      levelToInfinite_mem_selmer (sqrtK k) E c.2,
      (inclK_levelToInfinite (sqrtK k) E n c).trans hc'⟩
  · rintro ⟨y, _hy, hyx⟩
    obtain ⟨n, hn⟩ := infinite_class_twoPrimary (sqrtK k) E y
    refine AddCommGroup.mem_primaryComponent.2 ⟨n, Subtype.ext ?_⟩
    change (2 ^ n) • (x : H1 (galK (sqrtK k)) E.PointCoeff) = 0
    rw [← hyx, ← map_nsmul, hn, map_zero]

end Limit

/-- The two-clause two-power Kummer statement follows from the literal finite-level PRINT.
Kind: PROVED; the direct-limit argument by finite cocycle representatives and compatible
Kummer transitions. The only input is Silverman X.4.2 at the finite levels. -/
theorem kummerSequenceTwoPowerPrint_of_levels :
    SilvermanX42TwoPowerLevelPrint → KummerSequenceTwoPowerPrint := by
  intro hlevels k E hE
  have := hE
  refine ⟨Limit.image_eq_primary_of_levels hlevels k E, ?_⟩
  intro y hy n hn
  obtain ⟨z, hz⟩ := Limit.divisible_of_twoPrimary
    (A := (inclK (sqrtK k) E).ker)
    (fun x => by
      obtain ⟨a, ha⟩ := Limit.infinite_class_twoPrimary (sqrtK k) E x.1
      exact ⟨a, Subtype.ext ha⟩)
    (fun x => by
      obtain ⟨z, hz, hzx⟩ := Limit.kernel_two_divisible hlevels k E x.1 x.2
      exact ⟨⟨z, hz⟩, Subtype.ext hzx⟩)
    ⟨y, hy⟩ n hn
  exact ⟨z.1, z.2, congrArg Subtype.val hz⟩

/-- The limiting Kummer statement is realized without an additional limiting input.
Kind: PROVED; the finite coefficient Kummer sequence followed by the passage to the limit. -/
theorem kummerSequenceTwoPowerPrint : KummerSequenceTwoPowerPrint :=
  kummerSequenceTwoPowerPrint_of_levels silvermanX42TwoPowerLevelPrint

end ZInQ.Contrib.RC53Assist.DiskOrders
