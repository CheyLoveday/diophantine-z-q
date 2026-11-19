import ZInQKernel.Contrib.OneProof.RC.EvenBudget.Valuation

/-! Relate the fixed complex coefficients to their integral images at one
place. The data here concern only the undivided App E source. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenBudget

open AddressGenuine AuxInputs Wiring
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)}
variable {O K : Type} [CommRing O] [Field K] [CharZero K] [Algebra O K]

/-- Compare the two images of the common source field and the phase
values. This says nothing about the divided forms or weight two. -/
structure SourceAtPlace (P : EvenSource W L τ) (O K : Type)
    [CommRing O] [Field K] [Algebra O K] where
  K₀ : Type
  [instField : Field K₀]
  eC : K₀ →+* ℂ
  eK : K₀ →+* K
  c : ℕ → K₀
  η₀ : ℕ → K₀
  k : ℤ
  a : ℕ → O
  η : ℕ → O
  complex_coeff : ∀ n, eC (c n) = P.sievedCoeff n
  complex_eta : ∀ n, eC (η₀ n) = P.phaseData.η n
  integral_coeff : ∀ n, algebraMap O K (a n) = (2 : K) ^ k * eK (c n)
  integral_eta : ∀ n, algebraMap O K (η n) = eK (η₀ n)
  phase_lift : ∀ D, evenFilter W.S τ D → ∃ (z : K₀) (ζ : O),
    eC z = P.phaseData.z D ∧ algebraMap O K ζ = eK z
  padicInt : ℤ_[2] →+* O
  padic : ℚ_[2] →+* K
  padic_agree : ∀ x : ℤ_[2], algebraMap O K (padicInt x) = padic (x : ℚ_[2])

attribute [instance] SourceAtPlace.instField

variable {P : EvenSource W L τ} (C : SourceAtPlace P O K) (hS : SupportSpec W)
variable (inj : Function.Injective (algebraMap O K))

omit [CharZero K] in
include hS inj in
theorem source_at_place_phase {D : ℕ} (hD : evenFilter W.S τ D) :
    ∃ ζ : O, (∃ e : ℕ, ζ ^ (2 ^ e) = 1) ∧
      algebraMap O K (C.a D) = algebraMap O K ζ * (2 : K) ^ C.k * (P.r D : K) := by
  obtain ⟨z, ζ, hz, hζ⟩ := C.phase_lift D hD
  obtain ⟨ha, e, he⟩ := squarefree_phase P hS hD
  have hc : C.c D = z * (P.r D : C.K₀) := by
    apply C.eC.injective
    rw [C.complex_coeff, ha, map_mul, hz, map_ratCast]
  have hzroot : z ^ (2 ^ e) = 1 := C.eC.injective (by rw [map_pow, hz, map_one, he])
  refine ⟨ζ, ⟨e, inj ?_⟩, ?_⟩
  · simp only [map_pow, hζ, ← C.eK.map_pow, hzroot, map_one]
  · rw [C.integral_coeff, hc, map_mul, map_ratCast, hζ]
    ring

omit [CharZero K] in
include inj in
theorem place_zero {n : ℕ} (h : P.sievedCoeff n = 0) : C.a n = 0 := by
  have hc : C.c n = 0 := C.eC.injective (by rw [C.complex_coeff, h, map_zero])
  exact inj (by rw [C.integral_coeff, hc, map_zero, mul_zero, map_zero])

omit [CharZero K] in
include inj in
theorem source_at_place_recur {p : ℕ} (hp : (evenTypes W.S hS.1).Good p) :
    let : Fact p.Prime := ⟨hp.1⟩
    RecAt p (C.η p) 1 ((Ecurve ℓ).LFunction p) C.a := by
  let : Fact p.Prime := ⟨hp.1⟩
  change @RecAt O _ p ⟨hp.1⟩ (C.η p) 1 ((Ecurve ℓ).LFunction p) C.a
  have hc : RecAt p (C.η₀ p) 1 ((Ecurve ℓ).LFunction p) C.c := by
    intro n
    apply C.eC.injective
    have he := (sieved_recurrence P hS hp) n
    simp only [map_sub, map_mul, map_pow, map_natCast, map_intCast, C.complex_coeff, C.complex_eta] at *
    rw [← divCoeff_map, show (fun n => C.eC (C.c n)) = P.sievedCoeff from funext C.complex_coeff]
    exact he
  intro n
  apply inj
  have he := congrArg C.eK (hc n)
  have hd : algebraMap O K (divCoeff C.a (p ^ 2) n) =
      (2 : K) ^ C.k * C.eK (divCoeff C.c (p ^ 2) n) := by
    unfold divCoeff
    split_ifs <;> simp [C.integral_coeff]
  simp only [map_sub, map_mul, map_pow, map_natCast, map_intCast,
    C.integral_coeff, C.integral_eta, hd] at *
  rw [he]
  ring

theorem ap_mod_four (hS : SupportSpec W) {p : ℕ} (hp : (evenTypes W.S hS.1).Good p) :
    (Ecurve ℓ).LFunction p ≡ (p : ℤ) + 1 [ZMOD 4] := by
  have hcov : ∀ q : ℕ, q.Prime → q ∣ 6 * (ℓ : ℤ).natAbs → q ∣ (evenTypes W.S hS.1).m := by
    intro q hq hd
    apply (conductor_support hS.1 hS.2.1 hq).mpr
    rw [Int.natAbs_natCast] at hd
    rcases hq.dvd_mul.mp hd with h6 | hℓ
    · rcases hq.dvd_mul.mp (show q ∣ 2 * 3 from h6) with h2 | h3
      · rw [(Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2]
        exact hS.2.1
      · rw [(Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3]
        exact hS.2.2.1
    · exact hS.2.2.2 q hq hℓ
  simpa only [Int.cast_natCast] using
    FrobCount.apModFour_curve_typeData (evenTypes W.S hS.1) (ℓ : ℤ) hcov p hp

include inj in
/-- This supplies the untruncated even source for the shared shell
arithmetic. Its depth is fixed before any operator budget is chosen. -/
theorem source_at_place :
    ∀ t, SourceHyp t (P.δ + C.k) C.η ((evenTypes W.S hS.1).Good)
      (evenFilter W.S τ) (fun p => (Ecurve ℓ).LFunction p) C.a := by
  intro t
  refine ⟨⟨fun _ hp => hp.1, fun p hp => ?_, fun _ hp => ap_mod_four hS hp,
    fun p hp => ⟨1, Or.inl rfl, source_at_place_recur C hS inj hp⟩,
    place_zero C inj (by simp [EvenSource.sievedCoeff]),
    ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact_mod_cast odd_of_coprime_of_two_dvd (evenTypes W.S hS.1).two_dvd hp.2
  · rintro n ⟨p, hp, hbad⟩
    apply place_zero C inj
    have hnc : ¬ n.Coprime (conductor W.S) := fun h =>
      hbad (good_primeFactors hS.1 h p hp)
    simp [EvenSource.sievedCoeff, hnc]
  · exact fun D hD hn => place_zero C inj (sieved_off_squarefree P hD hn)
  · intro x y
    have he : C.η₀ (x * y) = C.η₀ x * C.η₀ y := C.eC.injective (by
      simp only [map_mul, C.complex_eta, Nat.cast_mul])
    exact inj (by rw [C.integral_eta, he, map_mul, map_mul, C.integral_eta, C.integral_eta])
  · have he : C.η₀ 1 = 1 := C.eC.injective (by rw [C.complex_eta]; simp)
    exact inj (by rw [C.integral_eta, he, map_one, map_one])
  · intro D hD hadm
    let e : ℤ := min (t : ℤ) (P.δ + C.k + ArithmeticFunction.cardDistinctFactors D)
    change (2 : O) ^ e.toNat ∣ C.a D
    by_cases he : 0 ≤ e
    · obtain ⟨ζ, _, hζ⟩ := source_at_place_phase C hS inj hadm
      refine phase_rational_dvd inj C.padicInt C.padic C.padic_agree ?_ hζ
      intro hr
      rw [Int.toNat_of_nonneg he]
      have hh := P.lower D hadm hr
      have hc : ArithmeticFunction.cardDistinctFactors D = D.primeFactors.card := by
        rw [← card_oddPart_of_squarefree hD, oddPart_of_squarefree hD]
      unfold omegaN at hh
      dsimp [e]
      rw [hc]
      omega
    · rw [Int.toNat_of_nonpos (by omega), pow_zero]
      exact one_dvd _

omit [CharZero K] in
include inj in
/-- Retaining the scalar-character order from Appendix E gives the phase
condition required by the (O.12) comparison on the whole good domain. -/
theorem eta_phase_of_character
    (horder : ∃ e : ℕ, P.phaseData.η ^ (2 ^ e) = 1)
    {p : ℕ} (hp : (evenTypes W.S hS.1).Good p) :
    ∃ t : ℕ, C.η p ^ (2 ^ t) = 1 := by
  let : NeZero P.phaseData.N := ⟨even_level_ne_zero P⟩
  obtain ⟨e, he⟩ := horder
  have hpN := (fresh_domains P hS (U := ∅) hp (Finset.notMem_empty p)).2
  have hu : IsUnit (p : ZMod P.phaseData.N) := (ZMod.isUnit_iff_coprime p _).mpr hpN
  have hη : (P.phaseData.η p) ^ (2 ^ e) = 1 := by
    rw [← MulChar.pow_apply' P.phaseData.η (pow_ne_zero e two_ne_zero), he, MulChar.one_apply hu]
  have hk : (C.η₀ p) ^ (2 ^ e) = 1 :=
    C.eC.injective (by rw [map_pow, C.complex_eta, map_one, hη])
  refine ⟨e, inj ?_⟩
  rw [map_pow, C.integral_eta, ← map_pow, hk, map_one, map_one]

#print axioms eta_phase_of_character

#print axioms source_at_place_phase
#print axioms place_zero
#print axioms source_at_place_recur
#print axioms ap_mod_four
#print axioms source_at_place

end ZInQ.Manuscript.RC.EvenBudget
