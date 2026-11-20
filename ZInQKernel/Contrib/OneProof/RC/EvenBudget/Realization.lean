import ZInQKernel.Contrib.OneProof.RC.EvenBudget.Place
import ZInQKernel.Contrib.OneProof.RC.O12Local.Blocks

/-! Compare the exact even expansions with a constituent model at the
same coefficient place. The independent analytic and attachment inputs
are the only inputs here that mention the weight-two forms. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenBudget

open AddressGenuine AuxInputs Wiring Symbols O12
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

theorem TL_perm_primes {O : Type} [CommRing O] (η a : ℕ → O) {J J' : List ℕ}
    (h : J.Perm J') (hnd : J.Nodup) (hp : ∀ p ∈ J, p.Prime) :
    TL η J a = TL η J' a := by
  induction h with
  | nil => rfl
  | cons p _ ih =>
    rw [TL_cons, TL_cons, ih (List.nodup_cons.mp hnd).2 (fun q hq => hp q (by simp [hq]))]
  | swap p q J =>
    have hp₀ := hp p (by simp)
    have hq₀ := hp q (by simp)
    have hne : q ≠ p := fun e => (List.nodup_cons.mp hnd).1 (by simp [e])
    simp only [TL_cons]
    exact Top_comm _ hq₀.pos hp₀.pos ((Nat.coprime_primes hq₀ hp₀).mpr hne) _ _
  | trans h₁ _ ih₁ ih₂ =>
    exact (ih₁ hnd hp).trans (ih₂ (h₁.nodup_iff.mp hnd) (fun p h => hp p (h₁.mem_iff.mpr h)))

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable (hS : SupportSpec W) {B : ℕ}
variable [NeZero (conductor W.S)]

abbrev Model (P : EvenSource W L τ) (hS : SupportSpec W) (B : ℕ) :=
  GaloisConstituentModel (evenTypes W.S hS.1) P.reading
    (fun p => (Ecurve ℓ).LFunction p) B (typChar (conductor W.S))

variable {X : Model P hS B} [CharZero X.K] (A : FourierData X)
variable (C : SourceAtPlace P X.O X.K)

def evenH (i : Fin 2) (U : Finset ℕ) (n : ℕ) : X.O := by
  classical
  exact if hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p then
    dividedCoeff (source_at_place C hS A.integral_inclusion) i U.toList
      U.nodup_toList (fun p hp => hU p (Finset.mem_toList.mp hp)) n
  else 0

theorem evenH_off (i : Fin 2) {U : Finset ℕ}
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (J : List ℕ) (hJ : J.Nodup) (he : J.toFinset = U) {n : ℕ}
    (hn : ¬ oddPart n ⊆ U) :
    algebraMap X.O X.K (evenH hS A C i U n) =
      scale X.K (P.δ + C.k) U * algebraMap X.O X.K (TL C.η J C.a n) := by
  classical
  have hprime : ∀ p ∈ U, p.Prime := fun p hp => (hU p hp).1
  have hperm : U.toList.Perm J :=
    List.perm_of_nodup_nodup_toFinset_eq U.nodup_toList hJ ((Finset.toList_toFinset U).trans he.symm)
  unfold evenH
  rw [dite_eq_left hU, dividedCoeff_spec, rawNumerator_off _ _
    (fun p hp => hprime p (Finset.mem_toList.mp hp)) (by simpa only [Finset.toList_toFinset] using hn),
    TL_perm_primes _ _ hperm U.nodup_toList (fun p hp => hprime p (Finset.mem_toList.mp hp)),
    Finset.length_toList]
  rfl

theorem evenH_two_fresh (i : Fin 2) {U : Finset ℕ}
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    {n q r : ℕ} (hn : n ≠ 0) (hq : q.Prime) (hr : r.Prime)
    (hqr : q ≠ r) (hqn : ¬ q ∣ n) (hrn : ¬ r ∣ n) (hqU : q ∉ U) (hrU : r ∉ U) :
    (2 : X.O) ∣ ThetaCoeff.timesTheta (evenH hS A C i U) (r * (q * n)) := by
  have hw := two_fresh_weight hn hq hr hqr hqn hrn hqU hrU
  have hoff : ¬ oddPart (r * (q * n)) ⊆ U := by
    intro h
    rw [Finset.sdiff_eq_empty_iff_subset.mpr h, Finset.card_empty] at hw
    omega
  obtain ⟨y, hy⟩ := normalized_double (K := X.K) (source_at_place C hS A.integral_inclusion)
    U.toList U.nodup_toList (fun p hp => hU p (Finset.mem_toList.mp hp)) (n := r * (q * n))
    (by simpa only [Finset.toList_toFinset] using hw)
  have hh : (2 : X.O) ∣ evenH hS A C i U (r * (q * n)) := by
    refine ⟨y, A.integral_inclusion ?_⟩
    rw [evenH_off hS A C i hU U.toList U.nodup_toList (Finset.toList_toFinset U) hoff,
      map_mul, map_ofNat]
    simpa only [scale, Finset.length_toList] using hy
  have hθ := timesTheta_congr (evenH hS A C i U) (r * (q * n))
  simpa only [sub_add_cancel] using dvd_add hθ hh

/-- The ambient good-Hecke formulas must act on the first translate as
well as on the seed. With those formulas, the two fresh Frobenius tests
read an actual coefficient divisible by the integer two. -/
theorem even_two_hecke (i : Fin 2) {U : Finset ℕ}
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    {n q r : ℕ} (hn : n ≠ 0) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hqn : ¬ q ∣ n) (hrn : ¬ r ∣ n) (hqU : q ∉ U) (hrU : r ∉ U)
    {Dq Dr : X.Λ →ₗ[X.O] X.Λ}
    (hqH : TraceLimits.HeckeFourier A.coeff (X.tΛ (X.frob q)) Dq q)
    (hrH : TraceLimits.HeckeFourier A.coeff (X.tΛ (X.frob r)) Dr r)
    (hcoef : A.coeff (r * (q * n)) (X.F U) =
      ThetaCoeff.timesTheta (evenH hS A C i U) (r * (q * n))) :
    (2 : X.O) ∣ A.coeff n (X.tΛ (X.frob q) (X.tΛ (X.frob r) (X.F U))) := by
  have hrq : ¬ r ∣ q := fun h => hqr ((Nat.prime_dvd_prime_iff_eq hr hq).mp h).symm
  have hn' : ¬ r ∣ q * n := fun h => (hr.dvd_mul.mp h).elim hrq hrn
  rw [hqH, ite_eq_right hqn, add_zero, hrH, ite_eq_right hn', add_zero, hcoef]
  exact evenH_two_fresh hS A C i hU hn hq hr hqr hqn hrn hqU hrU

include A in
theorem even_source_symbol (hm : X.m.IsMaximal) {U : Finset ℕ} {q : ℕ}
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hq : (evenTypes W.S hS.1).Good q) (hqU : q ∉ U) {b : X.O}
    (hb : algebraMap X.O X.K b =
      scale X.K (P.δ + C.k) U * algebraMap X.O X.K (C.a ((∏ p ∈ U, p) * q))) :
    Ideal.Quotient.mk X.m b = if P.reading (insert q U) = 0 then 0 else 1 := by
  classical
  let J := insert q U
  let D := ∏ p ∈ J, p
  have hprod : D = (∏ p ∈ U, p) * q :=
    (Finset.prod_insert hqU).trans (mul_comm _ _)
  have hprime : ∀ p ∈ J, p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hq.1
    · exact (hU p hp).1
  have hD : Squarefree D := ((ThetaCoeff.mem_subscripts hprime D).mp
    (Finset.mem_image.mpr ⟨J, Finset.mem_powerset.mpr (Finset.Subset.refl J), rfl⟩)).1
  have hcard : D.primeFactors.card = U.card + 1 := by
    change (∏ p ∈ J, p).primeFactors.card = _
    rw [Nat.primeFactors_prod hprime, Finset.card_insert_of_notMem hqU]
  change _ = (if coeffSymbol (fun n => (P.r n : ℚ_[2])) P.δ (evenFilter W.S τ) D = 0
    then 0 else 1)
  unfold coeffSymbol
  by_cases hd : evenFilter W.S τ D
  · obtain ⟨ζ, hζ, hCD⟩ := source_at_place_phase C hS A.integral_inclusion hd
    have hr : P.r D ≠ 0 → P.δ + (D.primeFactors.card : ℤ) ≤ padicValRat 2 (P.r D) := by
      intro hn
      have hp := P.lower D hd hn
      unfold omegaN at hp
      omega
    have hb' : algebraMap X.O X.K b = algebraMap X.O X.K ζ *
        (2 : X.K) ^ (-(P.δ + (D.primeFactors.card : ℤ))) * (P.r D : X.K) := by
      have hh : -(P.δ + C.k + (U.card : ℤ) + 1) + C.k =
          -(P.δ + (D.primeFactors.card : ℤ)) := by omega
      calc
        _ = algebraMap X.O X.K ζ *
            ((2 : X.K) ^ (-(P.δ + C.k + (U.card : ℤ) + 1)) * (2 : X.K) ^ C.k) *
              (P.r D : X.K) := by rw [hb, ← hprod, hCD, scale]; ring
        _ = _ := by rw [← zpow_add₀ (by norm_num : (2 : X.K) ≠ 0), hh]
    rw [phase_rational_residue A.integral_inclusion hm X.two_mem C.padicInt C.padic C.padic_agree hζ hr hb',
      Padic.valuation_ratCast]
    by_cases h : P.r D ≠ 0 ∧ padicValRat 2 (P.r D) = P.δ + (D.primeFactors.card : ℤ)
    · have h' : evenFilter W.S τ D ∧ (P.r D : ℚ_[2]) ≠ 0 ∧
          padicValRat 2 (P.r D) = P.δ + (D.primeFactors.card : ℤ) :=
        ⟨hd, by exact_mod_cast h.1, h.2⟩
      simp [h, h']
    · have h' : ¬ (evenFilter W.S τ D ∧ (P.r D : ℚ_[2]) ≠ 0 ∧
          padicValRat 2 (P.r D) = P.δ + (D.primeFactors.card : ℤ)) := by
        intro hh
        exact h ⟨by exact_mod_cast hh.2.1, hh.2.2⟩
      simp [h]
  · have hz : C.a D = 0 := place_zero C A.integral_inclusion (sieved_off_squarefree P hD hd)
    have hzero : b = 0 := A.integral_inclusion (by rw [hb, ← hprod, hz, map_zero, mul_zero])
    simp [hd, hzero]

variable (i : Fin 2) (hm : X.m.IsMaximal)
variable (hphase : ∀ p, (evenTypes W.S hS.1).Good p → ∃ t : ℕ, C.η p ^ (2 ^ t) = 1)
variable (hHecke : A.FormwiseHecke)
variable (hF : ∀ U : Finset ℕ, (∀ p ∈ U, (evenTypes W.S hS.1).Good p) → U.card + 1 ≤ B →
  ∀ n, n ≠ 0 → A.coeff n (X.F U) = ThetaCoeff.timesTheta (evenH hS A C i U) n)

/-- Supply the equalities in the existing theta comparison from the exact
even divided expansion. The finite cutoff field is unused by the even arithmetic. -/
def thetaDataOfEven : ThetaData A where
  δ := P.δ + C.k
  truncation := (P.δ + C.k + (B : ℤ) + 2).toNat
  admissible := evenFilter W.S τ
  a := C.a
  η := C.η
  ratio := fun _ => 1
  H := evenH hS A C i
  residue_maximal := hm
  source := source_at_place C hS A.integral_inclusion (P.δ + C.k + (B : ℤ) + 2).toNat
  ratio_sign := fun _ _ => Or.inl rfl
  signed_recur := fun _ hp => source_at_place_recur C hS A.integral_inclusion hp
  eta_phase := hphase
  good_hecke := hHecke
  theta_mod_two := fun U hU hB n hn => hF U hU hB n hn ▸ timesTheta_congr (evenH hS A C i U) n
  H_off_unary := fun _ hU _ J hd hJ n hn =>
    ⟨evenH hS A C i _ n, evenH_off hS A C i hU J hd hJ hn, by simp⟩
  source_symbol := fun _ _ hU hq hqU _ _ hb => even_source_symbol hS A C hm hU hq hqU hb

include C i hm hphase hHecke hF in
/-- Final handoff on the actual forms: attach the existing local sectors
and use the same common field for the source comparison. -/
theorem budgetRealization_of_blocks
    (localBlocks : ∀ (U : Finset ℕ) (q : ℕ) (hqU : q ∈ U)
      (hU : ∀ s ∈ U, (evenTypes W.S hS.1).Good s),
      U.card + 1 ≤ B → ∀ Q : LocalPair q,
      letI : Fact q.Prime := ⟨(hU q hqU).1⟩
      Nonempty (O12Local.Stage A U Q (hU q hqU).1.ne_zero)) :
    P.BudgetRealization hS B := by
  refine ⟨X, A, thetaDataOfEven hS A C i hm hphase hHecke hF, inferInstance,
    O12Local.localInput A localBlocks, ?_⟩
  exact ⟨C.K₀, inferInstance, C.eC, C.eK, C.c, C.k, rfl, rfl, C.complex_coeff, C.integral_coeff⟩


end ZInQ.Manuscript.RC.EvenBudget
