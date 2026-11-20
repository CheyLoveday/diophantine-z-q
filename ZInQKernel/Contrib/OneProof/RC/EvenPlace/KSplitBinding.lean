import ZInQKernel.Contrib.OneProof.RC.EvenPlace.BudgetBinding
import ZInQKernel.Contrib.OneProof.RC.EvenPlace.Singleton
import ZInQKernel.Contrib.OneProof.RC.KSplitSeed.Seed

/-! The transported App E source has integral singleton divisions in the
complex image of the very same valuation ring used for the even budget. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenPlace

open ZInQ.Manuscript AddressGenuine AuxInputs ZInQ.Manuscript.RC.Even EvenBudget EvenReading KSplit KSplitSeed Wiring
open ZInQ.Contrib.CloudB3RC53
open NumberField

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {hk : W.kfin < 0} {S : Finset ℕ} {τ : SqClass (conductor W.S)}
variable {F : IntermediateField ℚ ℂ} [NumberField F]

/-- The coefficient and division inputs for the singleton trace at a
fixed place. The last field already holds without a no-reading hypothesis. -/
structure SingletonCoefficientsAt (D : LabelData W) (G : GenuineEvenSource L hk S)
    (V : Place F) : Prop where
  hodd : ∀ d : ℕ, ¬ 2 ∣ d → (d : ℂ)⁻¹ ∈ V.complexIntegers
  hhalf : (2 : ℂ)⁻¹ ∉ V.complexIntegers
  hz : ∀ n, S0Filter S 1 n → G.P.z n ∈ V.complexIntegers
  hηO : ∀ n : ℕ, G.P.η n ∈ V.complexIntegers
  divisions : ∀ p : ℕ, p.Prime → p.Coprime D.m₂ → ∀ n,
    Bp (evenCoeff G) (G.P.η p) p n ∈ V.complexIntegers ∧
      Hp (evenCoeff G) (fun j => G.P.η j) D.m₂ p n ∈ V.complexIntegers

/-- Specialize the integer divisions to the actual positive companion
source. The support alignment is the address input; the ordinary
squarefree depth is the output of `transported_lower_of_old_unit`. -/
theorem singletonCoefficientsAt_of_shell (D : LabelData W) (G : GenuineEvenSource L hk S)
    {V : Place F} (H : PhaseScalarsAt G.P V)
    (hS : ∀ q, q.Prime → (q ∈ S ↔ q ∣ D.m₂))
    (hlow : ∀ n, S0Filter S 1 n → G.r n ≠ 0 → (omegaN n : ℤ) ≤ padicValRat 2 (G.r n)) :
    SingletonCoefficientsAt D G V := by
  classical
  refine ⟨V.odd_inv_mem, V.half_not_mem, fun n _ => H.phase_mem n, fun n => H.eta_mem n, ?_⟩
  have hM : 2 ∣ D.m₂ := dvd_trans (by decide : 2 ∣ (8 : ℕ)) D.eight₂
  have hzero : evenCoeff G 0 = 0 := by
    have h : ¬ evenUnitSieve S 0 := fun hs => hs.1 2 G.P.two_mem (dvd_zero 2)
    simp [evenCoeff, h]
  have hsupp (n : ℕ) (hn : ¬ n.Coprime D.m₂) : evenCoeff G n = 0 := by
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (n := n.gcd D.m₂)
      (fun h => hn (Nat.coprime_iff_gcd_eq_one.mpr h))
    have hqS := (hS q hq).mpr (hqd.trans (Nat.gcd_dvd_right _ _))
    have h : ¬ evenUnitSieve S n := fun hs => hs.1 q hqS (hqd.trans (Nat.gcd_dvd_left _ _))
    simp [evenCoeff, h]
  intro p hp hpM n
  refine singleton_of_shell (a := evenCoeff G) (η := fun j : ℕ => G.P.η j)
    (adm := S0Filter S 1) (ap := apk W) hM (fun j => H.eta_mem j)
    (fun x y => by simp only [Nat.cast_mul, map_mul]) (by simp)
    (apModFour_curve (W.kfin * ℓ) D.m₂ D.bad₂) hzero hsupp ?_ ?_ ?_ hp hpM n
  · intro j hj h
    rw [evenCoeff_squarefree G hj, ite_eq_right h]
  · intro j hj h
    rw [evenCoeff_squarefree G hj, ite_eq_left h]
    simpa only [zpow_zero, one_mul] using V.scaled_phase_factor (H.phase_mem j) (G.r j)
      0 j.primeFactors.card (fun hr => by simpa only [sub_zero, omegaN] using hlow j h hr)
  · intro q hq hqM
    let : Fact q.Prime := ⟨hq⟩
    exact evenCoeff_shell G (fun h => (hq.coprime_iff_not_dvd.mp hqM) ((hS q hq).mp h))

/-- Both consumers can use a single prime above two in one number field.
The two elliptic sources keep their respective phases and valuations. -/
theorem common_place_for_sources (P : EvenSource W L τ) (hW : SupportSpec W)
    (D : LabelData W) (G : GenuineEvenSource L hk S)
    (hP : PhaseOrigin P.phaseData) (hG : PhaseOrigin G.P)
    (hS : ∀ q, q.Prime → (q ∈ S ↔ q ∣ D.m₂))
    (hlow : ∀ n, S0Filter S 1 n → G.r n ≠ 0 → (omegaN n : ℤ) ≤ padicValRat 2 (G.r n)) :
    ∃ e : ℕ, ∃ V : Place (PhaseField e),
      ∃ (HP : PhaseScalarsAt P.phaseData V) (_ : PhaseScalarsAt G.P V),
        (∀ p, (evenTypes W.S hW.1).Good p → ∃ t : ℕ, (sourceAtPlace P hW HP).η p ^ (2 ^ t) = 1) ∧
        SingletonCoefficientsAt D G V := by
  obtain ⟨e, V, HP, HG⟩ := common_phase_scalars hP hG
  exact ⟨e, V, HP, HG, fun _ => sourceAtPlace_eta_phase P hW HP hP,
    singletonCoefficientsAt_of_shell D G HG hS hlow⟩

/-- The seed consumer can now take only the matching-prime, determinant,
and trace part of its packet, for these same characteristic-zero coefficients. -/
theorem kSplitSeed_of_trace_at_place (D : LabelData W) (G : GenuineEvenSource L hk S)
    {V : Place F} (H : SingletonCoefficientsAt D G V)
    (hlow : ∀ n, S0Filter S 1 n → G.r n ≠ 0 → (omegaN n : ℤ) ≤ padicValRat 2 (G.r n))
    (htrace : ∀ p : ℕ, p.Prime → p ∉ S → p.Coprime D.m₂ → jacobiSym W.kfin p = 1 →
      ∃ (p' : ℕ) (tf df : ℕ → ℂ) (δB δ1 δp : ℂ),
        p'.Prime ∧ p' ≠ p ∧ p'.Coprime D.m₂ ∧ jacobiSym W.kfin p' = 1 ∧
        δB = δp ∧ δp ∈ V.complexIntegers ∧ InTwoO V.complexIntegers (δp - δ1) ∧
        DphiBlocks df (evenCoeff G) (fun n => G.P.η n) D.m₂ p δB δ1 δp ∧
        tf (p ^ 2) = thetaMul (Hp (evenCoeff G) (fun n => G.P.η n) D.m₂ p) (p ^ 3) + df p ∧
        InTwoO V.complexIntegers (tf (p ^ 2) -
          thetaMul (Hp (evenCoeff G) (fun n => G.P.η n) D.m₂ p) (p ^ 2 * p'))) :
    AddressGenuine.KSplitSeed W D (RevGen S G.r) := by
  refine kSplitSeed_of_singleton_trace D G V.complexIntegers H.hodd H.hz H.hhalf H.hηO hlow ?_
  intro p hp hpS hpM hkp
  exact ⟨fun n => (H.divisions p hp hpM n).2, htrace p hp hpS hpM hkp⟩

end ZInQ.Manuscript.RC.EvenPlace
