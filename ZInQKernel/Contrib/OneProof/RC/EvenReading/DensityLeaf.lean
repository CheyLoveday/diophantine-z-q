import ZInQKernel.Contrib.OneProof.RC.EvenReading.Leaf

/-! The address density interface, with the even requirements on the transported source. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenReading

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53
open AddressGenuine AppE ZInQ.Manuscript.RC.Even PrintsAnalytic Wiring

/-- The genuine filter implies the squareclass condition modulo the even label
modulus, provided its primes are in the filter support (tex 10293–10295,
10591–10594). Use Hensel at each prime power and the Chinese remainder theorem. -/
theorem evenFilter_of_genuineEven {ℓ : ℕ} {W : WData ℓ} (D : LabelData W)
    {S : Finset ℕ} {r : ℕ → ℚ} (hm : D.m₂.primeFactors ⊆ S) :
    EvenFilter W D (RevGen S r) := by
  intro U hgood hU
  let n := ∏ p ∈ U, p
  have hf : S0Filter S 1 n := (revGen_eq_one (fun p hp => (hgood p hp).1) hU).1
  have hc : n.Coprime D.m₂ := Nat.Coprime.prod_left fun p hp => (hgood p hp).2
  have hs := AppE.isSquare_zmod_of_local n D.m₂ D.m₂_pos.ne' hc (fun p hp hd => by
    simpa only [mul_one] using hf.2.2.2 p (hm (Nat.mem_primeFactors.mpr ⟨hp, hd, D.m₂_pos.ne'⟩)))
  have hcast : (n : ℤ) = ∏ p ∈ U, (p : ℤ) := by simp [n]
  rw [← hcast, Int.cast_natCast]
  exact hs

/-- Choose a source whose support contains the old support, the prime factors
of the companion, and the primes of the even label modulus. -/
theorem genuineEvenSource_for_labels (hWN : WaldspurgerNonvanishing) (hW : WaldspurgerCor2)
    (hR : RamseyAlgebraicModel) (hB : PoleS12.BCDTThmA) (hH : HasseConvergence)
    {ℓ : ℕ} {W : WData ℓ} (hℓ : 0 < ℓ) (hcomp : CompanionLeaf W) (hbranch : ¬ W.OddEmptyUnit)
    (hN : LstarNormalized W.toRCData) (D : LabelData W)
    (Sold : Finset ℕ) (hSold : ∀ p ∈ Sold, p.Prime) :
    ∃ (C : CentralNormalization (Ecurve ℓ)) (hk : W.kfin < 0) (S : Finset ℕ),
      C.Lstar = W.Lstar ∧ Sold ⊆ S ∧ W.kfin.natAbs.primeFactors ⊆ S ∧ D.m₂.primeFactors ⊆ S ∧
        Nonempty (GenuineEvenSource C hk S) := by
  let T := Sold ∪ W.kfin.natAbs.primeFactors ∪ D.m₂.primeFactors
  have hT : ∀ p ∈ T, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact hSold p hp
      · exact Nat.prime_of_mem_primeFactors hp
    · exact Nat.prime_of_mem_primeFactors hp
  obtain ⟨C, hk, S, hC, hTS, hG⟩ :=
    genuineEvenSource_of_companion hWN hW hR hB hH hℓ hcomp hbranch hN T hT
  exact ⟨C, hk, S, hC, fun _ hp => hTS (Finset.mem_union_left _ (Finset.mem_union_left _ hp)),
    fun _ hp => hTS (Finset.mem_union_left _ (Finset.mem_union_right _ hp)),
    fun _ hp => hTS (Finset.mem_union_right _ hp), hG⟩

/-- Remaining address inputs on genuine data. `Sold` is the fixed support before
choosing the companion, containing the ramification of the old fixed label
extensions and of the torsion field. Its avoidance by the companion and its
coverage of `m₁` are recorded here. The even density models and the seed use
the reading of the very same source. Its construction from the existing
Appendix E inputs is `genuineEvenSource_for_labels`. -/
def AddressDensityLeafGenuineEven {ℓ : ℕ} (W : WData ℓ) : Prop :=
  ∃ (D : LabelData W) (Sold S : Finset ℕ) (C : CentralNormalization (Ecurve ℓ))
    (hk : W.kfin < 0) (G : GenuineEvenSource C hk S),
    (∀ p : ℕ, p.Prime → p ∣ D.m₁ → p ∈ Sold) ∧
    (∀ p ∈ Sold, ¬ (p : ℤ) ∣ W.kfin) ∧
    Sold ⊆ S ∧ W.kfin.natAbs.primeFactors ⊆ S ∧ D.m₂.primeFactors ⊆ S ∧ C.Lstar = W.Lstar ∧
    OddDensityModels W D ∧ OddFilter W D ∧ PreparedFilter W D ∧
    EvenDensityModels W D (RevGen S G.r) ∧ KSplitSeed W D (RevGen S G.r)

/-- The genuine even variant supplies the existing Branch 2 density leaf. -/
theorem addressDensityLeaf_of_genuineEven {ℓ : ℕ} {W : WData ℓ} (hcomp : CompanionLeaf W)
    (hbranch : ¬ W.OddEmptyUnit) (h : AddressDensityLeafGenuineEven W) : AddressDensityLeaf W := by
  obtain ⟨D, Sold, S, C, hk, G, hm₁, havoid, _, _, hm₂, hC, hodd, hof, hpf, heven, hseed⟩ := h
  exact ⟨D, RevGen S G.r, freshPrime_of_support D hcomp hbranch hm₁ havoid, hodd, hof, hpf, heven,
    evenFilter_of_genuineEven D hm₂, hseed, evenReading_of_genuineEven D G hC hcomp hbranch⟩

end ZInQ.Manuscript.RC.EvenReading
