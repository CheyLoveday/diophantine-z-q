import ZInQKernel.Contrib.OneProof.RC.Even.EvenPhase
import ZInQKernel.Contrib.OneProof.RC.Symbols.SymbolDef
import ZInQKernel.Contrib.OneProof.RC.KSplitOldUnit.Alignment

/-! The original negative source at its fixed reference and attained depth. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KSplitOldUnit

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC.Even PrintsAnalytic Symbols

/-- The original squareclasses and the initial coprimality sieve (tex 7793–7810,
8148–8155). Only `S₀` prescribes squareclasses. -/
def oldRetained (S₀ B : Finset ℕ) (D₀ d : ℕ) : Prop :=
  S0Filter S₀ D₀ d ∧ ∀ p ∈ B, ¬ p ∣ d

/-- The data from `EvenPhaseData.minimum_sieved` for the original curve and
sign minus one. Both the square identity and the depth concern this same form
and its rational parts, on its original retained filter. -/
structure OldSource {ℓ : ℕ} (C : CentralNormalization (Ecurve ℓ)) (S₀ B : Finset ℕ)
    (D₀ : ℕ) where
  phase : EvenPhaseData (Ecurve ℓ) C (-1) S₀ D₀
  ref_ne : C.Lstar (-(D₀ : ℤ)) ≠ 0
  r : ℕ → ℚ
  depth : ℤ
  coeff : ∀ d, oldRetained S₀ B D₀ d →
    hiwCoeff phase.g d / hiwCoeff phase.g D₀ = phase.z d * (r d : ℂ) ∧
      r d ^ 2 = C.Lstar (-(d : ℤ)) / C.Lstar (-(D₀ : ℤ))
  attained : ∃ d, oldRetained S₀ B D₀ d ∧ r d ≠ 0 ∧
    padicValRat 2 (r d) - omegaN d = depth
  lower : ∀ d, oldRetained S₀ B D₀ d → r d ≠ 0 →
    depth ≤ padicValRat 2 (r d) - omegaN d

/-- Apply the existing (E.11) and minimum theorem to the given old form,
reference and initial sieve (tex 8136–8155, 8193–8199). -/
theorem oldSource_of_phase {ℓ : ℕ} {C : CentralNormalization (Ecurve ℓ)}
    {S₀ B : Finset ℕ} {D₀ : ℕ} (P : EvenPhaseData (Ecurve ℓ) C (-1) S₀ D₀)
    (h₀ : C.Lstar (-(D₀ : ℤ)) ≠ 0) (hB : ∀ p ∈ B, ¬ p ∣ D₀)
    (hW : WaldspurgerCor2) (hE : (Ecurve ℓ).IsElliptic)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist (Ecurve ℓ) h) F)
    (h9 : EvenLowerBound (Ecurve ℓ) C) :
    ∃ O : OldSource C S₀ B D₀, O.phase = P := by
  have h₀' : C.Lstar ((-1 : ℤ) * (D₀ : ℤ)) ≠ 0 := by simpa using h₀
  obtain ⟨r, hc, δ, ⟨d, hd, hdB, hdne, hδ⟩, hlow⟩ :=
    P.minimum_sieved hW hE (Or.inr rfl) h₀' hcont h9 B hB
  refine ⟨⟨P, h₀, r, δ, ?_, ⟨d, ⟨hd, hdB⟩, hdne, hδ⟩, ?_⟩, rfl⟩
  · intro m hm
    simpa only [neg_one_mul] using hc m (P.filter_mem m hm.1)
  · exact fun m hm => hlow m hm.1 hm.2

/-- The signed avoidance of the initial sieve becomes the required
avoidance at the positive Fourier index (tex 2596–2598). -/
theorem oldRetained_of_companion_avoidance {S₀ B : Finset ℕ} {D₀ : ℕ} {k : ℤ}
    (hF : S0Filter S₀ D₀ k.natAbs) (havoid : ∀ p ∈ B, ¬ (p : ℤ) ∣ k) :
    oldRetained S₀ B D₀ k.natAbs :=
  ⟨hF, fun p hp hd => havoid p hp (Int.natCast_dvd.mpr hd)⟩

/-- The local filter comparison at tex 10293–10297, with the initial
coprimality sieve kept as well. -/
theorem oldRetained_mul_of_new_filter {S₀ B S : Finset ℕ} {D₀ d n : ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hS₀ : S₀ ⊆ S) (hB : B ⊆ S)
    (hdS : d.primeFactors ⊆ S) (hd : oldRetained S₀ B D₀ d)
    (hn : S0Filter S 1 n) : oldRetained S₀ B D₀ (d * n) := by
  have hnS (p : ℕ) (hp : p ∈ S₀) := hn.2.2.1 p (hS₀ hp)
  have hcop := coprime_of_new_support hd.1.1.ne' hdS hn.2.2.1
  refine ⟨mul_old_filter (fun p hp => hS p (hS₀ hp)) hd.1.1 hd.1.2.1
    hd.1.2.2.1 hd.1.2.2.2 hn.1 hn.2.1 hnS ?_ hcop, ?_⟩
  · intro p hp
    simpa only [mul_one] using hn.2.2.2 p (hS₀ hp)
  · intro p hp hpdiv
    exact ((hS p (hB hp)).dvd_mul.mp hpdiv).elim (hd.2 p hp) (hn.2.2.1 p (hB hp))

/-- The companion must read one on the separate, original negative symbol
at its fixed depth (tex 2595–2599, 10260, 10312–10314). This is the added
selection certificate at the already chosen `k`. -/
def CompanionOldUnit {ℓ : ℕ} {C : CentralNormalization (Ecurve ℓ)}
    {S₀ B : Finset ℕ} {D₀ : ℕ} (O : OldSource C S₀ B D₀) (k : ℤ) : Prop :=
  coeffSymbol (fun d => (O.r d : ℚ_[2])) O.depth (oldRetained S₀ B D₀) k.natAbs = 1

/-- Unpack the original symbol at the unsigned Fourier index. In particular,
a unit carries both retention and the valuation equality `hUnit`. -/
theorem companionOldUnit_iff {ℓ : ℕ} {C : CentralNormalization (Ecurve ℓ)}
    {S₀ B : Finset ℕ} {D₀ : ℕ} (O : OldSource C S₀ B D₀) (k : ℤ) :
    CompanionOldUnit O k ↔ oldRetained S₀ B D₀ k.natAbs ∧ O.r k.natAbs ≠ 0 ∧
      padicValRat 2 (O.r k.natAbs) = (omegaN k.natAbs : ℤ) + O.depth := by
  classical
  unfold CompanionOldUnit coeffSymbol
  rw [ite_eq_iff]
  simp only [one_ne_zero, zero_ne_one, and_false, or_false, and_true]
  simp only [Padic.valuation_ratCast, Rat.cast_ne_zero, omegaN, add_comm]

/-- The fixed source has an old unit somewhere, by its own attained minimum.
The index is selected in the initial filter. This does not identify an
independently chosen nonvanishing twist as that unit. -/
theorem exists_companionOldUnit {ℓ : ℕ} {C : CentralNormalization (Ecurve ℓ)}
    {S₀ B : Finset ℕ} {D₀ : ℕ} (O : OldSource C S₀ B D₀) :
    ∃ k : ℤ, k < 0 ∧ CompanionOldUnit O k := by
  obtain ⟨d, hf, hn, hv⟩ := O.attained
  have hneg : -(d : ℤ) < 0 := by exact neg_neg_of_pos (by exact_mod_cast hf.1.1)
  refine ⟨-(d : ℤ), hneg, (companionOldUnit_iff O _).mpr ?_⟩
  simpa only [Int.natAbs_neg, Int.natAbs_natCast] using
    (show oldRetained S₀ B D₀ d ∧ O.r d ≠ 0 ∧
        padicValRat 2 (O.r d) = (omegaN d : ℤ) + O.depth from ⟨hf, hn, by omega⟩)

end ZInQ.Manuscript.RC.KSplitOldUnit
