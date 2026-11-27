import ZInQKernel.Contrib.OneProof.RC.KSplitOldUnit.Comparison
import ZInQKernel.Contrib.OneProof.RC.KSplitSeed.Sieve

/-! Apply the lower bound to the actual transported source. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KSplitOldUnit

open ZInQ.Manuscript.RC.Even EvenReading Wiring KSplitSeed
open ZInQ.Contrib.CloudB3RC53

/-- The transported lower bound on the actual sign-plus-one source for
`W.kfin`, with no independent old square or lower-bound comparison inputs.
The only selection certificate is the old reading at this same `W.kfin`. -/
theorem transported_lower_of_companion_old_unit {ℓ : ℕ} {W : WData ℓ}
    {C : CentralNormalization (Ecurve ℓ)} {S₀ B S : Finset ℕ} {D₀ : ℕ}
    (O : OldSource C S₀ B D₀) {hk : W.kfin < 0}
    (G : GenuineEvenSource C hk S) (hS₀ : S₀ ⊆ S) (hB : B ⊆ S)
    (hkS : W.kfin.natAbs.primeFactors ⊆ S) (hunit : CompanionOldUnit O W.kfin) :
    ∀ n, S0Filter S 1 n → G.r n ≠ 0 → (omegaN n : ℤ) ≤ padicValRat 2 (G.r n) := by
  obtain ⟨hLk, hOldk, hUnit, hOld, hOldLow⟩ :=
    old_transport_inputs O hk hunit G.P.hS₀ hS₀ hB hkS
  exact transported_lower_of_old_unit G hkS O.r (C.Lstar (-(D₀ : ℤ))) O.depth
    O.ref_ne hLk hOldk hUnit hOld hOldLow

end ZInQ.Manuscript.RC.KSplitOldUnit
