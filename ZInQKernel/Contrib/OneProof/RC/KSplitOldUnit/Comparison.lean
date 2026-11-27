import ZInQKernel.Contrib.OneProof.RC.KSplitOldUnit.Source

/-! Transport uses two instances of (E.11) on one old source. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KSplitOldUnit

open ZInQ.Manuscript.RC.Even
open ZInQ.Contrib.CloudB3RC53

/-- Supply all four old inputs to `transported_lower_of_old_unit` from the
exact old source and the selected unit. The denominator is the original
`L_*(-D₀)` in both identities; the numerators use the signed twists `k` and
`n * k` (tex 10288–10315). -/
theorem old_transport_inputs {ℓ : ℕ} {C : CentralNormalization (Ecurve ℓ)}
    {S₀ B S : Finset ℕ} {D₀ : ℕ} (O : OldSource C S₀ B D₀)
    {k : ℤ} (hk : k < 0) (hunit : CompanionOldUnit O k)
    (hS : ∀ p ∈ S, p.Prime) (hS₀ : S₀ ⊆ S) (hB : B ⊆ S)
    (hkS : k.natAbs.primeFactors ⊆ S) :
    C.Lstar k ≠ 0 ∧
    O.r k.natAbs ^ 2 = C.Lstar k / C.Lstar (-(D₀ : ℤ)) ∧
    padicValRat 2 (O.r k.natAbs) = (omegaN k.natAbs : ℤ) + O.depth ∧
    (∀ n, S0Filter S 1 n →
      O.r (k.natAbs * n) ^ 2 = C.Lstar ((n : ℤ) * k) / C.Lstar (-(D₀ : ℤ))) ∧
    (∀ n, S0Filter S 1 n → O.r (k.natAbs * n) ≠ 0 →
      (omegaN (k.natAbs * n) : ℤ) + O.depth ≤ padicValRat 2 (O.r (k.natAbs * n))) := by
  obtain ⟨hF, hne, hv⟩ := (companionOldUnit_iff O k).mp hunit
  have hsign : -(k.natAbs : ℤ) = k := by rw [Int.natCast_natAbs, abs_of_neg hk, neg_neg]
  have hsign_mul (n : ℕ) : -((k.natAbs * n : ℕ) : ℤ) = (n : ℤ) * k := by
    rw [Nat.cast_mul, ← neg_mul, hsign, mul_comm]
  have hOldk := (O.coeff _ hF).2
  rw [hsign] at hOldk
  have hLk : C.Lstar k ≠ 0 := fun e => (pow_ne_zero 2 hne) (by simpa [e] using hOldk)
  have hret (n : ℕ) (hn : S0Filter S 1 n) :=
    oldRetained_mul_of_new_filter hS hS₀ hB hkS hF hn
  refine ⟨hLk, hOldk, hv, fun n hn => ?_, fun n hn hr => ?_⟩
  · simpa only [hsign_mul] using (O.coeff _ (hret n hn)).2
  · have hl := O.lower _ (hret n hn) hr
    omega

end ZInQ.Manuscript.RC.KSplitOldUnit
