import ZInQKernel.Contrib.OneProof.RC.EvenReading.DensityLeaf

/-! The attained depth and the valuation improvement in Appendix G. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KSplitSeed

open Finset AppE EvenReading ZInQ.Manuscript.RC.Even
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

/-- The exact valuation test for the unchanged transported symbol (tex 2068–2089). -/
theorem revGen_eq_one_iff {S U : Finset ℕ} {r : ℕ → ℚ}
    (hprime : ∀ p ∈ U, p.Prime) :
    RevGen S r U = 1 ↔
      S0Filter S 1 (∏ p ∈ U, p) ∧ r (∏ p ∈ U, p) ≠ 0 ∧
        padicValRat 2 (r (∏ p ∈ U, p)) = U.card := by
  refine ⟨revGen_eq_one hprime, ?_⟩
  rintro ⟨hf, hn, hv⟩
  unfold RevGen coeffReading Symbols.coeffSymbol
  have hω := Symbols.card_primeFactors_prod hprime
  have hne : ((r (∏ p ∈ U, p) : ℚ) : ℚ_[2]) ≠ 0 := by exact_mod_cast hn
  exact ite_eq_left ⟨hf, hne, by rw [Padic.valuation_ratCast, hω, zero_add, hv]⟩

/-- Appendix G 10298–10314: two instances of the rational square identity on
the old source and one on the new source give the valuation comparison.
The same fixed old reference value occurs in both old identities. -/
theorem transport_valuation {new oldD oldk LD Lk Lref : ℚ}
    (hnew : new ≠ 0) (hLref : Lref ≠ 0) (hLk : Lk ≠ 0)
    (eNew : new ^ 2 = LD / Lk) (eOldD : oldD ^ 2 = LD / Lref)
    (eOldk : oldk ^ 2 = Lk / Lref) :
    padicValRat 2 new = padicValRat 2 oldD - padicValRat 2 oldk := by
  have hLD : LD ≠ 0 := fun h => (pow_ne_zero 2 hnew) (by simp [eNew, h])
  have holdD : oldD ≠ 0 := fun h => (div_ne_zero hLD hLref) (by simpa [h] using eOldD.symm)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := congrArg (padicValRat 2) eNew
  have h2 := congrArg (padicValRat 2) eOldD
  have h3 := congrArg (padicValRat 2) eOldk
  rw [padicValRat.pow, padicValRat.div hLD hLk] at h1
  rw [padicValRat.pow, padicValRat.div hLD hLref] at h2
  rw [padicValRat.pow, padicValRat.div hLk hLref] at h3
  omega

/-- Attainment of the transported depth at the reference index, tex
10291–10303. In the prime-set reading the reference is the empty set. -/
theorem revGen_empty {ℓ : ℕ} {C : CentralNormalization (Ecurve ℓ)} {k : ℤ}
    {hk : k < 0} {S : Finset ℕ} (G : GenuineEvenSource C hk S) (hLk : C.Lstar k ≠ 0) :
    RevGen S G.r ∅ = 1 := by
  have hf := G.P.D₀_filter
  have he := (G.coeff_eq 1 hf).2
  simp only [Nat.cast_one, one_mul, div_self hLk] at he
  have hn : G.r 1 ≠ 0 := by
    intro h
    simp [h] at he
  have hv := congrArg (padicValRat 2) he
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValRat.pow, padicValRat.one] at hv
  have hv' : padicValRat 2 (G.r 1) = 0 := by omega
  apply (revGen_eq_one_iff (U := ∅) (by simp)).mpr
  simpa using (show S0Filter S 1 1 ∧ G.r 1 ≠ 0 ∧ padicValRat 2 (G.r 1) = 0 from
    ⟨hf, hn, hv'⟩)

/-- Absence of a unit strengthens the bound by one on a tested retained
nonzero coefficient. The integrality used here is that of the rational
coefficient's valuation, as in tex 10323–10325. -/
theorem succ_le_padicValRat_of_revGen_zero {S U : Finset ℕ} {r : ℕ → ℚ}
    (hprime : ∀ p ∈ U, p.Prime) (hF : S0Filter S 1 (∏ p ∈ U, p))
    (hne : r (∏ p ∈ U, p) ≠ 0)
    (hlow : (U.card : ℤ) ≤ padicValRat 2 (r (∏ p ∈ U, p))) (hzero : RevGen S r U = 0) :
    (U.card : ℤ) + 1 ≤ padicValRat 2 (r (∏ p ∈ U, p)) := by
  have h : padicValRat 2 (r (∏ p ∈ U, p)) ≠ (U.card : ℤ) := fun e =>
    zero_ne_one (hzero.symm.trans ((revGen_eq_one_iff hprime).mpr ⟨hF, hne, e⟩))
  exact Int.add_one_le_iff.mpr (lt_of_le_of_ne hlow h.symm)

end ZInQ.Manuscript.RC.KSplitSeed
