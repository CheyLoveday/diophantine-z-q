import ZInQKernel.Contrib.OneProof.BergerComparison.Transport

/-! Typecheck the whole conditional chain using a paper-ring basis witness as
input. There is no new published-form hypothesis or change to the headline. -/

open HDec.PkgI4
open BergerBst BmaxOne FontaineSt PanDict
open PanBergerSplit (IsDeRhamU)
open ZInQ.Manuscript.BergerReroute ZInQ.Manuscript.BergerComparison

example
    (ell : (p : ℕ) → [Fact p.Prime] → BdR p)
    (hφ : ∀ (p : ℕ) [Fact p.Prime], FrobeniusTransport p)
    (hRing : ∀ (p : ℕ) [Fact p.Prime],
      Algebra.adjoin ℚ_[p] ((Bmax p : Set (BdR p)) ∪ {ell p}) = BergerBst.Bst p)
    (hPaper : ∀ (p : ℕ) [Fact p.Prime]
      (n : ℕ) (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
      (ρE : GQp p →* GL (Fin n) E), Continuous ρE → IsDeRhamU p ρE →
      ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
        IsAdmissibleT p (Algebra.adjoin ℚ_[p] ((Bmax p : Set (BdR p)) ∪ {ell p}))
          K.fixingSubgroup ρE) : BergerSurveyF := by
  apply bergerSurveyF_of_thm06Print
  intro p _ ε₀ h n E _ ρE hc hdr
  exact isPstFBasis_of_paper p (hφ p) (hRing p) h ρE (hPaper p n E ρE hc hdr)
