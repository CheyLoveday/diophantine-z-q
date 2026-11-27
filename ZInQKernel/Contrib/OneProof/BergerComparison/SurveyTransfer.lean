import ZInQKernel.Contrib.OneProof.BergerComparison.SemistableComparison
import ZInQKernel.Contrib.OneProof.BergerComparison.DeRhamBasis

/-! Transfer the paper-ring basis implication to the existing survey row. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst BmaxOne FontaineSt BergerReroute PanDict

set_option maxHeartbeats 650000

/-- The paper-ring basis implication supplies the existing draft in
its Fontaine form, and hence the survey row. -/
theorem bergerSurveyF_of_cyclotomic_basis
    (hPaper : ∀ (p : ℕ) [Fact p.Prime]
      (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀)
      (n : ℕ) (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
      (ρE : GQp p →* GL (Fin n) E), Continuous ρE → HasDeRhamBasis p ρE →
      ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
        IsAdmissibleT p (Algebra.adjoin ℚ_[p]
          ((Bmax p : Set (BdR p)) ∪ {cyclotomicCoordinate p h})) K.fixingSubgroup ρE) :
    BergerSurveyF := by
  apply bergerSurveyF_of_thm06Print
  intro p _ ε₀ h n E _ ρE hc hdr
  exact isPstFBasis_of_paper p (frobeniusTransport p)
    (cyclotomicCoordinate_adjoin_eq p h) h ρE
    (hPaper p ε₀ h n E ρE hc (deRhamBasis_of_isDeRhamU p ρE hdr))

end ZInQ.Manuscript.BergerComparison
