import ZInQKernel.Contrib.OneProof.BergerComparison.SemistableDescent
import ZInQKernel.Contrib.OneProof.BergerComparison.CyclotomicBranch

/-! The actual semistable maps give basis transport over the same finite
extension. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst BmaxOne FontaineSt BergerReroute

variable (p : ℕ) [Fact p.Prime]

set_option maxHeartbeats 650000

/-- Compare the normalized paper ring to the embedded Fontaine ring
without changing the finite extension or the representation. -/
theorem bergerPaperStComparison {ε : PreTilt 𝓞_ℂ_[p] p} (hε : IsGenEps p ε) :
    BergerPaperStComparison p (cyclotomicCoordinate p hε) := by
  intro ε₀ h K _ n E _ ρE _ hBasis
  exact isAdmissible_of_pstF p h K.fixingSubgroup ρE
    ((isAdmissibleT_paper_iff p (frobeniusTransport p)
      (cyclotomicCoordinate_adjoin_eq p hε) h K.fixingSubgroup ρE).2 hBasis)

end ZInQ.Manuscript.BergerComparison
