import ZInQKernel.Contrib.OneProof.BergerComparison.LocalizedFrobenius
import ZInQKernel.Contrib.OneProof.BergerComparison.LogarithmRelations
import ZInQKernel.Contrib.OneProof.LogPTranscendenceBdR
import ZInQKernel.Contrib.OneProof.BergerReroute.BergerReroute

/-! The integral coefficient calculation excludes the logarithm from
the maximal fraction field and proves both polynomial presentations. -/

noncomputable section

namespace ZInQ.Manuscript.BergerComparison

open HDec.PkgI4 BergerBst BmaxOne BergerReroute

variable (p : ℕ) [Fact p.Prime]

/-- The normalized logarithm has no nonzero linear relation over B_max. -/
theorem logPTilde_notInFrac :
    LogPTransc.NotInFrac p (Bmax p) (toBdR p (logPTilde p)) := by
  intro a b ha h
  obtain ⟨ε, hε⟩ := exists_isGenEps p
  obtain ⟨A, B, hA, hB⟩ := clear_maximal_log_relation p hε ha h
  exact hA (eq_zero_of_integral_log_relation p A B 0 (by simpa only [pow_zero, one_mul] using hB))

/-- The de Rham logarithm is transcendental over the maximal image. -/
theorem logPTilde_transcendental : LogPTildeTranscendental :=
  LogPTransc.logPTildeTranscendental_of_notInFrac logPTilde_notInFrac

/-- The same argument proves injectivity for the crystalline polynomial
presentation, independently of representation transport. -/
theorem fontainePolynomialEmbedding : FontainePolynomialEmbedding :=
  fontainePolynomialEmbedding_of_logPTildeTranscendental logPTilde_transcendental

end ZInQ.Manuscript.BergerComparison
