import ZInQKernel.Contrib.OneProof.LogPTranscendence

/-!
# Berger's theorem with Fontaine's period ring

This is a draft statement and a bridge to the existing dimension form. The journal locator and
the use of Fontaine's ring as a consequence of the paper's own formulation need a reading.
See `docs/research/berger-reroute.md`.
-/

noncomputable section

namespace ZInQ.Manuscript.BergerReroute

open HDec.PkgI4
open BergerBst BmaxOne FontaineSt PanBergerSplit PanDict

private abbrev xi (p : ℕ) [Fact p.Prime] := ZInQ.Contrib.G9.BdrKer.Cp.xi p

/--
Draft Fontaine-ring consequence of Berger's de Rham ⇒ potentially semistable theorem,
*Représentations p-adiques et équations différentielles*, Invent. Math. 148 (2002), 219–284.
Locator **UNVERIFIED** in the journal: the repository audit gives Théorème 0.6 in arXiv v3
and Théorème 0.7 in the later author copy. The paper's reported basis condition over
`B_max[log [π̄]]` still needs to be connected to the Fontaine-ring basis condition below.

Here `V = E^n` is viewed over `ℚ_p`. De Rham is `dim_{ℚ_p} (B_dR ⊗ V)^G = dim_{ℚ_p} V`.
The conclusion is that over some finite `K/ℚ_p`, `B_st ⊗ V` has a basis of `G_K)-fixed
vectors. We use `B_st = B_cris[log [p̃]]` as an image in Mathlib's `B_dR` (`BstFOf`).
Its coefficients are defined by the divided power series at `ξ` with coefficients tending
to zero p-adically, then inverting `p` and `t = log [ε₀]` (`AcrisOf`, `BcrisOf`).
The normalization is `log(p) = 0`: the polynomial coordinate `X` evaluates at
`log_dR([p̃]/p)` (`logPTilde`). On the polynomial ring, the Galois action extends that
on `B_cris` by `σ(X) = X + log [σ(p̃)/p̃]`. The usual operators with the negative
derivative convention extend crystalline Frobenius by `φ(X) = p X` and give
`N = -d/dX`. Only the induced Galois action enters this predicate, via the action on
`B_dR`; no Frobenius or monodromy on `B_dR` is asserted.
-/
def BergerThm06Print : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀)
    (n : ℕ) (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (ρE : GQp p →* GL (Fin n) E),
    Continuous ρE → IsDeRhamU p ρE → IsPstFBasis p h (xi p) (theta_xi' p) ρE

/-- The draft suffices for the existing row: invariant basis ⇒ dimension equality,
and the embedded ring is independent of the chosen generator of `ker θ`. -/
theorem bergerSurveyF_of_thm06Print (hB : BergerThm06Print) : BergerSurveyF := by
  intro p _ ε₀ h w hw hgen n E _ ρE hc hdr
  obtain ⟨K, hK, hBasis⟩ := hB p ε₀ h n E ρE hc hdr
  refine ⟨K, hK, ?_⟩
  rw [bstFOf_eq_xi p h hw hgen]
  exact isAdmissible_of_pstF p h K.fixingSubgroup ρE hBasis

/--
The polynomial-to-image comparison at the generator used by the draft: the map
`B_cris[X] → B_dR` taking `X` to `log_dR([p̃]/p)` has zero kernel. Its image already
is `BstFOf` by `LogPTransc.bstFOf_eq_adjoin` and
`Algebra.adjoin_singleton_eq_range_aeval`. Thus this is one injectivity condition,
independent of representations and extension fields.
-/
def FontainePolynomialEmbedding : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀),
    Function.Injective
      (Polynomial.aeval (R := BcrisOf p h (xi p) (theta_xi' p))
        (toBdR p (logPTilde p)))

/-- The existing, stronger logarithm transcendence gap over `B_max` implies the needed
injectivity over `B_cris`. -/
theorem fontainePolynomialEmbedding_of_logPTildeTranscendental
    (ht : LogPTildeTranscendental) : FontainePolynomialEmbedding :=
  fun p _ _ h => LogPTransc.transcendental_bcrisOf p ht h (theta_xi' p)

/--
The difference for the literal paper route. For `ell` equal to Berger's `log [π̄]` under
his chosen normalization in `B_dR`, the input is an invariant basis over the paper's
`B_max[ell]`; the required output is the dimension condition over Fontaine's embedded
`B_cris[log [p̃]]`, over the same finite extension. This is a ring comparison, not
the monodromy theorem. The paper's logarithm is not constructed by this definition.
-/
def BergerPaperStComparison (p : ℕ) [Fact p.Prime] (ell : BdR p) : Prop :=
  ∀ (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (n : ℕ) (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (ρE : GQp p →* GL (Fin n) E),
    Continuous ρE →
    IsAdmissibleT p (Algebra.adjoin ℚ_[p] ((Bmax p : Set (BdR p)) ∪ {ell}))
      K.fixingSubgroup ρE →
    IsAdmissible p (BstFOf p h (xi p) (theta_xi' p)) K.fixingSubgroup ρE

/-- The missing comparison precisely suffices to transport a witness of potential
semistability from the paper's ring. -/
theorem isPstF_of_paperSt {p : ℕ} [Fact p.Prime] {ell : BdR p}
    (hcmp : BergerPaperStComparison p ell)
    {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {w : Ainf p}
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w})
    {n : ℕ} {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]
    {ρE : GQp p →* GL (Fin n) E} (hc : Continuous ρE)
    (hpst : ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
      IsAdmissibleT p (Algebra.adjoin ℚ_[p] ((Bmax p : Set (BdR p)) ∪ {ell}))
        K.fixingSubgroup ρE) :
    IsPstF p h w hw ρE := by
  obtain ⟨K, hK, hBasis⟩ := hpst
  letI := hK
  refine ⟨K, hK, ?_⟩
  rw [bstFOf_eq_xi p h hw hgen]
  exact hcmp ε₀ h K n E ρE hc hBasis

end ZInQ.Manuscript.BergerReroute
