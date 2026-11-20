# Berger comparison: results log

## Sizing (VERIFIED in the manuscript and base Lean source)

The manuscript's input is the underlying representation of the finite
coefficient model (719–731), known to be de Rham (735–738, 10940–11006).
The comparison concerns the use of Berger at 739–741, to supply the
hypothesis of Pan at 755–758. The citation at 11037–11040 gives the
monodromy paper, without a theorem number.

Both target declarations below are in
`ZInQKernel/Contrib/OneProof/BergerReroute/BergerReroute.lean`.
Here `xi p` abbreviates the canonical `p - [p̃]` and standard tensor
and Galois notations are as in that module.

```lean
def BergerPaperStComparison (p : ℕ) [Fact p.Prime] (ell : BdR p) : Prop :=
  ∀ (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (n : ℕ) (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (ρE : GQp p →* GL (Fin n) E),
    Continuous ρE →
    IsAdmissibleT p (Algebra.adjoin ℚ_[p] ((Bmax p : Set (BdR p)) ∪ {ell}))
      K.fixingSubgroup ρE →
    IsAdmissible p (BstFOf p h (xi p) (theta_xi' p)) K.fixingSubgroup ρE

def FontainePolynomialEmbedding : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀),
    Function.Injective
      (Polynomial.aeval (R := BcrisOf p h (xi p) (theta_xi' p))
        (toBdR p (logPTilde p)))
```

| Ingredient | What exists | Missing for this task |
| --- | --- | --- |
| Fontaine's map | Mathlib's `fontaineTheta`, `fontaineThetaInvertP`; `BdrKer.Cp` proves their kernel descriptions. `BergerBst.evalB` evaluates at an argument in that kernel, in the kernel-adic completion. | An untilt gives a residue, not a distinguished lift of an arbitrary Cₚ scalar or its p-adic logarithm. |
| B_cris | `FontaineSt.AcrisOf`, `BcrisPlusOf`, `BcrisOf`: restricted divided-power series image, then invert p and t. `bstFOf_le` proves inclusion of its normalized semistable image in the tree's maximal image. | No Frobenius on this series image. Abstract completed PD envelope comparison separate. |
| B_max | `BergerBst.Amax`, `BmaxPlus`, `Bmax`: restricted series at ξ/p, then invert p and t. | No extension of Witt Frobenius to this image with values in the crystalline image. |
| Frobenius | Mathlib has Witt Frobenius; it is not a Frobenius on B_dR. | Descent through equality of restricted-series evaluations, range estimate, compatibility with t and the logarithmic Galois translations. |
| Logarithms | `BergerBst.logPlus`, `logTeich` (untilt 1), `logPTilde` (denominator p); the log sum and Galois increment are proved. `FontaineSt.bmax_adjoin_eq_bst` gives equality of maximal rings from a scalar-normalized estimate on the paper's coordinate. | Construct the normalized logarithm at the paper's tilt element and relate it to the tree's coordinate. The analytic extension in the prior arXiv reading uses a p-adic series, not simply a θ-adic series at the residue. |
| Representation transport | `FontaineSt.isAdmissibleT_mono` changes basis along an inclusion, and `BmaxOne.isAdmissible_of_T` derives the dimension form. | Basis transfer only needs an equivariant algebra map in the other direction; base change along a map should avoid identifying fixed fields or proving equality of invariant spaces. |
| Polynomial embedding | `LogPTransc.bstFOf_eq_adjoin` and the conditional proof from `LogPTildeTranscendental`. | No proof of the remaining fraction-field exclusion on this base. Not needed to transport an existing invariant basis along a map of embedded rings. |
| End-to-end | `bergerSurveyF_of_thm06Print` already gives the row from the Fontaine-ring draft alone. | The separate paper-ring witness must first produce the draft's basis form; comparison of the embedded predicates does not verify the journal citation. |

VERIFIED (prior audit as evidence, not a fresh journal reading):
`docs/research/locators.md` R11 records different theorem numbers in
arXiv v3 and the later author copy. The journal locator remains
UNVERIFIED. The prior report's description of division by the untilt
of the tilt element is a notation issue to resolve in the period ring.

VERIFIED (tools): `lake --help` and `lake build --help` show no jobs
flag on Lake 5.0.0 / Lean 4.35.0. Builds will use a compiler lock and
the load/memory gate, with downloads disabled. The pre-run gate is
`uptime` and `free -g`, load at most 150 and available memory at least
20 GB. Follow the same gate for each direct check.
