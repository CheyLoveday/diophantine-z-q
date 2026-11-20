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

## Invariant-basis transport (VERIFIED)

- The import builds for `BergerReroute.BergerReroute` and the
  `#discharges` matcher succeeded with `lake --old --no-cache build`,
  reusing local artifacts checked against identical sources. The
  compiler wrapper serialized compiler invocations. No Lean jobs
  overlapped. Direct checks use `lake env lean`.
- `BergerComparison/Transport.lean` compiled with `lake env lean`.
  An equivariant algebra map between stable rings sends a fixed basis
  to a fixed basis by scalar extension. The map need not act on
  `B_dR`, be injective, or induce an automorphism on the fixed scalars.
- The existing crystalline-to-maximal inclusion supplies one direction.
  For the reverse direction, the remaining `FrobeniusTransport p`
  takes only a prime and cyclotomic generator, and asks for one
  equivariant algebra map between the two specified embedded semistable
  rings. There is no representation or extension quantified in it.
  With the logarithm estimate of `bmax_adjoin_eq_bst`, the reduction
  proves `BergerPaperStComparison p ell`. It also transports an
  existential finite-extension witness to the basis conclusion of
  the existing draft.

## Residue denominator (VERIFIED)

- `BergerComparison/ResidueLog.lean` compiled with `lake env lean`.
- Mathlib already has p-adic completeness of the Witt ring over the
  perfect tilt. For `p ∣ x^♯ − 1`, Fontaine surjectivity gives a
  denominator lift `1+pa`; its Witt logarithm is the p-adic sum given
  by `pLog_spec`. The quotient is `1+ξb`, with kernel-adic logarithm.
  Both contributions to `residueLog` lie in `Amax`.
- The fixed-lift addition formula and the bounded logarithm correction
  are proved. `coordinateFromUnit_adjoin_eq` identifies the ring for
  the candidate built from a small powered unit. The paper's actual
  cyclotomic unit normalization and branch compatibility (including
  change of lift) have not been proved.

## Frobenius on the finite expressions (VERIFIED)

- `BergerComparison/FrobeniusGenerator.lean` compiled with
  `lake env lean`.
- In the Witt ring, `p ∣ φ(ξ) + (-ξ)^p`. The divided-power monomial
  with coefficient `(p−1)!` at index `p` realizes `ξ^p/p` in
  `AcrisOf`. Thus the generator image `φ(ξ)/p` is crystalline.
- The same range estimate is proved for the evaluation of every
  finite polynomial with Witt Frobenius applied to the coefficients.
  This is before extending to restricted series and proving descent
  through equality of their evaluations. The actual equivariant
  semistable map has not been constructed.
