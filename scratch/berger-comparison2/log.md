# Berger comparison continuation: results log

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

The base commits already prove the equivariant basis argument, the
crystalline estimate for finite Frobenius expressions, and the bounded
near-one lift formula. New targets are descent and range for an entire
restricted series, localization and semistable equivariance, and the
cyclotomic normalization and coherence of the lift formula.

SPECULATIVE decomposition of the coefficient calculation: first show the
kernel of restricted evaluation at `ξ/p` is `(pX − ξ)` by recursively
dividing out the constant term of a series evaluating to zero. Separately
substitute `φ(ξ)/p` in the ring of restricted divided-power series, by
taking coefficientwise p-adic sums before evaluation. These steps address
different issues: independence of presentation, and crystalline range.

## Restricted substitution and cyclotomic unit (VERIFIED)

- Offline Lake built the three base comparison imports. The previous
  worktree had the same commit; reusing the matching Lean and C artifacts
  let Lake replay existing targets. The first invocation that lacked
  the C artifacts was interrupted before the serial replay. The compiler
  wrapper locks each compiler invocation and checks load and memory;
  direct checks use the same load/memory gate and run in sequence.
- `RestrictedEvaluation.lean` compiled with `lake env lean`, and its
  import artifact built with `lake --old --no-cache build`. Modulo each
  `p^k` the reduced coefficient series is a polynomial. Evaluation and
  passage to the compatible limit give a ring homomorphism into a
  complete target. It agrees with ordinary evaluation on polynomials.
- The cyclotomic calculation in `CyclotomicUnit.lean` compiled with
  `lake env lean`. It gives a tilt correction `u` with
  `(ε - 1)^(p - 1) = pFlat^p * u^p` and `‖u.untilt + 1‖ < 1`.
  Working at the second cyclotomic root gives the needed strict norm
  bound also for `p = 2`. A positive even power of `u` has untilt one
  modulo `p`. This check does not identify Berger's logarithm.

## Integral coefficient Frobenius (VERIFIED)

- `MaximalEvaluation.lean`: the kernel of evaluation on restricted
  series is generated by `ξ - pX` inside the restricted ring. The
  recursive division preserves restrictedness because multiplying by
  `ξ` does not create divisibility by `p^k`.
- `DividedPowerCompletion.lean`: the formal restricted divided-power
  ring is p-adically complete. A Cauchy limit is taken coefficient by
  coefficient in the Witt ring, with a uniform bound in the coefficient
  index; this preserves decay.
- `CoefficientFrobenius.lean`: substitute a divided-power series
  representative of `φ(ξ)/p` and apply Witt Frobenius to the coefficients.
  After crystalline evaluation this kills `ξ-pX`, so it gives the
  ring homomorphism `integralFrobenius : Amax p →+* crystallineIntegral p`
  on the two embedded integral images. Its value on every finite
  polynomial has the original Witt Frobenius formula.
- All three files compiled directly with `lake env lean`. The concrete
  `cyclotomicCoordinate` from the positive powered correction also
  compiled and its adjunction gives the normalized maximal ring.

## Logarithm and equivariance (VERIFIED)

- The powered-correction witness now uses the full correction
  `v = u^p` in the cyclotomic relation. The coordinate uses
  `log[v^m]/m`, so the factor of p on the correction is accounted for.
- `MaximalSeparation.lean`: the ideal generated by `ξ - pX` is
  closed in the p-adic topology of the restricted ring. Thus
  `Amax` is separated, and two maps into it agree if they agree on
  finite polynomial lifts.
- `IntegralEquivariance.lean`: Witt Frobenius commutes with the Galois
  action on every element of `Amax`, checked using the finite
  polynomial formula and separation.
- `LogOverlap.lean`: the two analytic logarithms agree on
  `1 + pξ Ainf`. The p-adic sum coming from the Witt ring has the
  same reductions modulo every power of `ξ` as the kernel-adic sum.
- `WittLogAdd.lean`: the p-adic logarithm is multiplicative in
  additive notation on `1 + p Ainf`. Modulo `p^k` use the truncation
  at `4k`; a formal log identity handles coefficients of degree below
  `4k`, and higher degrees are already divisible by `p^k`.
- `LogLiftIndependence.lean`: two lifts of the same lifted product
  differ by a ratio in `1 + pξ Ainf`. The overlap identity gives
  independence of the lift, and the product of two such factorizations
  gives the multiplication rule for `logSmallTeich`.
- All preceding files compiled with `lake env lean`.

## Localized coefficient and logarithm normalization (VERIFIED)

- `CyclotomicBranch.lean` identifies the local logarithm with the
  kernel-adic logarithm at untilt one and characterizes the cyclotomic
  coordinate for any branch with the usual multiplicative rules on
  nonzero elements and the two specified local values.
- `FrobeniusTeichLog.lean`: the integral map fixes the p-adic integers
  and carries every `log[ε]` with untilt one to `p * log[ε]`.
  Compare finite sums on each side, use the agreement of their terms
  under Witt Frobenius, and pass to the separated limit.
- `LocalizedFrobenius.lean`: `Bmax` is the localization of the
  embedded `Amax` at `p * t`; every p-adic scalar has bounded
  p-denominator. The localized map is a ℚ_p-algebra map into the
  actual `BcrisOf` and commutes with Galois. The logarithm formula
  applies to both `t` and each Galois shift. These files compiled
  directly with `lake env lean`.

## Truncated log estimate (VERIFIED)

- `LogDenominators.lean`: at any prime, for `0 < n < 2 p^k`,
  `p^k/n` is integral. Its only nonzero residue in this range is at
  `n=p^k`, where the residue is one. Thus the scaled Witt truncation
  of `log(1-X)` reduces to `-X^(p^k)`. Its finite coefficients
  agree after inverting p, and `log(1-X)` evaluated at `ξ/p` is
  `log[p̃]`.
- The maximal localization proof also gives denominators for any
  two `Bmax` coefficients. Clearing them in a relation with
  `log[p̃]` gives a relation in the integral image and preserves
  a nonzero leading coefficient.
- These two modules compiled with `lake env lean`.

## Integral fraction-field obstruction (VERIFIED)

`LogarithmRelations.lean` compiled with `lake env lean`. For
`p^r a log[p̃]=b`, fix a coefficient index `i` of a restricted lift of
`a` and truncate at `p^k+i<2p^k` for sufficiently large `k>r`.
Clear denominators in the finite evaluation and reduce modulo p.
Vanishing modulo `ξ^(p^k+i+1)` forces the top coefficient to be
divisible by ξ modulo p. The scaled log has only one surviving term,
so this makes the coefficient at `i) belong to `(p,ξ)`. The ξ
correction may be taken with finite support, since the original
series is restricted. In the actual image `ξ=pX`, so `p∣a`;
iterate with `r+1` and apply p-adic separation to conclude `a=0`.
