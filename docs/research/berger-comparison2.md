# Berger comparison: embedded semistable rings

**Lean proves the comparison over the original finite extension.** The
normalized cyclotomic logarithm generates the same maximal semistable
ring as `log[p̃]`. Witt Frobenius extends to an algebra map from that
actual maximal image to the actual Fontaine image, and commutes with
Galois and with the induced Frobenius actions. This closes
`FrobeniusTransport` and supplies `BergerPaperStComparison` with no
literature assumption. The same calculation also proves
`FontainePolynomialEmbedding`.

The representation implication still uses Berger's monodromy theorem:
a de Rham representation admits an invariant basis over the paper's
ring for some finite extension. From that inline input,
`bergerSurveyF_of_cyclotomic_basis` yields the existing draft
`BergerThm06Print`, then `bergerSurveyF_of_thm06Print` gives the
existing row. Neither transfer enlarges the finite extension. The draft
remains unchanged and no new published-form statement is registered.

## Known issues

- **Journal locator UNVERIFIED.** The manuscript cites Inventiones
  Mathematicae 148 (2002), 219–284, DOI 10.1007/s002220100202. The
  earlier source audit distinguishes Théorème 0.6 / 5.19 in arXiv v3
  from 0.7 / Corollaire 5.22 in a later author copy. See
  `docs/research/locators.md` and `docs/research/pb-p1.md`, §4.
  Those readings do not verify the publisher's version or pagination.
- The earlier reading writes an untilt in the denominator of the
  logarithm. The untilt gives a residue and does not give a
  distinguished element of `B_dR^+`. The new proof uses
  `[x]=(1+pa)(1+ξb)` and proves that the sum of the p-adic logarithm
  of the first factor and the kernel-adic logarithm of the second is
  independent of the lift. It identifies the cyclotomic coordinate
  for the multiplicative reading of the branch, with `log(p)=0`,
  the local formula just given, and the value
  `log_dR([p̃]/p)` at `p̃`. No journal wording or literal embedding
  of the residue field in `B_dR^+` is asserted.
- The previously recorded survey typos in the log exponent and in
  the Frobenius of the semistable variable are unrelated to the
  manuscript implication. The formal formulas use the power series
  with degree `n` and Frobenius `X ↦ pX`. No new error in the
  manuscript was found.

## Proof and scope

The source ring for the integral map is a quotient of restricted
Witt series by `ξ-pX`. On polynomials the map applies Witt Frobenius
to coefficients and sends `X` to `φ(ξ)/p`. The earlier crystalline
generator estimate and the complete ring of restricted divided-power
series extend that prescription to all integral maximal periods.
The relation `ξ-pX` maps to zero. Polynomial approximation and
separation give Galois equivariance. Comparing finite terms also
gives `φ(log[ε])=p log[ε]` for every untilt-one Teichmüller factor.
This handles both the inverted period `t` and the Galois shifts
of the semistable variable. Inverting `p*t` gives the map on the
embedded coefficient rings.

For descent after adjoining the semistable variable, the logarithm
has no linear relation over the fraction field of `B_max`. To see
the integral step, write a putative relation as
`p^r a log[p̃] = b` with `a,b ∈ A_max`. For the coefficient of
degree `i` of a restricted lift of `a`, take a sufficiently large
`k>r` and truncate at degree `N=p^k+i<2p^k`. The only nonzero
residue of the scaled log `p^k log(1-X)` in this range is
`-X^(p^k)`. Evaluation of the scaled relation vanishes modulo
`ξ^(N+1)`. Clearing the powers of p in that finite evaluation
and reducing modulo p shows that the leading coefficient is a
multiple of ξ modulo p. Thus the coefficient of degree `i` of
the lift of `a` lies in `(p,ξ)`. The ξ correction needs only
finitely many terms, as the original coefficients tend to zero
p-adically. The relation `ξ=pX` now gives `p ∣ a` in the
actual image. Iterate with `r+1`; separation gives `a=0`.
Clearing a maximal denominator and using the existing Galois
minimal-polynomial argument yields transcendence. This route uses
the tree's proof of `B_dR^G = ℚ_p`, with no new invariant-field
hypothesis. The semistable Frobenius respects all polynomial
relations, and transcendence also implies the weaker injectivity
of the Fontaine polynomial presentation.

The normalized-branch characterization takes the ordinary local
logarithm laws and values. These only identify one element of `B_dR`
and say nothing about semistable bases. The inline hypothesis of the
final transfer theorem is the monodromy implication over the paper
ring from tex 739–741, before any change of rings. Its de Rham
premise is the existence of an invariant de Rham basis, a predicate
over the actual de Rham field which says nothing about semistability.
Neither the published implication nor an abstract period ring is
used in the proof of the comparison.

## New Lean results (VERIFIED)

The following modules are under
`ZInQKernel/Contrib/OneProof/BergerComparison/`.
The named lemmas are public; private lemmas are covered by the axiom
audit.

| Module | New results |
| --- | --- |
| `RestrictedEvaluation.lean` | `restrictedEval_polynomial`: evaluation of restricted Witt series into a complete ring agrees with polynomial evaluation. |
| `MaximalEvaluation.lean` | `maximalEval_relation`, `pow_p_dvd_of_dvd_xi_mul`, `maximalEval_zero_iff`: multiplication by ξ is regular modulo p-powers; the kernel of maximal evaluation is the linear relation. |
| `DividedPowerCompletion.lean` | `pDvd_iff_coeff`, `exists_restricted_limit`, `restricted_isAdicComplete`, `dividedPowerRestricted_isAdicComplete`: division and completion are controlled coefficient by coefficient in the two restricted rings. |
| `CoefficientFrobenius.lean` | `mem_crystallineIntegral` identifies the image with the original integral crystalline set. `polynomial_mem_restricted`, `frobBeforeDescent_polynomial`, `maxToImage_surjective`, and `integralFrobenius_polynomial` compute Witt Frobenius before and after descent. |
| `MaximalSeparation.lean` | `amax_eq_zero_of_pDvd`, `exists_polynomial_mod_pPow`, `restricted_to_amax_ext`: separation in the maximal image and evaluation by finite approximation. |
| `IntegralEquivariance.lean` | `maximalEval_polynomial`, `integralFrobenius_galois`: ordinary polynomial evaluation, then commutation with Galois on all integral coefficients. |
| `FrobeniusTeichLog.lean` | `integralFrobenius_zp`, `integralFrobenius_logTeich`: integral Frobenius fixes p-adic integers and scales the untilt-one logarithms by p. |
| `LocalizedFrobenius.lean` | `localizedFrobenius_integral`, `localizedFrobenius_logTeich`, `coefficientFrobenius_galois` extend the computations to the actual localized coefficient rings. `exists_maximal_denominator` and `clear_maximal_log_relation` reduce relations to the integral image. |
| `LogDenominators.lean` | `exists_scaledInverse`, `negativeLogSeries_eval`, `scaledNegativeLog_coeff`, `scaledNegativeLog_mod_p`: evaluate the normalized log at ξ/p, scale its truncation and isolate its nonzero residue. |
| `LogarithmRelations.lean` | `eq_zero_of_integral_log_relation`: an integral linear relation of the stated shape forces its leading coefficient to vanish. |
| `LogTranscendence.lean` | `logPTilde_notInFrac`, `logPTilde_transcendental`, `fontainePolynomialEmbedding`: no linear relation over the maximal fraction field, and polynomial injectivity over both rings. |
| `CyclotomicUnit.lean` | `exists_cyclotomic_correction`, `exists_small_power_of_correction`, `exists_cyclotomic_small_unit`, `cyclotomicCoordinate_adjoin_eq`: cyclotomic estimate including p=2, near-one unit power, and equality of the maximal adjunctions. |
| `LogOverlap.lean` | `xiPow_dvd_of_mod_every_pPow`, `wittLogTerm_one`, `pLogTerm_eq_mul_pow`, `pLog_agrees_logPlus_on_overlap`: closure of the ξ-powers and agreement of the two logarithms on their overlap. |
| `WittLogAdd.lean` | `pLog_add`: multiplicative law for the Witt logarithm on units congruent to one modulo p. |
| `LogLiftIndependence.lean` | `residueLog_independent_of_lift`, `logSmallTeich_eq_residueLog`, `logSmallTeich_mul`: independence of the lift and multiplicativity of the near-one Teichmüller logarithm. |
| `CyclotomicBranch.lean` | `logSmallTeich_eq_logTeich`, `cyclotomicCoordinate_eq_of_normalized`: agreement on untilt one, and identification of the coordinate by the normalized branch laws. |
| `SemistableDescent.lean` | `evaluateMaximalSt_val`, `evaluateMaximalSt_surjective`, `evaluateMaximalSt_injective`: the polynomial presentation of the maximal image. `semistableFrobenius_coeff`, `semistableFrobenius_log`, `semistableFrobenius_galois`, `semistableFrobenius_intertwines`, `frobeniusTransport`: well-defined coefficient and log substitution, with both equivariances on the actual images. |
| `DeRhamBasis.lean` | `deRhamBasis_of_isDeRhamU`: the dimension premise supplies the invariant basis used by the paper, by the usual shortest-relation argument over the de Rham field. |
| `SemistableComparison.lean` | `bergerPaperStComparison`: unconditional comparison over the same extension. |
| `SurveyTransfer.lean` | `bergerSurveyF_of_cyclotomic_basis`: the chain from the paper basis hypothesis through the existing draft to the survey row. |

All 20 new modules compiled with Lean 4.35.0 using `lake env lean`,
one Lean process at a time. The check in
`scratch/berger-comparison2/Axioms.lean` prints the axioms of all 58
public theorem and instance declarations. Its allowlist also covers
private and generated theorems and definitions: 422 declarations in
total, including 324 theorems, use only `propext`, `Classical.choice`
and `Quot.sound`.

The focused `#discharges` in `scratch/berger-comparison2/Discharges.lean`
(removed when this work landed on main: it named `OpenResearchLeaves72`,
which main no longer has)
matches the type of the existing headline row without importing the
headline module. It finds the new transfer, with only the inline
paper-ring basis implication still assumed. The raw results are
`axioms-output.txt` and `discharges-output.txt` in that scratch directory.

## Remaining input and count

The only remaining input to the rerouted row is the monodromy
implication itself: for each prime and each continuous finite
coefficient model with an invariant de Rham basis, it supplies a
finite extension and an invariant basis over the normalized maximal
semistable ring. This is one theorem, not a further ring comparison.
The direct journal statement and locator still need checking. No
comparison with an abstract completed divided-power envelope is
required for this route.

Actual registry delta: **0 GLUE / 0 LEAF**. The existing row is
reduced to one candidate refereed LEAF with no open ring GLUE.
If the journal reading is verified and the integrator classifies
and folds the result, the reroute replaces one GLUE by one LEAF.

## Manuscript check

| Lines in `diophantine_zq.tex` | Step used | Verdict |
| --- | --- | --- |
| 719–731 | Use a finite coefficient model and the underlying representation. | OK |
| 735–738 | Supply the de Rham premise from the comparison and descent lemma. | OK |
| 739–741 | Convert the paper-ring potential semistability to the project's Fontaine-ring basis/dimension form. | gap filled |
| 755–758 | Use the potential semistability conclusion at the coefficient prime 5, without changing the witness extension. | OK |
| 10940–10951 | Identify the continuous finite coefficient representation and the de Rham conclusion of the stated premise. | OK |
| 10954–10972 | Obtain the de Rham comparison for the proper smooth Tate representation; this is upstream of the period-ring comparison. | OK |
| 10973–10978 | Pass to the underlying finite coefficient representation and its summand. | OK |
| 10980–10994 | Descend de Rhamness over the finite extension; no semistable descent is used here. | OK |
| 10996–11006 | Use the Tate weight convention and distinguish the de Rham premise from its weights. | OK |
| 11037–11040 | Identify the journal theorem and the paper's precise period-ring and admissibility conventions. | unverified (journal copy not checked) |
