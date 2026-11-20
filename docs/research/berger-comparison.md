# Berger comparison

**Scoped stop.** Lean now transports a Galois-fixed basis between the two
embedded semistable rings over the **same** subgroup, given an equivariant
algebra map in the Frobenius direction. The comparison therefore needs
neither a fixed-field computation nor injectivity of that map. The integral
crystalline estimate for Frobenius on `ξ/p` is proved. A logarithm using a
Witt lift of the residue denominator is constructed for near-one units,
with its correction in `B_max^+`. The remaining GLUE is to extend Frobenius
to the embedded semistable ring and identify Berger's particular logarithm
with the normalized coordinate. `BergerPaperStComparison` and
`FontainePolynomialEmbedding` are still open as unconditional statements.

## Known issues

- **Literal denominator.** In the prior reading of Berger's monodromy paper,
  the denominator in the logarithm formula is an untilt in the residue field
  of `B_dR^+`. It does not give a lift of that denominator to `B_dR^+`.
  The construction here uses a Witt lift and two different completions;
  matching the selected lift computation to the paper's multiplicative
  logarithm remains a proof obligation. This issue does not identify an
  error in the manuscript's monodromy implication.
- **Locator discrepancy.** The manuscript cites the theorem by name.
  The prior audit in `docs/research/locators.md`, R11, reads Théorème 0.6
  and Théorème 5.19 in arXiv v3, and Théorème 0.7 and Corollaire 5.22 in
  the later author copy. The journal locator remains **UNVERIFIED**.
  The source of the logarithm is the prior arXiv reading in
  `docs/research/pb-p1.md` §§2 and 4, including the proof of Prop. 2.23;
  the corresponding journal locator is **UNVERIFIED**.
- **Separate later survey.** The prior audit reports exponent `i-1` for
  `i` in its log series and `φ(X)=X^p` for `pX`, and leaves a topology
  implicit in its crystalline series. This contribution uses neither
  misprint and does not use the survey as a supplier.
- No new mathematical error was found in the manuscript or the monodromy
  paper. No primary journal text was reread.

## Checked Lean work

The module names below are relative to
`ZInQKernel/Contrib/OneProof/BergerComparison/`.
Declarations are under `ZInQ.Manuscript.BergerComparison`.

| Module | Theorem | Result |
| --- | --- | --- |
| `Transport.lean` | `isAdmissibleT_of_equivariant` | Base change along an equivariant algebra homomorphism gives an invariant basis over the target, with the same subgroup. |
| | `isAdmissibleT_fontaine_iff` | Basis equivalence for the normalized images, given the map from the maximal ring to the Fontaine ring. The reverse algebra map is the existing inclusion. |
| | `isAdmissibleT_paper_iff` | The same equivalence for the paper-ring predicate, given its identification with the normalized maximal ring. |
| | `bergerPaperStComparison_of_frobenius` | The exact draft comparison from the map and the scalar-normalized logarithm estimate. Converts the transported basis to the required dimension form. |
| | `isPstFBasis_of_paper` | Transports an existential paper-ring witness to the basis conclusion used by the Fontaine-ring draft. Retains the given finite field. |
| `ResidueLog.lean` | `exists_pLog`, `pLog_spec`, `pLog_zero` | The signed terms `(−1)^(n+1) p^n a^n/n` have a sum in the Witt ring; the first `2k` terms determine it modulo `p^k`. The sum at zero is zero. |
| | `exists_residue_factors` | If `p ∣ x^♯ − 1` in `𝓞_ℂₚ`, lift `(x^♯ − 1)/p` along Fontaine's surjection to `a`. The Witt unit `1+pa` has the same residue as `[x]`, and `[x]=(1+pa)(1+ξb)` for some Witt vector `b`. |
| | `logXi_mem_amax` | The kernel-adic logarithm of `1+ξb` is a restricted series in `ξ/p` with coefficients `(−1)^(n+1) (p^n/n)b^n`. |
| | `residueLog_mem_amax`, `logSmallTeich_mem_amax` | The sum `residueLog` of the two logarithms lies in `A_max`; `logSmallTeich` uses a chosen factorization to construct such a sum in `B_dR^+`. |
| | `residueLog_mul_kernelUnit` | For the same residue lift, multiplying the quotient by `1+ξc` adds its kernel-adic logarithm. |
| | `coordinateFromUnit_adjoin_eq` | Adding the scaled small-unit logarithm to the scaled `log[p̃]` gives the same embedded maximal semistable ring. This theorem does not identify the coordinate with the paper's. |
| `FrobeniusGenerator.lean` | `frobenius_xi_add_neg_pow_dvd` | In the Witt ring, `p ∣ φ(ξ)+(-ξ)^p`. |
| | `frobenius_xi_div_p_mem_acris` | `φ(ξ)/p = a - (-ξ)^p/p` belongs to the integral crystalline series image. The second term uses the single divided power `ξ^p/p = (p−1)! ξ^p/p!`. |
| | `eval₂_wittFrobenius_mem_acris` | Evaluation after Frobenius stays in the crystalline series image for every finite polynomial in the maximal generator. |

The private lemmas are `inclT_periodAct` and `fontaineRing_le` for
the tensor action and inclusion; `dvd_pLogTerm`, `intoPlus_mem_amax`,
`xiMul_mem` and `logPlus_congr` for the logarithm; and
`const_mem_acris`, `psEval_polynomial` and `pthDivision_mem_acris`
for finite Frobenius evaluation. The axiom check includes them.

## Remaining work and size

1. **Equivariant map (GLUE; large construction).** `FrobeniusTransport p` is
   one existential `ℚ_p`-algebra homomorphism
   `Bst p →ₐ[ℚ_[p]] FontaineRing p h`, commuting with the two specified
   Galois actions, for each cyclotomic generator. This is narrower than
   a Frobenius theory with injectivity, monodromy and fixed-field
   calculations. It is data about the two actual rings, with no
   quantification over representations or finite extensions and no
   admissibility conclusion. It would supply the ring comparison for manuscript 739–741. The generator estimate handles finite expressions;
   extending to restricted series requires control of their p-adic
   sums and descent through equality of the series images. One must then
   treat `t⁻¹` and check the logarithmic Galois translations at the
   embedded semistable level. A map on a formal polynomial ring must
   preserve the relations of the embedded ring, or use a separate
   injectivity proof. Estimate: several hundred Lean lines beyond the
   generator calculation, with the embedded logarithm relations a
   separate potentially large part. No Frobenius on all of `B_dR` is
   required or proposed.
2. **Paper logarithm (GLUE; two local checks).** At the level used by
   `Transport.lean` the missing input is one scalar-normalized membership
   in `B_max^+`, or just the resulting ring equality, for the actual
   `ell` of the paper. This is a statement about a single element with
   no representation data. For the explicit coordinate construction,
   find `v` with `π̄^(p−1) = p̃^p v` and a positive
   power `x = v^m` in the proven near-one domain; account for the
   cyclotomic valuation, including `p = 2`. Then prove compatibility
   of the near-one formula with the chosen logarithm branch
   (including changing the lift, or by an independent characterization
   of that branch), so the multiplicative normalization can be used.
   The fixed-lift addition formula does not suffice for this.
   Estimate: one local cyclotomic valuation calculation and one analytic
   coherence proof; roughly a few hundred Lean lines, unmeasured.
3. **Separate abstract comparisons.** `FontainePolynomialEmbedding`
   is one injectivity condition per prime and cyclotomic generator.
   The existing stronger route is the exclusion of `log[p̃]` from
   `Frac(Bmax p)`. This did not follow from the generator or logarithm
   work. The comparison of the completed divided power envelope
   with the embedded crystalline series image is also separate.
   Neither is a premise of the representation transport given an
   actual map of the embedded rings. Both matter when interpreting
   an abstract ring presentation as the Lean image.
4. **Primary reading (GLUE until verified).** Check the journal locator,
   actual ring and action, and de Rham premise. The conditional chain
   uses the row's dimension form of de Rhamness. If the print uses a
   basis, the usual independence argument over the de Rham period field
   with fixed field `ℚ_p` remains a separate dictionary step.

The finite-stage Frobenius calculation is VERIFIED. The implementation
route for its extension and the proof-size estimates are SPECULATIVE.
The repository's arXiv reading is evidence for choosing the
normalization, not a substitute for the required journal reading.

## Chain and count

The conditional check in `scratch/berger-comparison/Reduction.lean` starts
with an invariant basis over `B_max[ell]` on a finite extension `K`.
`isPstFBasis_of_paper` uses the ring equality and the equivariant map to
pass that basis to the Fontaine image over `K`. This is the conclusion
of `BergerThm06Print` on the same coefficient model and the given
Fontaine cyclotomic generator. The existing `bergerSurveyF_of_thm06Print` then gives the
exact row: basis implies dimension, and the embedded ring is independent
of the generator of `ker θ`. The two smaller period-ring obligations are
still premises of that chain from the paper, so no new `#discharges`
claim is made. `BergerThm06Print` remains a draft.

**Count delta: 0 GLUE, 0 LEAF.** The one Berger row remains GLUE; the
work discharges the representation argument inside that row. If the two
period-ring obligations and the source reading close, the intended
replacement is one fewer GLUE and one more LEAF, subject to review.
Nothing is folded.

## Manuscript check

All lines are from `diophantine_zq.tex` at the base.

| Lines | Step | Verdict |
| --- | --- | --- |
| 719–731 | Form the finite coefficient model and extract the two-dimensional summand. | OK — the comparison takes its underlying `ℚ_p`-model without changing coefficients. |
| 735–738 | Supply de Rhamness and the two Tate weights. | OK — de Rhamness is the premise of the draft; no weight input is needed for the transport. |
| 739–741 | Apply Berger to obtain potential semistability. | unverified — basis transport is proved conditional on the two ring inputs; the journal reading is pending. |
| 755–758 | Apply Pan at five with the Tate convention. | OK — the transport targets the existing semistability premise; Pan's journal statement was not reaudited. |
| 10940–10951 | State de Rhamness for the finite coefficient summand. | OK — supplies the upstream premise at `K = ℚ_p`. |
| 10954–10972 | Compare smooth proper cohomology and identify the Tate module by duality. | OK — upstream of the period-ring comparison; used only through de Rhamness. |
| 10973–10978 | Use closure under duals, subquotients and finite coefficient sums. | OK — independent of semistable period rings. |
| 10980–10994 | Descend the de Rham dimension formula. | OK — the descent concerns `B_dR`; transport here works with the given finite witness. |
| 10996–11006 | Separate the computation of weights from the de Rham assertion. | OK — the conditional chain uses the assertion itself. |
| 11037–11040 | Cite Berger's journal paper. | OK — the manuscript provides the title and DOI without assigning a theorem number. |

## Verification

VERIFIED: all three contribution modules and both scratch checks compiled
with `lake env lean` without importing `ZInQKernel.OneProof.Main`.
The explicit `#print axioms` checks and the audit of all 48 theorem
declarations (including private and generated lemmas) found only
`propext`, `Classical.choice` and `Quot.sound`. The command details are in
`scratch/berger-comparison/log.md`, and the axiom output is in
`scratch/berger-comparison/axioms-output.txt`.
