# Sun / Elliot / E364: integrated review and formal checks

## What is integrated

The supplied archive and the longer `Review outcome.txt` are preserved in
`source/`. The archive is diagnostic evidence, not a Lean proof. Its original
receipts are left unchanged. New mathematics and checks live in
`lean/SunElliotE364/`; this packet does not modify the manuscript, frozen Lean
inputs, audit-history register, evidence branches, or PRs.

Read the consolidated report at `results/sun-elliot-e364-review.md` after the
fresh verifier has been run. The report, not this README, records the actual
execution outcome. The shared research thesis, evidence boundaries and Version
comparison conventions are recorded separately in [FRAMING.md](FRAMING.md).

## Formal coverage

The modules are deliberately scoped to load-bearing exact interfaces:

- **Model transport** (`Models.lean`): the norm-one unit, parameter and generator
  transport, and the transported curve equation in the fixed real embedding of
  `Q(√2)`.
- **E364** (`E364.lean`): the marked point, tangent doubling formulas,
  square-middle bridge, reduced rational ordinates, exact denominator base
  `B₂ = 2s`, and the formal parameter `z = -x/y`. At odd support primes of a
  squarefree parameter, the theorem proves both
  `2*v_p(z)+1 = v_p(N(N²-1))` and `v_p(z) = (k-1)/2`; it separately proves
  `v₂(z) = 1 + v₂(s)`.
- **Common-strict algebra** (`Core.lean`): the division-free determinant
  comparison, opposite-sign adapter, guarded ratio with its nonzero hypotheses,
  an abstract countercontrol, reciprocal-guard term arithmetic, scalar-tree
  coefficients, strict height thresholds and one-place product-height loss.
- **Powerfulness and denominator defect** (`PowerfulBridge.lean`): the three
  factors are powerful exactly at `D ∣ s`, at `denominatorDefect D s = 1`, and
  at `2D ∣ 2s`, under the retained pairwise-coprime hypotheses. The separate
  product formula for primes with exponent one remains outside this module.
- **Characterwise versus universal descent** (`GroupRing.lean`,
  `Q2Descent.lean`): character values `3` or `1`, all with vanishing 2-adic
  valuation; the exact augmentation relation; arbitrary coefficientwise `Z₂`
  clearing with either zero augmentation or `b-1 ≤ v₂(aug(f))`; and
  nonintegrality for `b ≥ 2`. A rational integer-coefficient specialization also
  proves the exact divisibility `2^(b-1) ∣ aug(f)`.

`Q2IntegralCoefficients` uses `‖x‖ ≤ 1` in `ℚ_[2]`, the defining condition for
membership in `ℤ_[2]`. Thus the main clearing result is not limited to scalar
clearers or integer-coefficient elements. Continuous group cohomology and the
actual Selmer family are not constructed here.

## Stress-test outcome and corrections

The long review correctly restores the later fork's *source-relative*
opposite-sign computation. That computation does not identify the actual
retained Selmer objects, discharge every localization or prove universal
integral descent for the source construction. The same-place detector summary
was also checked against Sun's actual Lemma 3.1: every factor has nonpositive
valuation, so the claimed product bound survives. The source's maximum/trace
formulation is sharper, but the summary is not a counterexample.

During formalization, an auxiliary simplification of `-x/y` initially omitted
`N²+1`. The attached depth claim itself was not at fault: the corrected Lean
formula retains the factor and proves it is a unit at the support primes used
in both valuation formulas. No counterexample to Sun, Elliot or E364 was found.

## Explicit non-deliverables

This packet does **not** prove the Diophantine theorem, restricted converse,
Erdős 364, Sun's weighted polynomial-counting theorem, the large-prime tail,
the complete finite symbolic compiler atlas, the universal separating-element
bound, the defect's explicit product-of-valuation-one-primes formula, or the
ordered Kummer profile. Those remain outside this formalization. Full CRT order data and
actual simultaneous prime production are not supplied. Likewise, the attached
E364 identities do not supply a source-uniform global growth contradiction.

There is no claim of external-kernel replay, multi-checker acceptance,
human/self-independent review, source-theorem identification of the actual
arithmetic Selmer objects, or formalization of continuous Galois cohomology.

## Next global targets and owners

Owners below are **proposed workstream owners**, not assignments, independent
review or promises of delivery. Declaration names are target specifications,
not existing files. “Blocked” means the source-level prerequisite remains.

| Unformalized claim | Next concrete Lean target | Proposed owner |
|---|---|---|
| General separator bound and complete finite compiler atlas | `finiteChartAtlas_complete`: enumerate every zero/degree/pivot/guard branch and exhibit a finite separator list with `Injective (project b)` for some listed `b`; then prove rational-tuple recovery. | Compiler workstream; next agent |
| Full same-place local detector | [Completed `G=1` proof stack](targets/same-place-detector/SAME_PLACE_PROOF.md): `detectorFactor_valuation`, `failedEverywhere_product_bound`, and `samePlaceDetector` are proved with only foundational axioms. Next: the genuine number-field adapter and finite `G>1` disjunction. | Local-arithmetic workstream; next agent owns source instantiation and generalization |
| CRT compatibility, analytic counting and actual reduction-order/prime production | First `jointCRT_witness`; then `weightedCount_lowerBound` and `largePrimeTail_bound`; only then `primePatternInput_exists` supplying every order, gcd and avoidance hypothesis. CRT alone does not close this row. | Analytic-number-theory workstream; source plus independent specialist |
| Powerfulness, denominator defect product and ordered Kummer marking | [Checked](lean/SunElliotE364/PowerfulBridge.lean): `powerful_terms_iff_twoD_dvd_two_s` and the unit-defect equivalence are proved. Remaining: `defect_eq_prod_valuation_one` and `markedKummerProfile_eq`; retain `P_N` alongside `2P_N`. | E364 workstream; next agent owns the two remaining targets |
| Uniform marked-source/global E364 contradiction | Define `MarkedSource` and prove `markedSource_globalExclusion` from a joint local obstruction plus a source-uniform height/growth bound, or a complete alternative exclusion. | E364/global workstream; user selects route |
| Actual Selmer/duality and determinant identification | `actualBoundaryTuple_valid`: construct the retained global/local cup/trace tuple, original determinant coordinates, all localizations and prove `global_pairing` from the genuine Poitou–Tate diagram. | Arithmetic-interface workstream; source identification required |
| Universal integral descent with fixed clearing budget | `universalClearingBudget_exists`: use unaveraged cochains and common `f,d` to produce the source bound before character evaluation, through every required localization. | Descent workstream; source specialist required |
| Restricted converse and main Diophantine theorem | Compose `restrictedConverse` and the final theorem only after the preceding source and descent gates; do not substitute these intermediate controls. | Integration owner; **blocked** by the two preceding rows |

## Reproduce

From the repository root:

```sh
python3 -B research/sun-elliot-e364-review/verify.py \
  --output .scratch/sun-elliot-e364-review-check-NEW
```

Replace `NEW` with an unused run id; the output directory must be new. The
runner checks source hashes, executes
normal and optimized Python replays, compares their exact outputs with the
attached receipts, compiles every Lean module afresh with lean 4.35.0 and
`-t0 -j1 -Ddebug.skipKernelTC=false`, audits the public declarations' transitive
axioms, scans for proof holes and unsafe shortcuts, and writes `RESULT.json`.
Ordinary accepted axioms are `propext`, `Quot.sound` and `Classical.choice`.
