# Sun / Elliot / E364 integration and stress test

## Outcome

The attachment is integrated as a local research and formalization packet at
`research/sun-elliot-e364-review/`. Its original review artifacts are preserved;
the manuscript, existing/frozen Lean sources, audit-history register, branches
and PRs were not changed. No commit or remote write was made.

**Executed result: PASS for the scoped local checks below.** This is not external
verification of Sun's paper, Elliot's manuscript, the arithmetic switch,
Erdős 364 or any global completeness claim. It is a fresh native Lean build and
axiom audit of the explicitly listed interfaces, plus exact Python replay.
No independent or multi-checker acceptance is claimed.

## Actual execution

Command:

```sh
python3 -B research/sun-elliot-e364-review/verify.py   --output .scratch/sun-elliot-e364-review-check-10
```

Observed output:

- `status: PASS`, `lean_modules: 7`, `axiom_reports: 28`;
- normal and optimized replay outputs matched each other and the attached
  receipts byte-for-byte;
- all seven Lean modules compiled in fresh output locations with Lean 4.35.0,
  `-t0 -j1 -Ddebug.skipKernelTC=false`;
- all 28 selected declarations used only `propext`,
  `Quot.sound` and/or `Classical.choice`, with no `sorryAx`, `sorry`, `admit`,
  custom axiom, `unsafe` or `native_decide` in the delivered sources;
- eight original source-manifest entries passed their size/SHA-256 checks.

The replay underlying these compiler checks covers 10,000 even midpoints through
20,000, 56,091 odd-prime depth checks, 50,971 scalar valuation tuples and the
other attached exact controls. The completed local receipt is
`research/sun-elliot-e364-review/RESULT.json`; compiler/axiom logs are under
`research/sun-elliot-e364-review/evidence/`.

The builds emitted nonfatal style/linter warnings (58 total:
Core 17, E364 32, GroupRing 5,
Q2Descent 4); they did not emit compilation errors. This
packet is therefore **not described as linter-clean**. The audit log contains
only expected foundational axioms for the selected public declarations.

## What the Lean statements establish

| Area | Exact checked content |
|---|---|
| Quadratic-field model | Unit norm one, parameter and generator transport, and the transported curve equation in the chosen real embedding. |
| E364 marked point | Point on `y²=x³-D²x` from the source decomposition; full tangent-doubling formulas and square-middle bridge. |
| Denominators | Both doubled ordinates are reduced under the stated even-midpoint hypotheses; their square/cube denominator base is exactly `2s`. |
| Powerfulness and unit defect | `powerful_terms_iff_D_dvd_s`, `powerful_terms_iff_defect_eq_one`, and `powerful_terms_iff_twoD_dvd_two_s`: exact valuation identities for all actual factors under pairwise coprimality. This does not yet prove the product-of-valuation-one-primes defect formula or Kummer profile. |
| Formal depth | `2*v_p(z)+1=v_p(N(N²-1))` and `v_p(z)=(k-1)/2` at odd support primes of squarefree `D`; separately `v₂(z)=1+v₂(s)`. |
| Determinant interface | Division-free cross-evaluation identity, opposite-sign adapter, ratio under the retained nonzero guards and an abstract adverse model. These are algebraic identities, not arithmetic Selmer instantiation. |
| Compiler/height fragments | One reciprocal-guard term for `1≤j≤d`, the seven exact norm-tree coefficients, strict height thresholds and the local product-height loss identity. |
| Rational group algebra | Character values `3` or `1`, all with zero 2-adic valuation, and exact integer-augmentation divisibility `2^(b-1) ∣ aug(f)`. |
| Full `Q₂` descent control | For arbitrary `f` with coefficientwise `‖·‖≤1`, integral `fu_b` implies zero augmentation or `b-1 ≤ v₂(aug(f))`; `u_b` is nonintegral for `b≥2`. |

`Q2IntegralCoefficients` is precisely a coefficientwise norm-one hypothesis in
`Q₂`, not merely an integer-coefficient or scalar-clearer specialization. The
zero-augmentation alternative is necessary because `Padic.valuation 0 = 0`; no
fictitious `+∞` convention was introduced. `b=0` is retained in the general
valuation theorem, where its conclusion is vacuous; nonintegrality is stated
from `b≥2`.

These results refute the weaker scalar-characterwise-to-universal-integrality
inference. They do **not** refute or construct Sun's unaveraged-cochain, common
`f,d` universal descent argument.

## Stress-test dispositions

### 1. The determinant correction is historical/source-relative, not an open sign identity

The baseline `33483f751e6dcd3f91fb303969838aca33ad0458` was inspected directly,
not merely its attached verdict. Its `research/arithmetic-boundary-cup/`
`DERIVATION.md` and `README.md` give `cF=-κu`, `cS=κu`, and the retained
boundary/cup opposite-sign calculation relative to V13 arithmetic and duality
inputs. Thus the older "untouched scalar sign" description should not be used.

Disposition per the repository audit protocol: **prior justification found;
conditional algebra relative to explicit inputs**. Canonical manuscript
incorporation is **pending**, and this session did not alter it. The same
baseline's integration specification retains as separate obligations the
actual global diagrams, retained objects, localized inverses, all required
coefficient localizations, universal group-ring descent, restricted converse
and main theorem. The new formulas must not be read as discharging those gates.

### 2. The same-place detector summary survives the attempted product objection

Sun 28 unknowns, Lemma 4.2, delegates the main local implication to the other
paper's Lemma 3.1. The latter writes each factor valuation as `min(0,b)` and
`W`'s valuation as a sum of such nonpositive terms. A failed factor therefore
cannot be offset by another factor. The attached summary's product-before-trace
argument survives. The actual source's maximum-over-places formulation is
sharper for trace/integrality, but this is not an error in the attachment.
The exact split-prime example remains a local parity diagnostic, not a global
pole witness.

### 3. The E364 connection is exact but deliberately short of a global contradiction

The formal statements above preserve the marked point and `2P_N`; they do not
justify dropping the ordered Kummer data into an unmarked doubled-point input.
The missing transfer remains an actual joint marked-source obstruction or a
source-qualified global bound. Uniform height constants, a fixed cyclic
carrier, rapid growth comparisons and a prime population for the varying `D`
are not derived from these formulas.

### 4. Auxiliary formula correction during formalization

An early draft of my auxiliary `-x/y` simplification omitted `N²+1`. The retained
Lean theorem correctly uses

```
-(2s(N²+1)) / ((N²-2N-1)(N²+2N-1)).
```

The attached depth assertion itself did not fail: the added factor is shown to
be a unit at the relevant odd support primes and at two. This correction is
about my intermediate formula, not a counterexample to the review or papers.

## Shared framing and follow-up ownership

The supplied research judgment and our acceptance boundaries are preserved in
`research/sun-elliot-e364-review/FRAMING.md`. Its central thesis is the
compression of Sun's construction onto shared elliptic, local and compiler
structure, without treating that compression as replacing Glazer's arithmetic
foundations. The E364 direction is the marked-source/joint-local/global-obstruction
programme, explicitly **not** an E364 theorem.

The packet `README.md` now maps every unformalized global claim to a concrete
next Lean target and a proposed workstream owner. Owner means proposed research
responsibility, not an independent assignment or acceptance. Actual
restricted-converse and final-theorem composition are marked blocked on the
actual Selmer/duality identification and universal clearing budget.

The first same-place draft now lives at
`research/sun-elliot-e364-review/targets/same-place-detector/Draft.lean`, with
**proposed owner: Local-arithmetic workstream; next agent**. All three
obligations, including `samePlaceDetector`, are now proved with only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` remains. The proofs
require odd scalar valuation and `k_i ≥ 1`: the unguarded factor statement
fails at `R=-1,k=0,D=1` (zero factor on the left, zero `min` on the right).
The single-group `G=1` algebraic target is closed. What remains is instantiation
of the genuine number-field trace/place data and the finite-family `G > 1`
disjunction, not another algebraic gap in the completed module.
The scalar compatibility is separately zero-safe: zero maps to `⊤`, while
`padicValRat p 0 = 0`. The draft covers the single-group `G=1` slice and is not
part of the seven audited proof modules or their acceptance boundary. The
adversarial review subsequently showed that the legacy `trace_lower_bound`,
with `a : WithTop ℤ`, is inconsistent at `x=0` and `a=⊤` for every nonempty
place set. `targets/stress/DetectorKitLegacy.lean` proves that inconsistency
without new axioms. The current adapter uses finite `a : ℤ` bounds instead.

## Adversarial follow-through

The [expanded stress-test report](sun-elliot-e364-stress-test.md) contains the
full interface countermodel and repair, new powerfulness proof, bounded scan,
held-out height interpolations and cross-repository limits.

## Remaining unproved work and unrun checks

- No full finite symbolic compiler atlas or general separator-bound proof was
  formalized. The replayed chart cases and exact guard term do not replace them.
- No Kummer-profile, explicit defect-product formula, full finite-family (`G>1`)
  same-place detector, genuine unramified adapter, or simultaneous-prime theorem
  was formalized here. The single-group `G=1` algebraic detector is proved,
  and powerfulness/unit defect have since been proved separately. Existing
  Python diagnostics for the other targets remain replay, not Lean declarations.
- Weighted polynomial counting, finite-cutoff mass lower bounds and the complete
  large-prime tail were source-compared, not independently re-derived.
- No actual Selmer/Poitou–Tate objects, continuous Galois cohomology, original
  determinant-coordinate identifications or universal arithmetic clearing
  construction are supplied. The restricted converse and main Diophantine
  theorem remain open obligations.
- No global Erdős 364 exclusion or source-uniform growth contradiction was
  found. No simultaneous-prime search was run.
- There was no external-kernel replay, paranoid/multi-checker replay, or
  independent human/agent acceptance. Local native Lean checking and exact
  source arithmetic are the only executed formal checks claimed.

Sources consulted directly include [Sun's 28-unknown v1](https://arxiv.org/html/2611.14605v1),
[the comparison v3](https://arxiv.org/html/2610.20691v3), and baseline
`33483f75` files in the local Git object store. The attachment remains the
authority for which E364 statements were reviewed; no independent read of the
private E364 and SPROUT repositories is claimed.
