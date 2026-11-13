# Same-place detector — completed `G = 1` proof

**Proposed owner:** Local-arithmetic workstream; next agent.

`Draft.lean` now contains a complete algebraic proof of all three `G = 1`
declarations, with no `sorryAx`. It is **not included** in
`lean/SunElliotE364/`, the completed fresh-build module set or its accepted
axiom result; it is reported separately to keep the proof-to-source boundary
explicit. Remaining work is the genuine number-field adapter and the finite
`G > 1` disjunction, not another hole in this algebraic proof.

## Scope of this slice

The proof states the single-group (`G = 1`) case of Sun's Lemma 3.1. It does
not yet include the full finite-family sum of inverse products. The genuine
final adapter must instantiate the places, normalized valuations, number-field
trace and one-sided consequence of Sun's actual `Φ₀`, rather than supplying
arbitrary functions with the same names.

The first adapter used `a : WithTop ℤ` in `trace_lower_bound` and was shown
inconsistent at `x=0,a=⊤`. The compiled regression is
`targets/stress/DetectorKitLegacy.lean`. The current adapter uses finite `a : ℤ`.

The ordered checklist is:

1. **Done:** `detectorFactor_valuation` is proved, including zero test
   expressions and the odd-parity/no-cancellation argument. Its exact premise
   `Odd (padicValRat p R)` is the source's safeguard against the countermodel
   `R=-1,k=0,D=1`; nonzero `R` alone would not suffice.
2. **Done:** `failedEverywhere_product_bound` is proved, including the
   necessary `k_i ≥ 1` margin and explicit negative/positive scalar cases. See
   `PRODUCT_BOUND_PROOF.md`.
3. **Done:** convert the trace lower bound and pole rule into
   `samePlaceDetector`. See `SAME_PLACE_PROOF.md`.
4. **Next:** instantiate the genuine unramified diagram and one-sided pole rule,
   then generalize to the finite-family disjunction.

Scalar compatibility is also zero-safe:
`if q=0 then ⊤ else ↑padicValRat p q`, since `AddValuation 0 = ⊤` whereas
`padicValRat p 0 = 0`. Both countermodels are retained, and `p_prime` is
explicit rather than synthesized ad hoc.

The current compile has three axiom reports, all excluding `sorryAx`. See
`DRAFT_RESULT.json` and `DRAFT.log` for the actual output. No source manuscript,
frozen input, registered theorem or PR is modified.
