# Sun / Elliot / E364: load-bearing interface review

Review date: 2026-11-13.

## Scope

This packet contains an original exact-arithmetic diagnostic script, its outputs,
and an audit note. It is NOT a formal proof of either Diophantine paper or of
Erdos 364. No Lean build, external checker, or simultaneous-prime search was run.
The current sources were read through web and GitHub connectors; source PDFs
are linked in `sources.json`, not redistributed or claimed to have been locally
hashed.

## Reproduce

Python 3.10 or newer; standard library only.

```sh
python replay.py --output results.json
python -O replay.py --output results_optimized.json
```

Both commands were executed in this review and produced byte-identical JSON.
Checks use explicit exceptions rather than Python `assert` statements.

## Contents

- `replay.py`: exact arithmetic controls, using `fractions.Fraction`.
- `results.json`, `results_optimized.json`: actually executed results.
- `replay.stdout.txt`, `replay_optimized.stdout.txt`: captured stdout.
- `REVIEW.md`: independent mathematical derivations and acceptance boundaries.
- `sources.json`: source versions, exact locators and available repository pins.
- `MANIFEST.json`: hashes of files in this packet (excluding itself).

## Results and limits

All implemented diagnostics passed:

1. Five exact identities for the unit change between Sun's and Elliot's curve models.
2. A split-prime, opposite-place negative control for replacing one joint local
   witness by independently chosen witnesses.
3. 729 generated rational ordinate pairs across all four ordinate charts.
4. A nonseparating primitive-element countercontrol and its separating repair.
5. 165 reciprocal-polynomial checks and eight failed-guard checks.
6. Four determinant models showing that primitive rows and equal ranks do not
   imply valuation preservation.
7. Eight binary group-ring families (510 character evaluations), demonstrating
   scalar-unit values without uniformly integral group-ring coefficients.
8. One synthetic compatible CRT system and two incompatible controls.
9. All 10,000 even midpoints through 20,000, including 56,091 odd-prime depth
   checks, for the marked E364 congruent-curve identities.
10. Exact scalar norm-tree path weights and 50,971 sampled valuation tuples.
11. Exact rational arithmetic for the three strict height-exponent thresholds.

The CRT moduli are synthetic; they are not alleged elliptic reduction orders.
The split-prime control checks a local parity obstruction, not full acceptance
by a global pole predicate. The determinant and group-ring controls refute
weaker abstract implications, not the actual arithmetic constructions.
The E364 range is bounded; no global exclusion is inferred from it.

## Review disposition

- Compiler: the separating-element and reciprocal-guard arguments withstand the
  reviewed controls. The full symbolic branch atlas has not been generated.
- Completeness: CRT compatibility and the stated ordering of choices are coherent.
  The imported weighted prime-pattern theorem and large-prime tail have not been
  independently re-proved here. The source does explicitly address the tail.
- Determinants: the later fork already supplies a source-relative opposite-sign
  normalization and common-strict determinant bridge. Actual retained global
  objects, every localization and universal integral descent remain distinct.
- Soundness: the three exponent comparisons have strict margins under the stated
  imported bounds.
- E364: the curve, denominator and formal-depth connections are exact. The missing
  source-uniform global contradiction is not supplied merely by these identities.
