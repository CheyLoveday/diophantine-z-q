# Orthogonal comparison research packet

The explicit Selmer-cone comparison preserves the common global component.
Its actual homotopy inverse therefore preserves derivative local H1, with no
extra functional-normalization scalar. The canonical strict-H2 reduction then
identifies the actual boundary matrices and pulled-back functional rows in the
generic rank-one case. See [DERIVATION.md](DERIVATION.md) for the proofs,
source premises, field/ring guards and remaining obligations.

The new Lean helper is [OrthogonalComparison.lean](../../lean/Research/DerivativeSwitch/OrthogonalComparison.lean).
It proves the degreewise cone chain-map identity and preservation on Mathlib's
actual homological complexes. Continuous Galois Selmer complexes, PD/cup/trace,
retained arithmetic models, and integral determinant lines are not defined in
this helper. Their source applications remain human arguments. The frozen
39-target packet and manuscript are unchanged.

Run the exact finite-ring checks with:

```sh
python -B research/orthogonal-comparison/check_comparison.py
```

The retained [result](evidence/comparison-checks.json) records 6400 cone model
cases, 4680 two-term homotopy congruence cases, 2043 detected wrong-sign cases,
and rejection of an arbitrary rescaling without homotopy and inversion of a
nilpotent parameter. These are algebraic model checks, not concrete arithmetic
instances. Native Lean validation is recorded by the combined integration
packet; no new paranoid/cloud/external-checker result is asserted here.

Status: new source-interface lemmas and source-bound proof sketch, awaiting
non-author review of these final bytes. The full arithmetic determinant
comparison remains open as detailed in DERIVATION.md.
