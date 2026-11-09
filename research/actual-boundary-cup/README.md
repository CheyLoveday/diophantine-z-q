# Actual boundary–cup source interface

This packet derives the connecting-map adjunction from the actual cone product,
its explicit representative correction, and the one compact-support trace.
The [proof and limits](DERIVATION.md) distinguish ordinary source mathematics,
new local Lean lemmas, finite cochain tests, and the remaining arithmetic inputs.

- [Application contract](APPLICATION.md): exact source premises and identities.
- [Source identities](SOURCES.json).
- New formal source: `lean/Research/DerivativeSwitch/ActualBoundaryCup.lean`.
- [Exact cochain checks](evidence/cochain-checks.json):256 torus-model trials,
  each with nonzero cochain correction, and three rejected weaker interfaces.
- [Native Lean receipt](evidence/native-reviewed/RESULT.json): seven new lemma roots.

Reproduce from the repository root:

```sh
python -B research/actual-boundary-cup/check_cochains.py
python -B research/actual-boundary-cup/verify_native.py /tmp/actual-boundary-cup-new-run
```

The torus is an independent nontrivial cochain model, not a computation of the
actual arithmetic Selmer complexes. Native Lean4.35 compiles the seven local
Leibniz/trace consequences; it does not formalize global Poitou–Tate duality.
No paranoid, external-checker, full arithmetic-switch, or whole-paper acceptance
is asserted. The frozen39 sources and cloud packet are unchanged.
