# Source coupling: Rule 110 / E364 → DZQ Lean pilot

A source-level theorem experiment, not a completed arithmetic or manuscript proof.

- `CoupledSource.lean` expresses two observations from one shared source witness.
- `coupled_implies_marginal` proves the valid implication.
- `bool_not_coupled` refutes the tempting converse; independent local constraints need not share a source witness.
- `check_coupled.py` exhaustively checks all 4 Boolean source maps for each observation and all 4 output pairs (64 finite configurations).

## Execute

```sh
python3 -B research/strategy-transfer-20261119/check_coupled.py
cd lean
lake env lean ../research/strategy-transfer-20261119/CoupledSource.lean
```

The independent Boolean oracle passed **64/64** in GitHub Actions. The exact source passed **strict Lean 4.35.0 compilation**, with `-DautoImplicit=false -DwarningAsError=true`; all four `#print axioms` reports were **axiom-free**. [CI receipt](https://github.com/CheyLoveday/diophantine-z-q/actions/runs/44615668875), source SHA-256 `496901ab3b44a2cc558ce0d140532116b11e4bdd47859ce3f8f2f7de7988de2d`. Separate independent native checker replay is **NOT_RUN**; the actual DZQ arithmetic adapter remains **OPEN**.

The required next mathematical bridge is an **actual DZQ source** `S` together with both maps from that same source to the paired Selmer/trace/determinant data. This small theorem does not supply that arithmetic witness and does not close the restricted converse.

A separate, already-source-reviewed kernel-reduction transfer adds two wrapper-rewrite lines in `ZInQKernel/.../Brauer/MaximalUnramified.lean` on `gemini/fix-max-unramified-replay`. Its synthetic two-module Lean 4.35 test passed six checkers; the 309-module consumer replay remains parked after a different `LocalTraceTwo` compilation resource failure. The patched main arithmetic source is not altered by this pilot.
