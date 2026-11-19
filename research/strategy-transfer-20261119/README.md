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

The Python finite oracle passed all 64 combinations in the initiating work session. Exact pinned Lean compilation and checker replay are **NOT_RUN** in that session; the Lean source is an uncompiled research candidate until tested with the receiving project's pinned toolchain.

The required next mathematical bridge is an **actual DZQ source** `S` together with both maps from that same source to the paired Selmer/trace/determinant data. This small theorem does not supply that arithmetic witness and does not close the restricted converse.

A separate, already-source-reviewed kernel-reduction transfer adds two wrapper-rewrite lines in `ZInQKernel/.../Brauer/MaximalUnramified.lean` on `gemini/fix-max-unramified-replay`. Its synthetic two-module Lean 4.35 test passed six checkers; the 309-module consumer replay remains parked after a different `LocalTraceTwo` compilation resource failure. The patched main arithmetic source is not altered by this pilot.
