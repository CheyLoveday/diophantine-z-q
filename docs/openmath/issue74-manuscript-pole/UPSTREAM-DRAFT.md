# Draft for inspection only — issue #82

Proposed title: Align the kernel headline with manuscript pole completeness

Deicyde/diophantine-z-q issue #74 chooses the manuscript's pole polynomial
`x(x−ℓ)(x+3ℓ)` and takes its pole completeness (Theorem 5.2) explicitly.
The planned headline is `SixContactMin → PoleCompleteness → FrozenTarget`;
Route K used a different polynomial and is being retired from that fork's
active headline. The frozen conclusion and numerical bounds stay unchanged.

The contribution restores the polynomial and templates, reuses the existing
manuscript valuation obstruction, and composes the existing H and progression
proofs with PC. PC remains the manuscript's unrefereed claim. The restricted
converse is not proved by this transition.

Which headline should upstream's `ZInQKernel/Contract.lean` pin? Once the
fork change is accepted with complete build/export evidence, a separate
upstream PR can update that contract and its `KERNEL_CONTRACT.json` hashes.
Those contract files are not changed by this contribution.

Link: https://github.com/Deicyde/diophantine-z-q/issues/74

Publication status: NOT_POSTED. Record the response in fork issue #4 only
after authorized upstream coordination. This file does not claim agreement.
