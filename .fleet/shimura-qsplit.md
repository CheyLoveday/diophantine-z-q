# Shimura quotient split: scoped stop

The proposed `ShimuraQuotientByC` is false as a formulation of the
construction. `XiAction` and `PrintedClauses` only use positive indices;
`printRing` includes zero. Changing the dummy value to `ξ 0 = 1` preserves a
genuine printed triple but adds `(1, 0)` to the ring because `a₀(f) = 0`.
The killing condition would force its quotient map to vanish, contradicting
surjectivity onto the positive-dimensional `A`. The old combined statement
also quantifies over this dummy value.

The manuscript cites Theorem 1 at L770–773 for the quotient construction;
the identification `ker ν = C` is in the proof on p. 526. A faithful
split using the current ring needs the normalization `ξ 0 = 0`. The
closed Hecke bridge provides it; a revised consumer could then use the
construction directly to recover the fixed target. The requested
reconstruction through the old combined statement still has the same
obstruction.

The stop rule triggered before any Lean changes. No new module was built and
there are no axiom or discharge results for the split. See the
[verdict](shimura-qsplit-verdict.md), [report](../docs/research/shimura-qsplit.md),
and [results log](../scratch/shimura-qsplit/log.md).

The report commit is `9fc8ebd69dc6b048719c789687a63dfded6626b4`.
The final SHA is the commit that adds this file; resolve it with
`git log -1 --format=%H -- .fleet/shimura-qsplit.md`.
