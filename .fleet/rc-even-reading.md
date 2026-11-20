# Transported even reading handoff

The Branch 2 variant `AddressDensityLeafGenuineEven` supplies `FreshPrime`,
`EvenReading` and `EvenFilter` to the existing address density leaf. The
reading is the depth-zero symbol of the Appendix E phase on the twist by
`k`, with sign +1, reference index 1, and the original central values
transported by `h ↦ h*k`. At a prime-set unit, (F.1) holds with equality
and constant `v₂(W.Lstar k)`. The adapter fits the existing Branch 2
consumer directly.

All four files in `ZInQKernel/Contrib/OneProof/RC/EvenReading/` passed
serial `lake env lean -j1` without warnings. The 15 entries in the axiom
audit each list exactly `propext`, `Classical.choice` and `Quot.sound`.
The statements, owners, print inputs and manuscript checks are in
[the report](../docs/research/rc-even-reading.md).

The companion provider must retain avoidance of the old fixed label and
torsion ramification support, and the address provider must place the
primes of `m₁` in that support. The remaining obligations are the odd
density models, odd and prepared filters, and the even density models
and `KSplitSeed` for the **same** genuine reading. The source uses the
existing Appendix E hypotheses; the Waldspurger nonvanishing Prop still
includes the manuscript's classical construction. The companion leaf
does not certify that `k` was a unit of the old source, which the
manuscript uses for the whole-filter transported lower bound.

Proof and report commit: `3a26663b4ac6ce2c0acb9f4db9ffe0e0d4f30d5a`
