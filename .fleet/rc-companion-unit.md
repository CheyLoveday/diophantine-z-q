# Final companion from the separate even source

The provider fixes the negative Appendix E source and its initial sieve
before choosing `k` at the attained minimum. `Selection.leaf_and_oldUnit`
proves every conjunct of `CompanionLeaf W` and
`CompanionOldUnit A.old W.kfin` for the same choice. Build `W.S` as the
union of the level primes, the pre-companion exclusions, and the prime
factors of `k`. For the quadratic field of `k`,
`Selection.fresh_ramification` gives a ramified prime outside both old
supports.

The reference at tex 2595–2599 is implicit: Appendix E requires a nonzero
reference in the initial sieve. The provider uses the existing BFH clause
(ii) with the enlarged splitting set for the reference. Neither
`HoffsteinLuo` nor `BFHTwistSign` is needed by this provider. The genus
partner and rough companion routes retain their existing dependencies.

The integrator supplies the actual old support covering the fixed label
fields, the torsion ramification support, and the original normalization
and App E inputs. Use the same normalization and selected `k` for the
transported source. Wiring and odd minimum preservation remain separate.
The inherited shell support slip at tex 10393–10404 is documented in
[rc-ksplit-seed](../docs/research/rc-ksplit-seed.md).

`Provider.lean` compiled after all six imports were built serially.
All ten theorem audits list exactly `propext`, `Classical.choice`, and
`Quot.sound`. See the [report](../docs/research/rc-companion-unit.md) for
the interfaces, owners, and manuscript checks.

Final proof and report SHA: `2cbddc131791ce557eb9a91652f36d27b24d4369`.
