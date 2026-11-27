# Equation (3.4) at the rough companions

Implementation and report SHA: `a20f471218dab97887dbb1dc62186d85924fa400`.

The construction gives `GenusOddInstance W` from the named inputs and
proves `Gz34CompAt W 0` and `Gz34Target W`. The rough clause needs no
final-`k` input. The genus selector reuses the conductor-one construction.
At a companion of a prepared `h`, the ring-class selector constructs
the primitive form of discriminant `k' |h|²` and proves the norm
character primitive at conductor `|h|`. Both selectors cover the full
prepared domains without assuming rank one. The curve adapters supply
the coefficient-matching form, the lattice, and the level-prime support;
the existing `StageSupport` provides the prepared-filter conditions.

All seven Lean modules passed `lake env lean` sequentially. All 33
theorem audits list only `propext`, `Classical.choice`, and `Quot.sound`.
No print was added.

The remaining arithmetic inputs are the algebraic parametrization
values over the two class fields, the non-CM lattice and the period
scale, the central normalization, and the named nonzero rationality
`hElkikMD`. For a fixed `W`, the two index identifications and the
normalization identification are explicit. The full target also takes
the existing final-companion fields. The base interface still combines
the old support with the primes of final `k`; the rough theorem does
not use that final choice. The field audit, hypothesis owners and
manuscript checks are in `docs/research/rc-gz34-instance.md`.
