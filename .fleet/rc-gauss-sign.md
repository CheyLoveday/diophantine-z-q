# rc-gauss-sign

Implementation and report SHA: 7d279e489093a1b25865eff15e57fa8f5c7fb390.
The final SHA is the commit adding this handoff; read it with
`git log -1 --format=%H -- .fleet/rc-gauss-sign.md`.

`oddGauss_one` proves Gauss's sign at every odd prime in the
manuscript's negative finite normalization. The value is 1 for primes
congruent to 1 modulo four and −i for primes congruent to 3. The proof compares the
degree-(p−1)/2 coefficients of two integral polynomials after
translation by one and reduction modulo p. The inherited square
calculation reduces the comparison to a sign; the congruence excludes
the opposite sign. The proof is on-the-spot (c).

`gaussGamma_eq_finiteGamma` identifies the actual oscillatory indices
and the explicit eighth-root family. `gaussGamma_productFormula`
proves both clauses on all nondegenerate rational diagonal lists.
`gaussGamma_rectangular_products` gives the two rectangular
product-one identities with their common real index. This discharges
the scalar Weil citation at tex 9000–9004.

All four files under `ZInQKernel/Contrib/OneProof/RC/GaussSign/`
pass sequential `lake env lean`. All 23 theorem audits use only
`propext`, `Classical.choice`, and `Quot.sound`. No print was added.
No manuscript error was identified within scope.

The common metaplectic lifts and actions, the old-level realization,
and the fixed-pool character identification remain outside this
scalar step. Exact inputs and the manuscript check are in
`docs/research/rc-gauss-sign.md`.
