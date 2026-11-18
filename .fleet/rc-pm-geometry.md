# RC/PM geometry at the detector's place

**Result.** `PMGeometry` derives the good Hecke sum, affine Atkin–Lehner
identity, and Frobenius identities from the modular special fibre's
divisor and correspondence inputs. The actual stage place gives the
additive specialization equivalence on geometric `2^M`-torsion.
Transport of the global row supplies `PM.Evaluation`, including
`row_fixed` and `square_trivial`. Both theta constructors use this
detector. At a selected Heegner datum the same-place point comparison
gives the reference-tuple reduction congruence for `lamOf`.

**Verified.** `Geometry.lean`, `Evaluation.lean`, `Theta.lean`, and
`Heegner.lean` compiled with `lake env lean --threads=1`. All 27 axiom
audits show only `propext`, `Classical.choice` and `Quot.sound`.
An earlier queue transition briefly overlapped two Lean processes. After
it was stopped, all final checks ran sequentially under one lock. A later
shell quoting error invoked Lean without its resource precheck, printing
usage only. Both resource incidents are recorded in the report.

**Remains.** Instantiate the named supersingular comparison and good
modular model, including the specialized quotient, in the adelic outputs.
For each Heegner datum to be compared, supply the pointwise CM reduction
for its reference orientation and the corresponding stage map at the
same place. The witness-only stage map does not cover other entries.
The Jetchev–Kane citation scope at level one is recorded in the report.

Final result SHA (before this fleet note): `efb154ad405272e59566ebc48e6ccb35d44602a9`.

Report: `docs/research/rc-pm-geometry.md`.
Results: `scratch/rc-pm-geometry/log.md`.
