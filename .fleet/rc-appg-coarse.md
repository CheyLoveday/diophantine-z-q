`depths_of_prepared_stages` proves App G's (F.5), the attained minimum, and
`IntegerDepth` for each fixed budget on the full intrinsic odd filter. The
filter uses the original prepared squareclasses and the moving Legendre test.
The same fixed `D_w` is visible with valuation `9 + ω(N) + c_w` eventually;
this gives nonemptiness, while the minimum is attained by a bounded-weight
sequence. The proof installs that minimum and applies `integerDepth_of_data`.

`Intrinsic.lean` and `Prepared.lean` passed individual `lake env lean -j1`
checks. All seven axiom audits list only `propext`, `Classical.choice`, and
`Quot.sound`. No new prints were added.

The actual application still needs uniform (F.3), (3.4), and (3.5) on the
original prepared data, (O.7) with the same lifts and coefficients, the
native and torsion comparisons, and the fixed detector value (O.2) on the
selected stages. The exact owners and comparisons are in
`docs/research/rc-appg-coarse.md`. The exact sieve and stage identification
remain downstream inputs.

Known issues: an address restriction cannot supply the full-filter minimum.
Tex 10176 leaves `C_H` undefined; the existing proof uses `C_per + 2`.
Tex 2360–2361 and 10131–10132 request even seeds too broadly if read as
including sign −1 types; the companion wiring uses the prepared types
that occur at nonvanishing.

Code and report SHA: `3ddaa17b1537a7fbd2cc06a965be6fd6c96758ba`.
Final SHA (this handoff commit): `git log -1 --format=%H -- .fleet/rc-appg-coarse.md`.
