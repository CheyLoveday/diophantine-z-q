# rc-intertwine-2

Implementation and report SHA: `69b86bc47cdaf015b34af112eb1956092731fc05`.
This note is the following handoff commit; its SHA can be read with
`git log -1 --format=%H -- .fleet/rc-intertwine-2.md`.

The finite adèlic Haar measure `nuF` is normalized by the actual local
Haar volumes on the compact open rectangular cylinder. Its cylinder mass is
`ENNReal.ofReal (finiteVolume a)`, and it agrees with the measure in
`adelic_pair_comparison`. On each elementary class indicator, the
inverse upper operator and the normalized Weyl integral factor into the
local operators, including the Fourier zero off the polar dual. The
real Weil index is `zetaEight ^ 3` for both positive ternary forms.

All five new files under `ZInQKernel/Contrib/OneProof/RC/Intertwine2/`
pass `lake env lean`. All 41 theorem audits list only `propext`,
`Classical.choice`, and `Quot.sound`. No new prints or changes to
existing Lean modules.

The conditional theorem `pair_of_tensor_generators` gives both
`IntertwinesGenerators` instances with the same inverse lifts and scalar.
The missing inputs are the actual finite Weil index family, the realized
common lifts evaluated on elementary local tensors
(`GeneratorTensorAction`), and `WeilIndexProductFormula`
(tex 9000–9004, Weil II.30, Proposition 5, independently UNVERIFIED).
The stage weights, classwise depth, spherical and class identifications,
and character remain with their existing owners. The report
`docs/research/rc-intertwine-2.md` records the exact conditions and
manuscript check. No manuscript error was identified in scope.
