# Appendix F: genus selections away from the witness

**Scoped stop.** The prepared filter gives the imaginary quadratic field,
its exact discriminant, a primitive conductor-one Heegner form with `A=N`,
and the norm genus character. `extendSelG` keeps every old entry and fills
each empty admissible entry away from the witness once `PreparedParamValue`
is supplied there. `exists_selected_of_admissible` gives the exact selection
equation for `StageMap.lamOf_admissible` at every admissible pair, without a
simple-zero condition. The witness datum and its embedding stay fixed.

**Verified.** `RC/StageSelector/Forms.lean`, `Character.lean`, and
`Selector.lean` compile separately with `lake env lean -j1`. All 20 theorem
audits and the two construction audits list only `propext`,
`Classical.choice`, and `Quot.sound`. No new print was added.

**Remaining.** For the chosen form, realize its analytic parametrization
value as the image of a point over the conductor-one ring class field. This
needs the modular curve's canonical model, CM descent and compatibility of
the rational parametrization with `phiAn` at the chosen scale. The geometric
identification with the theta comparison remains with that lane. No
manuscript or cited-source error was found in the steps used here.

Report: `docs/research/rc-stage-selector.md`. Log: `scratch/rc-stage-selector/log.md`.

Final result SHA (Lean, report, and log): `1d6e9848e0a1d373710e4bc14ac15fb4338db7f6`.
This fleet note is committed separately as the last commit.
