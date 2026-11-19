# Appendix F: stage maps on the genus support

**Result.** `actualForStages.ev` evaluates every conductor-one genus datum on
the moving Legendre support. The stage prime is inert in that datum's quadratic
field. It is principal there, so its restriction from the selected absolute
place to the ring class field has quadratic residue. The map reduces there
and applies the same finite Kummer map and row as at the witness.

`actualForStages_at_witness` supplies `hev` by equality of additive maps at the
selected witness. `actualEvaluationsOn_spec` and
`witnessValuation_actualForStages` give the finite specialization and (O.2).
At each admissible pair with a selected datum, `lamOf_admissible` reads the
integer lift of the evaluation on the scaled genus point, with no rank
restriction. The off-support extension is never used by this comparison.

**Verified.** `RC/StageMap/Actual.lean` and `RC/StageMap/Consumers.lean`
compile separately with `lake env lean -j1`. All twelve theorem audits use only
`propext`, `Classical.choice`, and `Quot.sound`. No new print.

**Remaining.** To compare at all admissible nonwitness pairs, the assembly
needs `(selG D).isSome` there; the current selector guarantees it only at
prepared simple zeros. The pointwise geometric identification with the
supersingular side and (O.7) remain comparison inputs.

Report: `docs/research/rc-stage-map.md`. Log: `scratch/rc-stage-map/log.md`.

Final result SHA (Lean, report, and log): `6937a702709b89bc3bab09488a3779ebd8a02233`.
This fleet note is committed separately as the last commit.
