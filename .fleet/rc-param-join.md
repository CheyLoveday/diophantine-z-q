# Fixed-scale modular curve join

`ParamJoin.algebraicParametrizationAtScale` instantiates the actual curve on
`X0Branch.model (newformLevel (Ecurve ℓ))`. The prepared-value family and
`StageKummer.MissingParamValues` take the existing setup, the rational
representative of its fixed scale, and `CMFieldOfDefinition` on that model.
The rough (3.4) assembly supplies both `halgG` and `halgR`; the companion
uses its own order of conductor `|h|` and discriminant `k * |h|²`. The two
index fields must still read from the corresponding selectors. All existing
arithmetic and normalization inputs to (3.4) are listed in the report.

The current scale data do not supply the rational representative of the
particular `κ` (ELLIOT input, tex 1785–1787 and 1825–1828). CM descent remains
with the field-of-definition lane. The analytic limits agree with the scaled
cusp symbols; the remaining Elkik–MD step identifies the images of the
actual based cusp classes under `α q_f` with these limits in the period
quotient. The inherited Milne citation scope issue at tex 1784/1788 remains:
the cited pair does not give the normalized newform or the Hecke identity.

All four files compile serially with `lake env lean -j1 -DautoImplicit=false`.
All eight axiom checks report only `propext`, `Classical.choice`, and
`Quot.sound`. No new prints or assumed structures.

Report: `docs/research/rc-param-join.md`. Results: `scratch/rc-param-join/log.md`.

Final implementation and report SHA: `db3b7b0cf6190aeb7cb8147cc902ce379c6e1fdd`.
The handoff commit SHA is returned by
`git log -1 --format=%H -- .fleet/rc-param-join.md`; a commit cannot contain
its own SHA.
