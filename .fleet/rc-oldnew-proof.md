# Even inventory old/new independence

`oldNewIndependenceWeightTwo_proved : OldNewIndependenceWeightTwo`
discharges the old/new leaf using vendored good-prime Hecke equivariance
and strong multiplicity one, the diamond characters, and a least-degree
Fourier coefficient argument. The placed inventory and joint rules-and-seed
entry point now have specializations that supply this proof.

The inherited manuscript error at tex 8162–8167 is a missing base factor
in the simplified expansion. The consumers use the exact expression at
8168–8182. The earlier Li attribution was to the strong multiplicity-one
theorem. The old/new independence locators are UNVERIFIED and the proof
supplies the input for which they were requested.

Both Lean files compile. The audit of 29 declarations found only
`propext`, `Classical.choice`, and `Quot.sound`. The two remaining
mathematical inputs are the intrinsic `SourceAttachment` for each
normalized newform and the local cuspidal data with the Whittaker
comparison on the resulting row.

See `docs/research/rc-oldnew-proof.md` for the theorem statements,
remaining hypotheses, manuscript check, and audit results.
