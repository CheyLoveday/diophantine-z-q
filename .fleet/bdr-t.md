# De Rham period reading

**VERIFIED (Lean):** `DeRhamPrint.BdRT.tt_eq_logTeich` identifies the two
constructions of Fontaine's `t = log[ε]` for every `RootSystem p`.
`fontaineT_reading` records the nonzero uniformizer and the cyclotomic
law in both period rings, identifies the localization at `t` with the
localization at `xi`, and gives the equivariant equivalence with the
kernel's `B_dR`. The concrete action match is
`DeRhamPrint.BdRT.bdREquivAwayT_intertwines`.

`lake env lean ZInQKernel/Contrib/OneProof/BdRT.lean` passed. All ten axiom
checks returned exactly `propext`, `Classical.choice`, and `Quot.sound`.
The initial Lake build launched parallel compiler jobs; it was stopped.
The target and its missing prerequisites compiled serially with
`lake env lean -o`, and all 79 base declaration checks passed. The full
Lake target build was not completed.

Count effect: none. The proposed replacement for the `OPEN.md` bullet is in
`docs/research/bdr-t.md`, for the lead to apply. It uses Brinon–Conrad,
replaces `deRhamH1AbVarT` with `deRhamVpAbVarDirect`, and records the matching
Galois action. Fontaine's *Astérisque* citation is unread and outside the
manuscript bibliography; Berger 2002 §1.2 remains UNVERIFIED as a locator.

Known stale pointers: the consequence cited at L10995 in
`ZInQKernel/Contrib/OneProof/DeRhamScholzeT.lean:234` is at L10997, and the
`FontaineTwistT` docstring predates its proof. The manuscript check found the
Tate signs consistent. The gap filled at L10984–L10992 is the dictionary
for the period ring and action used to form the invariants.
