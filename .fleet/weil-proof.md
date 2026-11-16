# weil-proof (field `weilPairingMumford`): interim status

**Main result (VERIFIED, standard axioms).** Mumford's §20 display (pic-dict's leaf `MumfordWeilPairingAC`: the
formula `ē_n(x, M) = t_x^*ψ ∘ ψ⁻¹` is independent of `ψ`, a constant `n`-th root of unity, bilinear) is proved,
three conjuncts outright and the fourth from one formal glue statement `WeilProof.PullbackCompMonoidal`
(Mathlib's `pullbackComp` commutes with the vendored tensorators of `Scheme.Modules.pullback`).
`WeilProof.weilPairingMumford_proof` gives the field from 5 Mumford leaves + that glue + the open field
`phiAmpleIsogeny` (`ZInQKernel/Contrib/OneProof/WeilFormula.lean`, builds; `#discharges` lists it).

**Not done.** The field is not removed: nondegeneracy (§20) and `e^L(x,x) = 1` (§23) stay leaves (no Cartier
duality / cube theorem / theta groups in the tree). Fold dry run with honest flags: 34/11 -> 37/13 (rise); do not
fold now.

Report: `docs/research/weil-proof.md`.
