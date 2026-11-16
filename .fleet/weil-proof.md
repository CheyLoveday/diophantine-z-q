# weil-proof (field `weilPairingMumford`): interim status

**Main result (VERIFIED, standard axioms).** pic-dict's §20 leaf `MumfordWeilPairingAC` (Mumford's `ē_n` by
the formula `t_x^*ψ ∘ ψ⁻¹` is well defined, `μ_n`-valued, bilinear) is a theorem
(`WeilProof.mumfordWeilPairingAC_proof`), via `WeilProof.pullbackCompMonoidal_proof` (pull-back of sheaves of
modules is a monoidal pseudofunctor for the vendored structure). `WeilProof.weilPairingMumford_proof` gives the
field from 5 Mumford leaves (§6 Cor. 4, §8 (iv), §8 Thm 1, §20 nondegeneracy, §23) and the open field
`phiAmpleIsogeny`. File `ZInQKernel/Contrib/OneProof/WeilFormula.lean` (builds; `#discharges` lists it).

**Not done.** The field is not removed: §20 nondegeneracy (and so far §23) stay leaves. Dry run: honest flags
(the two `ē_n` leaves pending reading) 34/11 -> 37/12; with pic-dict's "unread" flags 34/11 -> 39/10.

Report: `docs/research/weil-proof.md`.
