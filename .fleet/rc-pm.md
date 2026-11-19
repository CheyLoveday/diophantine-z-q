# Appendix F: the supersingular stage function

**Result.** On the Eichler order's ideal class set, the finite detector gives
`P_M(z) = λ_M(L • π_ℓ₀(z))` in `ZMod (2 ^ M)`. The good-prime line sum has
eigenvalue `a_p`; Atkin–Lehner has sign `w_{p^e}) after `L` kills the cusp;
and the right division uniformizer has sign `+1` by Frobenius invariance of
the finite row. The last two also have the lift congruences needed for the
orientation comparison, including the norm-character factor when supplied.

`AppF.ThetaStage` uses this residue function in `𝒪/2^M𝒪`, with neighbours
and weighted adjointness from the supplied Eichler line index.
`Visibility.ThetaStage` uses any integral lift of the same function.
Relifting preserves every Visibility coefficient modulo `2^M𝒪`.
The pointwise Heegner lift lemma uses the same map as `StageKummer` when
the two underlying specialized points agree. The detector adapter uses
`Stages.finiteRow` and the existing reduced Kummer construction.

**Verified.** `Stage.lean`, `Theta.lean`, and `DetectorRow.lean` each
compiled with `lake env lean --threads=1`. All 24 axiom audits use only
`propext`, `Classical.choice`, and `Quot.sound`. No new printed-form leaf.
No new manuscript error found. The Jetchev–Kane and Voight locators are
UNVERIFIED.

**Remains.** Supply the actual supersingular/adelic correspondence and
parametrization specialization in the `Geometry` record, and the torsion
and Heegner specialization identities at the chosen place. The line
indexing, local order models, theta coefficients and witness specialization
are separate.

Final verified result SHA (before this fleet note): `c472857f373cf931b8e8c38d2820972afcc5b4c3`.

Report: `docs/research/rc-pm.md`. Results log: `scratch/rc-pm/log.md`.
