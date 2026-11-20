# Relative finite Weil action

**Scoped stop.** The ordinary reference table is an eigenvector for **every** word in the old congruence subgroup: the six reference lines track the bottom row modulo four, and `LevelSetup.four_dvd` gives the required depth. The finite table proofs also give exact Fourier inversion, the displayed upper and lower words, the reflection word on even weights, and composition for actual word concatenations. The stage upper action uses the given `StageGrid.extracts`; the lower action uses an explicit annihilator depth check at the existing old level.

Under the existing Weil-index hypotheses, the common-lift unit factorization gives the relative diagonal scalar `αₚ(u)(u,m)ₚ`, including at two. The abstract spherical case covers other places once their generators fix the given local vectors. The inverse matrix uses the original lower-right entry; the separate dyadic sign and odd-prime product give `(m/d)`.

**Remaining:** prove the common `IntertwinesGenerators` identities for the two rectangular coset spaces, with the same lifts and scalars, and supply the stage's classwise depth, scaling, spherical and character identifications at the actual old level. The concrete stop is at the phase and Fourier generators, independently of the character and the choice of weight. Once those inputs are instantiated, the transport lemma gives the weighted table equation and the existing `oldStageLaw_of_finiteAction` applies.

All six new Lean files pass `lake env lean`. Their 55 axiom audits list only `propext`, `Classical.choice` and `Quot.sound` or a subset. No new printed leaf or manuscript error was identified in scope.

Report: `docs/research/rc-relative-action.md`. Final result SHA (Lean, report and log): `03dad081eeb0afa520024afe460ec158569605a2`.
