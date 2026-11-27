# Old-stage weighted theta law

**Scoped stop.** `oldStageLaw_of_finiteAction` supplies the exact `BlocksPerU.OldStageLaw` expected by `realize_of_stage` once the prescribed finite weight has its relative Weil action and the old character is identified. The expansion is the existing `Lift.aθ` for the given stage and fixed sieve, at the existing old level.

The seven modules in `ZInQKernel/Contrib/OneProof/RC/OldStageLaw/` pass `lake env lean`; the 44 `#print axioms` checks list only `propext`, `Classical.choice` and `Quot.sound`. The proofs give translation from integral support, inversion by Jacobi Poisson summation, the action along ambient modular words, holomorphy, bounded normalized values at every cusp, and absolute regrouping by the extracted norm. The local lemmas give the Fourier support and lower unipotent depth test, the relative diagonal factor, and the reciprocity step combining the odd and dyadic signs.

The remaining inputs are `StageGrid` for the existing class weights, the pullback identity for (O.5), and `RelativeFiniteAction`: the finite Fourier and phase operators must act on the given coset vector by the old character times their scalar on the ordinary reference vector, for words representing elements of the stated `Γ₀` group. This needs the comparison with the normalized local Weil operators, including the depths of the actual fixed-sieved vectors. No additional printed leaf or separate local weight construction was added. No manuscript error was identified in the scoped steps.

Report: `docs/research/rc-old-stage-law.md`. Final result SHA (Lean, report and log): `4d09fba2df23c6043c2ab3cac4f4ad96f02245d2`.
