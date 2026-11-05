# Dependency boundaries

The 82 application records distinguish an external theorem from the internal constructions needed to apply it. Source/application acceptance checks the stated result, its hypotheses and conventions, and the recorded translation. It does not make an internal premise true merely because another accepted record cites it.

## Finite models and Selmer duality

A075 contains four different steps. Their order matters.

| Step | Inputs | Output |
|---|---|---|
| Finite-model construction | Bounded finite residual cohomology, the actual coefficient rings and local point-group structure | Bounded finite free models and contractions |
| Transport and specified limits | Supplied maps and homotopies; the stated compatibility, finiteness and stage-existence conditions | Transported diagrams and retained identities |
| Duality on those models | Perfect coefficient pairings and actual orthogonal local diagrams | Selmer duality comparisons |
| Arithmetic budgets | The preceding duality, Selmer corank inputs and local determinant bounds | Dimension, rank and torsion estimates |

A037's local Kummer comparison uses the first step and finite local duality. A038 then applies global Selmer duality to the actual local diagrams. A045 derives the self-dual dimension and torsion formulas; these feed A075's arithmetic budgets. Those budgets are not the proof that the original complexes are perfect.

The A080 repair supplies the custom derivative local maps and their compatibility homotopies for the actual split and totally ramified extensions. It does not prove global exact-annihilator or rank statements. A044 obtains its exact-annihilator conclusion from global duality, while retaining the separate hypotheses that the old class spans generic cohomology, its localization is nonzero, and the actual derivative has the stated local coordinates.

A041 likewise retains the arithmetic norm relation, its boundary, the paired lift and the integral cone-basis comparison. Naturality of the pairing alone does not supply those inputs or the asserted unit factor.

## Arithmetic inputs

A040 uses the algebraic isogeny ratio where forward theorems already give the required finite Tate–Shafarevich groups. A045's full-Selmer-corank calculation allows a divisible Tate–Shafarevich part and is a different argument. A082 supplies the forward analytic-rank-zero input; it does not prove the separate real-place cohomology calculation.

A081 uses local Iwasawa control, local duality and finite local elliptic torsion to prove the nonzero central value of the fixed clearing factor. Its local Kato input is separate from the global Euler-system divisibility in A023. The latter may therefore consume A081 without a circular argument.

A067 and A068 track the actual finite extensions, characters and Frobenius prescriptions. A076's compactness arguments consume nonempty compatible arithmetic stages; compactness does not establish their existence.

## Reused lemmas and historical repairs

Some application families contain a reusable lemma and a later application of it. In A064, the semisimple character/density lemma can be used by A011 before the final comparison of the constructed representations. That final comparison depends on A011. Similarly, A013's local semistability theorem precedes the conductor bound in A012. These are ordered uses of different statements, not mutual proofs of whole application records.

The final records should be read with their linked repairs and manuscript anchors. In particular, the earlier A080 local-data finding is resolved by its later explicit construction and review, not by reinterpreting the original class-coordinate identities as sufficient. Earlier open-item reports describe their own review stage.

These boundaries permit a complete inventory of scoped decisions while preserving the distinction between checked external applications, their internal premises, and the manuscript's overall proof.
