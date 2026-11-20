# Results log

- Base: 4fb8bc1d9100f188de0512ad63191454d3aed4a6.
- Initial worktree cache lacked the Picard and orbit dependencies; serial compilation checks the devserver load and available memory before each invocation.
- Local affine conjugacy: trace and determinant classify a nonscalar matrix by the cyclic companion basis; in a division algebra the intertwiner is X+Y or the commutator Xw−wX.
- Completed quadratic torus: extend scalars to each finite completion above p; use CRT for dense simultaneous integral approximation. Power divisibility at all places above p recovers divisibility by p in the global ring of integers.
- Conjugacy.lean: passed `lake env lean`. Ambient conjugacy in the split and division models; span description of the centralizer.
- CompletedIntegers.lean: passed `lake env lean`. Scalar maps, prime index compatibility, density, and divisibility.
- QuadraticCompletion.lean: passed `lake env lean`. Bijective affine evaluation; integral coefficient test; completed quadratic ring equivalence.
- Ambient.lean: passed `lake env lean`. Reference root and split characteristic polynomial.
- The unchanged Picard assembly and its imports compile from the base.
- SplitRealization.lean: passed `lake env lean`. Integral companion at exponent zero; both prescribed level bits at positive exponent.
- Torus.lean: passed `lake env lean`. Units equivalence onto the centralizer, compatibility on diagonal field units, and the conjugated integral unit test at every prime.
- Realization.lean: passed `lake env lean`. Both detecting bits and `∀ t, HasLocalRealizations s α t`. The kernel checks the division chart compatibility through an abstract transport lemma.
- Assembly.lean: passed `lake env lean`. `picardFibers` and `orbitFibers` instantiate the existing assembly with the two verified inputs.
- Axioms.lean: passed `lake env lean`. Printed 97 theorem constants and 18 definition constants, including generated declarations. Allowed axioms only: `propext`, `Classical.choice`, and `Quot.sound`.
