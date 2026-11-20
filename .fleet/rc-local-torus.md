# rc-local-torus handoff

Both placewise hypotheses of `picardFibers_of_local` are proved. The completed torus chart respects diagonal field units and detects conjugated completed order units. Every tuple is realized, using the maximal split companion, both Eichler level labels, and both detecting residue labels.

`LocalTorus.picardFibers` and `LocalTorus.orbitFibers` give a `ClassGroup (𝓞 F)` equivalence to each actual orientation fiber. They take the actual stage, full filter including the fixed-partner detecting symbol, quadratic integral basis, chosen rational embedding, and support bridge.

All eight Lean modules and the scratch axiom audit compile individually with `lake env lean`. The audit accepts only `propext`, `Classical.choice`, and `Quot.sound`. No new print was used. The [report](../docs/research/rc-local-torus.md) records the remaining inputs to (O.7). No placewise Picard input remains.

Final proof and report commit: `f0727ec88f5c61f14b3d4eb9571113d0ad1159e2`. This handoff follows it as the last commit.
