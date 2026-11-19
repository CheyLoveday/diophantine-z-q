# Results

- Base `5152f326a7716248d0fd8dd905f70ddca6c05ad0`; merged `42f91fa8e53341a321c5f40e26181d7a0856c5ee` cleanly.
- Tex 2915–2919 states the field-of-definition clause; Cai–Chen–Liu §2 passage unread. The archived audit locates the trace relation at Theorem 2.15, p. 3730. The pinned offprint is absent.
- The existing weak-Weil and minimal-level modules supply a cusp form and analytic period scale. The existing function field pullback and analytic differential comparison start from a rational parametrization point; they do not identify a rational morphism with the recorded fixed `phiAn`.
- An actual projective Weierstrass scheme model, with its affine chart and point at infinity, is present in `RC53Assist/IsogenyScheme/ProjectiveModel.lean`. The canonical rational modular curve and its complex comparison are missing.
- `Prints.lean`: passed `lake env lean -j1`. `CMFieldOfDefinition` states the sole approved printed-form leaf on the canonical modular curve. Its field-valued points are morphisms over `ℚ`; the complex comparison is part of `X0Model`.
- `Parametrization.lean`: passed `lake env lean -j1`. Audits: `mem_affineOpen_of_ne_pointO`, `range_le_affineOpen`, `specToAlgHom_map`, `projectiveValue_map`. The point evaluator uses the actual `Proj` model, the affine coordinate ring, and infinity. `AlgebraicParametrizationAtScale` is the missing rational morphism and fixed analytic comparison.
- `Descent.lean`: passed `lake env lean -j1`. Audits: `value_of_cmFieldOfDefinition`, `discr_conductorOne`, `coprime_level`, `preparedParamValues`. The last theorem supplies the whole prepared family from the one source-curve CM statement and the fixed scale comparison.
- `Consumers.lean`: passed `lake env lean -j1`. Audits: `genusParamValues`, `missingParamValues`, `gz34CompAt_of_scaledParametrization`. The adapters use the same prepared family; the rough-companion wrapper has no independent `halgG`.
- All eleven audits: `[propext, Classical.choice, Quot.sound]`. No direct TYZ import; the existing selector's character code already imports a TYZ arithmetic module.
