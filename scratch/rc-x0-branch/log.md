# X₀(N) normalized branch comparison

- Base: `ecddf799e810fca2ad339aaa984ac80c8203700a`.
- Target: equality of the two valuative points above one j-fiber implies a stabilizer match of their punctured second-coordinate germs.
- `X0Branch.eventually_eq_of_unramified`: local uniqueness of complex evaluations with a shared base evaluation. Compiled serially with `lake env lean -j1 -DautoImplicit=false`; 5 clean axiom checks.
- Affine evaluation: use a basic open of the inverse image of the finite j-chart for local membership. Section continuation gives the pullback germs. The second coordinate is a ratio with eventually nonzero denominator on punctured neighborhoods. `AffineEval.lean` compiled with 17 clean axiom checks.
- Normalized overlap: use an étale coordinate, the diagonal idempotent and local open mapping. The projection and the local modular orbit argument prevent a constant coordinate pullback.
- `Overlap.lean`: `eventually_overlap_of_complexPoint_eq` matches actual punctured complex points with the second parameter in any prescribed neighborhood. Compiled; 6 clean axiom checks.
- `Model.lean`: `exists_stabilizer_germ_match`, `complexPoint_eq_iff`, and `model (N : ℕ) [NeZero N] : PreparedParam.X0Model N`. Compiled; 3 clean axiom checks.
- All four files compiled with serial `lake env lean -j1 -DautoImplicit=false`. All 31 axiom checks: `propext`, `Classical.choice`, `Quot.sound`.
