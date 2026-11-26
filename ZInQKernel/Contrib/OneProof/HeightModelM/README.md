# HeightModelM: the Néron-model height is Gaudron–Rémond's semi-abelian-model height

Item M of the Gaudron–Rémond statement checks. An adversarial reading of the rows
`gaudronRemondSec9LowerAnSS` (GR1, Comment. Math. Helv. 89 (2014), Cor. 8.4) and
`gaudronRemondThm14AnSS` (GR2, Duke Math. J. 163 (2014), Thm 1.4) found no Lean identification
between the height computed on the full semistable Néron model (`IsAnStableHeightSS`) and the
height GR1 §2.3 defines on a semi-abelian model. This directory supplies it, from one printed
leaf, EGA IV₃ (9.7.7).

WIP: the description below is updated as the hosted check runs.

## Files

| file | content |
|---|---|
| `EGA977.lean` | the leaf `EGAIV_9_7_7_OL` (EGA IV₃ (9.7.7)(ii) at `Spec 𝓞_L`), and the glue `genericConnectedFibresOL_of_ega`: a locally constructible subset of `Spec 𝓞_L` containing the generic point has finite complement. Mathlib only. |
| `OpenIdComp.lean` | `isOpen_idCompSet_of_ega`: `𝒢⁰` is open for every group model over `𝓞_L`; `SGA3_VIB_3_10_NeronOLPrinted` and its proofs. |
| `SemiAbelianModel.lean` | `IsSemiAbelianModel` (GR1's "modèle semi-abélien"), `exists_semiAbelianModel`: `𝒩⁰` is a semi-abelian group model with an open immersion homomorphism onto `𝒩⁰ ⊆ 𝒩`. |
| `MetricTransport.lean` | along an open immersion homomorphism `𝒢₀ → 𝒩`: the Hodge lattice and the index of a section (`secIndex_hodgeMap`), the analytic topology, holomorphic charts and the measures `(i/2)^g η̃ ∧ η̄̃` (`isAnMetricSq_hodgeMap`). |
| `GR1Height.lean` | `IsGR1StableHeightOriginal` (GR1 §2.3, original normalization `h_F`) and `isGR1StableHeightOriginal_of_isAnStableHeightSS`. |
| `Rows.lean` | `GaudronRemondSec9LowerGR1`, `GaudronRemondThm14GR1` and their implications to the current rows. |
| `FoldCheck.lean` | `frozenTargetM`: `frozenTarget` with the two rows replaced by the GR1 rows plus the EGA leaf. |
| `Check.lean` | `#print axioms`. |
