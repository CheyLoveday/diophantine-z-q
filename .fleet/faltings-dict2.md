# Faltings’ Lemma 1: print-form handoff

**VERIFIED in Lean:** Both bridges are complete. The proposal is **LEAF /
LEAF**, provenance **(b)**, on the reading desk's record of Faltings,
Invent. Math. 73 (1983), p. 350, Lemma 1, subject to the third skeptic pass.

`FaltingsLemma1DVRPrint` uses the printed conclusion: a generic
homomorphism extends uniquely as a morphism. The unit and multiplication
equations follow by injectivity on the generic open, giving
`faltingsLemma1DVR_iff_print`. The pointwise torus data identify the
kernel, realized as a closed subgroup by a fibre product, with the
split Laurent polynomial group scheme over the algebraic closure. The comparison is an
isomorphism of group schemes, and the scheme-level fibre dictionary
covers both fibres and both models.

All four new modules compile, and the axiom audit checks only
`propext`, `Classical.choice`, and `Quot.sound`. The live discharge
takes the print-form leaf and the same two existing inputs. The dry
run gives **5 LEAF / 24 GLUE → 6 LEAF / 23 GLUE** on 29 H fields in
both counts. No fold was applied. The remaining step is the review of
the proposed rating; the print was not reread here.

The full report is [here](../docs/research/faltings-dict2.md); the
[reproducers and outputs](../scratch/faltings-dict2/) include the axiom
audit, the live discharge check and the fold manifest.
