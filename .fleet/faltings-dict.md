# Faltings’ DVR dictionary handoff

**VERIFIED in Lean.** The model hypotheses of `FaltingsLemma1DVR` imply
Faltings’ semiabelian conditions for both models on the reading desk’s
account of p. 350. The closed fibre itself is an extension of an abelian
variety by a torus, both fibres have dimension `dim A` in each model, and the
model is commutative. The kernel is expressed on affine points over an
algebraic closure of the residue field. The specialization proof also uses
normality and the identification `Spec K = D(π)` as the dense generic open.

`FaltingsDict.lean` compiles. All 20 new theorems use only `propext`,
`Classical.choice`, and `Quot.sound`. Live `#discharges` matched
`faltingsSemistableHeightBC` with `FaltingsLemma1DVR` and the two existing
inputs for Raynaud’s criterion and Néron existence. The dry run was
**5 LEAF / 24 GLUE → 6 LEAF / 23 GLUE** in both counts on 29 H fields.
No existing declaration was edited and no fold was applied.

The Lean objections are cleared for **LEAF / LEAF (b)** on the recorded
reading. Lemma 1 remains a literature input; the separate source reading and
skeptic pass are still required before landing. The manuscript cites the
paper at L621 and L733, without citing Lemma 1. The earlier height-invariance
locator and citation attribution are corrected in the
[report](../docs/research/faltings-dict.md), which links the check outputs.
