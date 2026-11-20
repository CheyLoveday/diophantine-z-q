# cm-port2 — ready to fold

**VERIFIED (Lean).** On fork main `c3624d0e3`, the port discharges the
unchanged `HDec.CMBranch.CMFibreSplit` from seven fields already in
`OpenResearchLeaves64`. The generated fold adds no assumptions:
**H strict LEAF/GLUE 5/27 on 32 → H strict LEAF/GLUE 5/26 on 31**.
The curve order and matrix-unit proofs are unchanged.

The Hom-field proof now calls `good_of_QML3U` with `T324_subset_T u`.
Its good-reduction input comes from properness of the integral `Y₃` model and
the universal abelian scheme (`thm:height`, L529–530, used at L557–561).
The wild-inertia component of `R6U` remains the existing conductor input
(L814–818). The old all-inertia Raynaud premise is no longer needed by the
CM provider. The relative polarization comparison remains an open reading
point for the existing integral-model row; this port adds no claim about it.

The provider, open84 fold, and scratch `ZInQ.FrozenTarget` compiled with only
`propext`, `Classical.choice` and `Quot.sound`. The scratch headline keeps
Main's textbook and added bundles and `hRC`, `h54`, `hB`, `hK`. Both
`#discharges` transcripts, including `DISCHARGES [cmFibreSplit]`, are in
[scratch/cm-port2/discharges.txt](../scratch/cm-port2/discharges.txt).

Integration remains: apply [the autofold spec](../scratch/cm-port2/autofold.json)
to Main, using [the checked preview](../ZInQKernel/Contrib/OneProof/CMCurveOrder/FoldOpen84.lean)
as a reference, and update the open-row documentation. This branch does not
edit Main or kinds.tsv. See [the report](../docs/research/cm-port2.md).
