# derham-range (11-17)

**Main result.** I proved `DeRhamPrint.Range.range_iotaF_eq_bdrFix`: the range of `iotaF : F' → B_dR` is exactly
`B_dR^{G_F}`. The proof uses `bdrAct_iotaF`, the injectivity of `iotaF`, `bdRInvariantsPrinted_proof` and
`finrank_fieldF`. With it, `deRhamVpAbVarDirect_iff_adm` proves that the leaf's `dim_{F'}` form is equivalent to the
admissibility form `DeRhamVpAbVarAdm`: `dim_{B_dR^{G_F}} D_dR(V_p A) = dim V_p A`, with `B_dR^{G_F}` an intrinsic
subalgebra (`bdrFixAlg`, which is a field, `≃ₐ F'`). This resolves the review's missing lemma. Both dimension
readings of Berger's definition are now definition-level.

**Compiles.** `ZInQKernel/Contrib/OneProof/DeRhamRange.lean` (scratch copy `scratch/derham-range/DeRhamRange.lean`)
builds and uses the standard axioms only. `#discharges` shows that it discharges `deRhamVpAbVarDirect` from
`DeRhamVpAbVarAdm`. The optional `scratch/derham-range/autofold.json` has a dry run with the count unchanged
(9/25), and the dry-run fold compiles.

**Not done.** I could not read Berger (arXiv math/0210184v1, §II.2-II.3, §II.5): there is no DNS on this host, so
the download failed. The leaf stays GLUE. The recommended hand edit of the kinds row is to keep the leaf, set
flag_class `pending-reading`, and use the new flag text (exact row in docs/research/derham-range.md). A reader must
check whether Berger defines de Rham by dimension (then the row becomes LEAF) or by `B_dR ⊗ V ≅ B_dR^d` (then a
consequence step is needed), and whether A is over K in §II.5. Do not apply the autofold swap unless the reading
finds the admissibility form.
