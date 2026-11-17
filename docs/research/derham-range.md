# derham-range: `ι(F') = B_dR^{G_F}`, and the admissibility reading of `deRhamVpAbVarDirect` made definition-level

Task: review queue14 (11-17) on the research leaf `deRhamVpAbVarDirect` (`DeRhamPrint.Direct.DeRhamVpAbVarDirect`,
`ZInQKernel/Contrib/OneProof/DeRhamPrintDirect.lean`; kinds.tsv row GLUE/GLUE, pending review). The review said:
Berger's definition of "de Rham" is unread, and under the admissibility reading (dimension over `B_dR^{G_K}`, with
`B_dR^{G_K} = K` stated separately) the leaf's `dim_{F'}` form needs `ι(F') = B_dR^{G_F}`, which no lemma stated.

## Verdict

1. **Proved** (VERIFIED, compiles, standard axioms only): `DeRhamPrint.Range.range_iotaF_eq_bdrFix`:
   `LinearMap.range (iotaF p F).toLinearMap = bdrFix p F`. The range of `iotaF : F' → B_dR` is exactly the
   `G_F`-invariants of `B_dR`.
2. **Proved** (VERIFIED): the leaf's `dim_{F'}` form is equivalent to the admissibility form,
   `DeRhamPrint.Range.deRhamVpAbVarDirect_iff_adm : DeRhamVpAbVarDirect ↔ DeRhamVpAbVarAdm`, where
   `DeRhamVpAbVarAdm` says `dim_{B_dR^{G_F}} (B_dR ⊗ V_p A)^{G_F} = dim_{ℚ_p} V_p A`, with `B_dR^{G_F}` defined
   intrinsically (`bdrFixAlg`, a `ℚ_p`-subalgebra of `B_dR`, no embedding of `F`). So the admissibility reading is
   now definition-level: whichever of the two dimension readings Berger uses, the Lean leaf is a direct instance.
3. **Not done: reading the print.** The one allowed download (arXiv math/0210184v1) failed: `curl: (6) Could not
   resolve host: arxiv.org`, inside and outside the sandbox (VERIFIED, log.md). There is no local copy. I could not
   check how Berger defines B-admissible, `D_dR` and de Rham (§II.2-II.3), or whether `A` is over `K` in §II.5.
   **The flag stays open, as pending reading.** The target "deRhamVpAbVarDirect LEAF" is not reached: the count is
   unchanged.

From memory (SPECULATIVE, UNVERIFIED): surveys in Fontaine's formalism usually define "V is B-admissible" as
`B ⊗_{ℚ_p} V ≅ B^d` (B-semilinearly and G_K-equivariantly). For a (ℚ_p, G_K)-regular B they then prove that this is
equivalent to `dim_{B^{G_K}} D_B(V) = d`. If Berger's §II.2 does this, the dimension form is a proposition printed
in the same section. Then the leaf is a consequence of the print's definition plus that printed proposition, and it
is not a definition-level instance. A reader of pp. 11-13 should record which one Berger uses.

## What is in Lean

File `ZInQKernel/Contrib/OneProof/DeRhamRange.lean` (namespace `DeRhamPrint.Range`, same content as
`scratch/derham-range/DeRhamRange.lean`). It imports `DeRhamPrintDirect` and `BdRInvariants`:

| declaration | statement | proof from |
|---|---|---|
| `iotaF_injective` | `iotaF` injective | `B_dR` a field (`isField_BDeRham`) |
| `range_iotaF_le_bdrFix` | `range ι ≤ B_dR^{G_F}` | `bdrAct_iotaF` |
| `range_iotaF_eq_bdrFix` | `range ι = B_dR^{G_F}` | the above, `bdRInvariantsPrinted_proof` (`dim B_dR^{G_F} = [F:ℚ_p]`), `finrank_fieldF`, `Submodule.eq_of_le_of_finrank_eq` |
| `set_range_iotaF`, `mem_bdrFix_iff` | set and membership forms | |
| `bdrFixAlg` | `B_dR^{G_F}` as a `Subalgebra ℚ_[p] (BdR p)` (`toSubmodule_bdrFixAlg`: carrier = `bdrFix`) | `bdrAct` a ring hom, `bdrAct_smul` |
| `bdrFixEquiv` | `fieldF p F ≃ₐ[ℚ_[p]] bdrFixAlg p F` through `iotaF` | the range lemma |
| `isField_bdrFixAlg` | `B_dR^{G_F}` is a field | `bdrFixEquiv` |
| `ddrFix` | `D_dR(W) = (B_dR ⊗ W)^{G_F}` as a `bdrFixAlg`-submodule (same carrier as `ddrTensorOver`, `restrictScalars_ddrFix`) | `map_smulFix` |
| `finrank_ddrFix` | `dim_{B_dR^{G_F}} ddrFix = dim_{F'} ddrF` | `rank_eq_of_equiv_equiv` along `bdrFixEquiv`, `smul_eq_iotaF_smul` |
| `IsDeRhamAdm`, `isDeRhamAdm_iff`, `isDeRhamAdm_iff_tensorOver` | admissibility form ⇔ `dim_{F'}` form ⇔ `IsDeRhamTensorOver` | |
| `DeRhamVpAbVarAdm` | the leaf in admissibility form | |
| `deRhamVpAbVarDirect_iff_adm`, `deRhamVpAbVarDirect_of_adm`, `deRhamVpAbVarPrinted_of_adm` | the bridges | |

Compile: `lake env lean scratch/derham-range/DeRhamRange.lean` gave no errors and no warnings after the edits.
`#discharges` and `#print axioms`: `scratch/derham-range/Discharges-output.txt`.

## Leaf rating

* `DeRhamVpAbVarDirect` (existing) and `DeRhamVpAbVarAdm` (new, optional): both are **printed form under a dimension
  reading** of Berger's definition, and they are now proved equivalent. Neither is printed form if Berger defines
  de Rham by the isomorphism `B_dR ⊗ V ≅ B_dR^d`; then each would be a consequence through Fontaine's regularity
  proposition. That is unread, so the leaf stays GLUE.

## Kinds row (hand edit; recommended now)

Keep the leaf `deRhamVpAbVarDirect` (no statement change, no fold needed). Replace the row's flag and flag_class:

```
research	deRhamVpAbVarDirect	published	pending reading: Berger's definition of de Rham (section II.2-II.3, pp. 11-13) unread (no download possible in derham-range); a direct instance of Berger II.5.1 p. 19 under either dimension reading: dim_K via the theta-compatible K -> B_dR^+ (derham-direct) and dim over B_dR^{G_K} (admissibility), proved equivalent through iota(F') = B_dR^{G_F} (derham-range: range_iotaF_eq_bdrFix, deRhamVpAbVarDirect_iff_adm); an isomorphism-form definition (B_dR (x) V = B_dR^d) would add a consequence step; primary Fontaine numbers UNVERIFIED	GLUE	GLUE	<source unchanged>	leaf-fold33-batch-w98; derham-range; pending reading	R7	long-pole	T4	pending-reading	elliotglazer/diophantine-z-q#84
```

(kind `published`, strict/strictest GLUE/GLUE unchanged, flag_class `pending-review` → `pending-reading`.) Reason:
the review's second concern, the missing `ι(F') = B_dR^{G_F}`, is resolved. What is left is a reading of the
print's definition. That clears through reading (two readings or a known reader), not through a rating. If a
reading finds a dimension-form definition and that `A` is over `K` in §II.5, the row becomes LEAF with flag
`unread: ...`/note (one GLUE fewer).

## Autofold spec (optional; only if a reading finds the admissibility form printed)

`scratch/derham-range/autofold.json` discharges `deRhamVpAbVarDirect` by `deRhamVpAbVarDirect_of_adm` from the new
leaf `deRhamVpAbVarAdm` (kind `published`, flag beginning "pending reading: ...", so autofold rates it GLUE). Dry
run (`scripts/one_proof/autofold.py ... --dry-run`, output `scratch/derham-range/autofold-dryrun.txt`):
`strict count: 9/25 on 34 -> 9/25 on 34`, so the count is unchanged. With a flag beginning "pending review",
autofold would rate the leaf LEAF (autofold.py line 196). That would raise the count without a reading, so I did
not use that flag. Recommendation: do not apply the spec unless the reading shows Berger's definition is the
admissibility one. The `dim_K` form (the current leaf) is equally close to the most likely prints.
