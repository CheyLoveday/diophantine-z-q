# vpdual-merge

Goal: replace the two added-bundle rows `scholzeH1AbVar` (`DeRhamScholze.HTMerge.ScholzeH1AbVar`)
and `t10TateDuality` (`T10Etale.T10_TateDuality`) of `ZInQ.OneProof.frozenTarget` by one weaker
row about the dual Tate module, `vpDual : DeRhamScholze.HTMerge.VpDualDeRhamAbVar`: `V_p(A)^∨` is
de Rham, its Hodge jumps lie in `[0, 1]`, and `dim_{ℚ_p} Fil¹ D_dR = [F:ℚ_p] · g`. Count 22 → 21;
strict and strictest GLUE 16 → 15 (in the H bundles, 6 published / 13 glue → 6 / 12); LEAF
unchanged. No statement gets stronger: the pair implies the new row (`vpDual_of_pair`).

This is an alternative to the draft PR #204, which proves `t10TateDuality` equivalent to
Milne (1986), Thm 15.1(a) with Rem. 15.5. The two routes cannot both land as they stand: this one
removes the row that #204 restates. The owner chooses between them. This contribution claims
neither row.

Base: `main` at `c05342735cf71fe001e0dcf8c617743f62d135ba` (docs only since `72ab3180`).

## Files

* `Row.lean`: the row and its conversions, in `DeRhamScholze.HTMerge`.
  * `VpDualDeRhamAbVar`, with its three clauses `VpDualIsDeRham`, `VpDualHodgeRange`,
    `VpDualFilOneDim` (each with its sources); `vpDualDeRhamAbVar_iff` unfolds them (`Iff.rfl`).
    `V_p(A) = ℚ_p ⊗ T_p(A)` is `A.V p` with `A.galRep p`, built from the `F̄`-points of `A`.
  * `vpDual_of_pair : ScholzeH1AbVar → T10_TateDuality → VpDualDeRhamAbVar`, through the existing
    `HTMerge.dual_of_H1` (with `mumfordTorsionAlgClosed_proof`).
  * The three outputs of the `HTMerge` theorems from the row alone:
    `deRhamVpAbVarDirect_of_vpDual`, `hodgeTateDecompOr_of_vpDual` (through
    `hodgeTateDecompHom_of_vpDual`) and `hodgeTateDecompAbVar_of_vpDual` (through
    `htDecomp_of_vpDual`).
* `Chain.lean`: the generated copy reroute (below), new top
  `HDec.HSyn.sixContactMin_of_open98_vp (r : OpenResearchLeaves78) (t : OpenTextbookLeaves18)
  (l : OpenAddedLeaves29VP)`.
* `gen_vp.txt`: the generator (a Python script, shipped as text because the scope gate admits no
  `.py`): `python3 gen_vp.txt REPO_ROOT OUT_DIR [AUDIT_FILE]`. It reads named files only.
* `FoldCheck.lean`: `addedLeaves29VP_ofLive`, a fully qualified `example`,
  `frozenTarget_with_vpDual` (`frozenTarget`'s body verbatim with only the top swapped), and
  `#print axioms` for every new theorem.

## Where the two fields are read

On the live route (`sixContactMin_of_open98` → `DS965Reroute/Chain5`…`Chain3`), the pair is read
in three places, each passing both fields together into one `HTMerge` theorem:

| Declaration (live copy) | File | Reader |
|---|---|---|
| `openResearchLeaves60_y3x6_of_OpenResearchLeaves63_nos_ds` | `DS965Reroute/Chain3.lean` L1666 | `hodgeTateDecompOr_of_scholzeH1Milne` |
| `sixContactMin_of_open82_nos_ds` | `DS965Reroute/Chain3.lean` L1711 | `hodgeTateDecompAbVar_of_scholzeH1` |
| `openResearchLeaves65_of_OpenResearchLeaves66_ds` | `DS965Reroute/Chain4.lean` L520 | `deRhamVpAbVarDirect_of_scholzeH1Milne` |

Everything else on the route only passes the bundle on (`sixContactMin_of_open83_nos_ds`, the
copies of `TailZ91`–`TailZ103` in `Chain4`/`Chain5`, `openAddedLeaves28_of_OpenAddedLeaves29`,
`sixContactMin_of_open98`) or reads `conradAppB` (`c8Leaves_of_OpenAddedLeaves28`).

Checked by reading named files, and found off the live route:

* `TailZ87` L94/L120, `TailZ88` L91/L122, `TailZ89` L90/L122, `TailZ92` L76: the originals of the
  conversions above. The live route uses their copies (`NOSNarrowChain` → `DS965Reroute`).
* `NOSNarrowChain.lean` L4691/L4728: the originals of the two `Chain3` readers.
* `C8Chain.lean` L1427/L1439 (`sixContactMin_of_open72_sf_u_hm`, `sixContactMin_of_open79_hm`)
  and `CMR5.lean` L1049/L1074/L1087 (`…_hm_cm_r5`, `sixContactMin_of_open80_cm_r5`) take
  `(hN : ScholzeH1AbVar) (hT : T10_TateDuality)`. They feed the superseded tops
  (`sixContactMin_of_open80`, `…_open80_cm_r5` and the generations above them), not the live top,
  whose declarations take no such argument.
* No mention of either field or row in `TailZ90`, `TailZ93`–`TailZ105` (apart from forwarding
  `OpenAddedLeaves28`/`29`), `Y3Copy1`–`Y3Copy6`, `D2A6Chain`, `CMOpen`, `NOSNarrow`,
  `NOSNarrowNC`, `CMCurveOrderLiveNOS`, `DS965Reroute/Chain1`, `Chain2`.

The check does not depend on this list alone. The generator stops if a copied declaration still
names either field or row after the edits. The new bundles lack the two fields, so Lean rejects any
reader of them that was not switched, and any uncopied declaration that is handed the new bundle.

## The copy reroute (`Chain.lean`, generated)

Generated from `TailZ87` (`OpenAddedLeaves28`, `c8Leaves_of_OpenAddedLeaves28`),
`DS965Reroute/Chain3`–`Chain5` (every declaration that the taint from `OpenAddedLeaves28` reaches),
`TailZ104` (`OpenAddedLeaves29`, `openAddedLeaves28_of_OpenAddedLeaves29`) and `TailZ105`
(`sixContactMin_of_open98`). The suffix is `VP` for structures and `_vp` for theorems. 22
declarations:

* `OpenAddedLeaves28VP` = `{conradAppB, vpDual}`, `OpenAddedLeaves29VP` = `{vpDual}`: the pair is
  replaced by `vpDual : DeRhamScholze.HTMerge.VpDualDeRhamAbVar`;
  `openAddedLeaves28_of_OpenAddedLeaves29_vp`: `vpDual := n.vpDual`.
* Readers: `HTMerge.<out>_of_scholzeH1[Milne] l.scholzeH1AbVar l.t10TateDuality` →
  `HTMerge.<out>_of_vpDual l.vpDual` (the three rows of the table above).
* Pass-through copies: `c8Leaves_of_OpenAddedLeaves28_vp`, `sixContactMin_of_open83_nos_ds_vp`,
  `sixContactMin_of_open84_ds_vp` … `sixContactMin_of_open96_ds_vp`, and the top
  `sixContactMin_of_open98_vp` (through `openResearchLeaves77DS_of_OpenResearchLeaves78`, reused).
* The research and textbook bundles are unchanged and reused.

## The fold (integrator): `OneProof/H/TailZ106.lean`

```lean
import ZInQKernel.OneProof.H.TailZ105
import ZInQKernel.Contrib.OneProof.VpDualMerge.Chain

namespace HDec
namespace HSyn

/-- `OpenAddedLeaves29` with `vpDual` in place of `scholzeH1AbVar` and `t10TateDuality`
(vpdual-merge; the pair implies it, `DeRhamScholze.HTMerge.vpDual_of_pair`). -/
structure OpenAddedLeaves30 : Prop where
  /-- (the docstring of `VpDualDeRhamAbVar`: clauses and sources) -/
  vpDual : _root_.DeRhamScholze.HTMerge.VpDualDeRhamAbVar

/-- `OpenAddedLeaves29VP` (the bundle of the copy chain) from `OpenAddedLeaves30`. -/
theorem openAddedLeaves29VP_of_OpenAddedLeaves30 (n : OpenAddedLeaves30) :
    OpenAddedLeaves29VP where
  vpDual := n.vpDual

/-- **G0 with only the open leaves and the open glue** (vpdual-merge-fold). -/
theorem sixContactMin_of_open99 (r : OpenResearchLeaves78) (t : OpenTextbookLeaves18)
    (l : OpenAddedLeaves30) : ZInQ.SixContactMin :=
  sixContactMin_of_open98_vp r t (openAddedLeaves29VP_of_OpenAddedLeaves30 l)

end HSyn
end HDec

#print axioms HDec.HSyn.sixContactMin_of_open99
```

* `Main.lean`: import `ZInQKernel.OneProof.H.TailZ106`; `frozenTarget (r : …OpenResearchLeaves78)
  (t : …OpenTextbookLeaves18) (l : HDec.HSyn.OpenAddedLeaves30) …` through
  `HDec.HSyn.sixContactMin_of_open99 r t l`. `FoldCheck.frozenTarget_with_vpDual` is that body over
  `OpenAddedLeaves29VP`. Add a vpdual-merge paragraph to the module docstring.
* `docs/one-proof/kinds.tsv`: remove the rows `added scholzeH1AbVar` and `added t10TateDuality`;
  add one consequence row (GLUE):

  ```
  added	vpDual	consequence	pending review: new row (vpdual-merge), merges scholzeH1AbVar and t10TateDuality, which imply it (DeRhamScholze.HTMerge.vpDual_of_pair through HTMerge.dual_of_H1; Lean); stated on V_p(A)^dual built from Fbar-points, so the pro-etale vs classical comparison, the rigid analytification and Fbar vs C_p are no longer Lean-side steps but print-to-print steps on classical objects; consequence of several prints: Scholze Cor. 1.8 with Thms 9.1(ii), 9.3 (clauses i-iii on H^1_et(A_Fbar, Q_p)), Milne, Abelian Varieties v2.0 (2008) Part I Thm 12.1(a) with Rem. 12.5 (H^1 = V_p(A)^dual, Galois-equivariantly; the edition read on main; the 1986 Cornell-Silverman Thm 15.1(a) with Rem. 15.5 is not yet read on main, draft #204), h^{1,0}(A) = g (Mumford, Abelian varieties, section 4, locator UNVERIFIED); a LEAF rating needs a ruling on readings that combine several prints	GLUE	GLUE	Scholze, p-adic Hodge theory for rigid-analytic varieties, Forum Math. Pi 1 (2013) e1, Cor. 1.8 pp. 5-6, Thm 9.1(ii) p. 74, Thm 9.3 p. 75, Rem. 8.9 p. 72 (corrigendum Forum Math. Pi 4 (2016) e6: no effect on these); Milne, Abelian Varieties v2.0 (March 16, 2008), Part I, Thm 12.1(a) p. 55 with Rem. 12.5 p. 56 (Milne, Abelian varieties, in Cornell-Silverman (eds.), Arithmetic Geometry, Springer 1986, Thm 15.1(a) p. 129 with Rem. 15.5 p. 131: not yet read on main, draft #204); h^{1,0}(A) = g: Mumford, Abelian varieties, section 4 (UNVERIFIED); manuscript diophantine_zq.tex lem:de-rham-descent L10939-10970 and L10996	vpdual-merge; pending review	R7	long-pole	T4	pending-review,unverified-locator	elliotglazer/diophantine-z-q#84
  ```
* Reviews: move every `reviews.tsv` row of `scholzeH1AbVar` and `t10TateDuality` to
  `reviews-retired.tsv`. At `c0534273` neither file has a row for either field, so this step is
  empty unless a review lands before the fold.
* Claims: `t10TateDuality` is held by the project (claim on #14); its claim is closed with the row.
  PR #204 restates that row, so it must be resolved first, by the owner's choice of route.
* `docs/one-proof/OPEN.md`: regenerate with `scripts/one_proof/render_open.py` (22 → 21; strict
  6 published / 12 glue).
* No existing constant changes. `ScholzeH1AbVar`, `T10_TateDuality` and the `HTMerge` theorems
  stay in the tree for the superseded tops.

## Prints the merged row needs (for the ruling on a reading that combines several prints)

1. Scholze, *p-adic Hodge theory for rigid-analytic varieties*, Forum Math. Pi 1 (2013) e1:
   Cor. 1.8, pp. 5-6 (de Rham, Hodge-Tate decomposition, filtered `D_dR = H^i_dR(X)`), at
   `X = A^an`; Thm 9.1(ii), p. 74 (coherent cohomology of the analytification, for all `i ⩾ 0`);
   Thm 9.3, p. 75, with Rem. 8.9, p. 72 (étale cohomology of the analytification). Corrigendum,
   Forum Math. Pi 4 (2016) e6: no effect on these. Gives clauses (i)-(ii) and
   `Fil¹ = H⁰(A, Ω¹)` for `H¹_ét(A_{F̄}, ℚ_p)`.
2. Milne, *Abelian Varieties* v2.0 (March 16, 2008), Part I, Thm 12.1(a), p. 55, with Rem. 12.5,
   p. 56: `H¹(A_{k_s}, ℤ_ℓ) ≅ Hom(T_ℓ A, ℤ_ℓ)`, compatibly with `Gal(k_s/k)`. Moves (1) to
   `V_p(A)^∨`. This is the edition read on main (the `t10TateDuality` docstring). The same
   statement in Milne, *Abelian varieties*, in Cornell-Silverman (eds.), *Arithmetic Geometry*
   (Springer 1986), Thm 15.1(a), p. 129, with Rem. 15.5, p. 131, is not yet read on main
   (draft #204); that volume is conference proceedings, refereeing status unverified.
3. `h^{1,0}(A) = dim H⁰(A, Ω¹_A) = g`, for clause (iii): Mumford, *Abelian varieties*, §4
   (`Ω¹_A ≅ 𝒪_A^g`), the source the row `scholzeH1AbVar` names; locator unverified.

Candidates for a version without Scholze (not read here): Colmez, *Périodes p-adiques des
variétés abéliennes*, Math. Ann. 292 (1992), Thm 5.2(ii), p. 639. Its period pairing
`H¹_dR(A) × T_p(A) → B_dR` is Galois-equivariant, sends `H⁰(Ω¹)` into `Fil¹ B_dR`, and is
non-degenerate over `B_dR`. That gives clause (i) on `T_p(A)` directly (no Milne step) and
`Fil¹ ⊇ H⁰(Ω¹)`. With the Hodge-Tate decomposition `ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^g ⊕ ℂ_p^g` of
Fontaine, *Formes différentielles et modules de Tate des variétés abéliennes sur les corps
locaux*, Invent. Math. 65 (1982), and the equality of Hodge and Hodge-Tate numbers for de Rham
representations, it would give clauses (ii)-(iii). It would be a reading of two or three prints as
well.

## Open points

* Rating: GLUE (a consequence of several prints). A LEAF needs the owner's ruling on readings that
  combine prints, and a source for `h^{1,0} = g`.
* The route excludes #204's route; the owner chooses.
* If `main` gains a `TailZ106` first, re-run `gen_vp.txt` with its top in `SOURCES` and `TOP_OLD`.
