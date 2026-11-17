# derham-direct: `deRhamVpAbVarPrinted` as a direct instance of Berger II.5.1

Task derham-direct, 2026-11-17. Base `wip/leaf-fold33b` 2da302cd7. Log `scratch/derham-direct/log.md`.

## 1. Result

**The research field `deRhamVpAbVarPrinted` (`DeRhamPrint.DeRhamVpAbVarPrinted`, GLUE, pending review) is
proved in Lean from a new leaf `DeRhamPrint.Direct.DeRhamVpAbVarDirect` that states the print's own form, and the
two Props are equivalent** (`deRhamVpAbVarPrinted_of_direct` and its converse `direct_of_deRhamVpAbVarPrinted`,
standard axioms, VERIFIED). Under the integrator's ruling (relayed reading, notes `readings/derham.md`, not in this
tree) the new leaf is a direct instance of Berger, *An introduction to the theory of p-adic representations*
(Geometric aspects of Dwork theory, de Gruyter 2004; arXiv math/0210184v1), §II.5.1, p. 19, "the Tate modules of
abelian varieties are de Rham", attributed to Fontaine: LEAF, flagged "pending review" until a reviewer confirms.

Proofs: `ZInQKernel/Contrib/OneProof/DeRhamPrintDirect.lean` (new file; scratch copy
`scratch/derham-direct/DeRhamDirect.lean`). Autofold spec `scratch/derham-direct/autofold.json`; the dry-run fold
compiles (§4).

## 2. The new leaf

Print (as relayed): `V` is de Rham iff `dim_K D_dR(V) = dim_{ℚ_p} V`, `D_dR(V) = (B_dR ⊗_{ℚ_p} V)^{G_K}`, a
`K`-vector space through `K → K̄ → B_dR^+`.

```lean
def DeRhamVpAbVarDirect : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
      finrank (fieldF p F) (ddrF p (A.galRep p)) = finrank ℚ_[p] (A.V p)
```

The objects (all genuine definitions, none invented for the purpose):

* `K = F' = fieldF p F ⊆ ℚ̄_p`, the image of `F` (g9-derham). `G_F` acts on `B_dR` through pkg-I4's `gfToGqp`,
  whose image is `G_{F'}` (`HodgeSplit.range_gfToGqp_eq`), so `(·)^{G_F}` is the print's `(·)^{G_K}`.
* `iotaPlusF p F : F' →ₐ[ℚ_p] B_dR^+` (new), the Hensel lift of `F' ⊆ ℚ̄_p ⊆ ℂ_p` through bdr-kertheta's
  `θ⁺ : B_dR^+ → ℂ_p`, for **any** finite `F` (g9-derham's `iotaDR` assumes `F/ℚ_p` Galois). It is the print's
  `K ⊆ K̄ ⊆ B_dR^+`: `iotaPlusF_unique` proves it is the only `ℚ_p`-algebra map lifting `F' ⊆ ℂ_p` through `θ⁺`,
  so the choice in its definition is immaterial. `bdrAct_iotaF`: `G_F` fixes `iotaF x ∈ B_dR`.
* `ddrF p ρ : Submodule F' (B_dR ⊗_{ℚ_p} W)` (new): the `G_F`-invariants, an `F'`-space through `iotaF` acting on
  the left factor; the same carrier as HodgeSplit's `ddrTensorOver` (`restrictScalars_ddrF`, `Iff.rfl`).
* `V_p(A) = ℚ_p ⊗ T_p A` and its `G_F`-action: pkg-I4's `A.V p`, `A.galRep p`, as in the old field.
* Period ring: Berger's `B_dR = B_dR^+[1/t]` is the kernel's `B_dR` by derham-print's `TDict.bdREquivAwayT`
  (unchanged; see `DeRhamPrint.lean`).

## 3. The translation (proved, VERIFIED)

`finrank_ddrTensorOver`: `finrank ℚ_p (ddrTensorOver p ρ) = finrank ℚ_p F · finrank F' (ddrF p ρ)`, by
`[F':ℚ_p] = [F:ℚ_p]` (`finrank_fieldF`) and the tower law (`Module.finrank_mul_finrank`, which in Mathlib 4.35 has no
finiteness hypotheses). Hence `isDeRhamTensorOver_iff : IsDeRhamTensorOver p ρ ↔ finrank F' (ddrF p ρ) =
finrank ℚ_p W` (cancel `[F:ℚ_p] > 0`), which gives both directions between the old field and the new leaf.

| declaration | statement |
|---|---|
| `exists_iotaPlusF`, `iotaPlusF`, `thetaAlg_iotaPlusF` | `F' → B_dR^+` with `θ⁺ ∘ ι = (F' ⊆ ℂ_p)` |
| `iotaPlusF_unique` | uniqueness of that lift |
| `gfToGqp_fix`, `cpAct_iotaCp_gf` | `G_F` fixes `F' ⊆ ℚ̄_p` and its image in `ℂ_p` |
| `bdrPlusMap_iotaPlusF`, `bdrAct_iotaF` | `G_F` fixes `ι(F')` in `B_dR^+` and `B_dR` (Hensel naturality) |
| `iotaF`, `algF`, `towerF` | `F' → B_dR`, `B_dR` an `F'`-algebra, `ℚ_p → F' → B_dR` a scalar tower |
| `map_smulF`, `ddrF`, `restrictScalars_ddrF` | `D_dR` as an `F'`-subspace |
| `finrank_ddrTensorOver`, `isDeRhamTensorOver_iff` | the translation |
| `deRhamVpAbVarPrinted_of_direct`, `direct_of_deRhamVpAbVarPrinted` | old field ⇔ new leaf |

## 4. Compile log (VERIFIED, 2026-11-17, Lean 4.35.0 / Mathlib v4.35.0)

| check | outcome |
|---|---|
| `lake env lean scratch/derham-direct/DeRhamDirect.lean` | no errors or warnings; `#print axioms` of `deRhamVpAbVarPrinted_of_direct`, `direct_of_deRhamVpAbVarPrinted`, `iotaPlusF_unique`: `[propext, Classical.choice, Quot.sound]` |
| `lake build ZInQKernel.Contrib.OneProof.DeRhamPrintDirect` | built |
| `scratch/derham-direct/Discharges.lean` (`#discharges`) | `DISCHARGES [OpenResearchLeaves40.deRhamVpAbVarPrinted] by DeRhamPrint.Direct.deRhamVpAbVarPrinted_of_direct`, still assumes `[DeRhamPrint.Direct.DeRhamVpAbVarDirect]`, standard axioms |
| `python3 scripts/one_proof/autofold.py scratch/derham-direct/autofold.json --dry-run`, line 1 stripped → `FoldDryRun.lean.txt`, `lake env lean` | `strict count: 16/15 on 31 -> 17/14 on 31; strictest 16/15 -> 17/14`; `HDec.HSyn.sixContactMin_of_open59` compiles, standard axioms |
| rebuild after the docstring edit of `DeRhamPrint.lean` | see §6 |

**Autofold spec**: discharges `deRhamVpAbVarPrinted` with
`_root_.DeRhamPrint.Direct.deRhamVpAbVarPrinted_of_direct {n}.deRhamVpAbVarDirect`, one leaf
`deRhamVpAbVarDirect : _root_.DeRhamPrint.Direct.DeRhamVpAbVarDirect`, kind published, flag "pending review: direct
instance of Berger II.5.1 p. 19 (...)". Autofold rates a published leaf LEAF unless its flag starts with "pending
reading", so the fold counts it LEAF (GLUE 15 → 14), as the integrator's ruling says; if the integrator wants it
counted GLUE until the review, the kinds row needs strict = GLUE by hand (as for the old row). The fold itself (no
`--dry-run`, build, hash guard, OpenStatements, render_open) is the integrator's.

## 5. Locator

The old docstring (`DeRhamPrint.lean`, the `DeRhamVpAbVarPrinted` docstring) said Berger "§I.3"; changed to
"§II.5.1, p. 19" per the relayed reading, with a note that h-leaves §3.2 recorded the same wording under "§I.3". I
could not read Berger here (no network, no local copy), so the locator is the integrator's reading, UNVERIFIED by
this task; the two section numbers may be the arXiv and the published numbering of the same passage
(SPECULATIVE). Not touched: `BdRInvariantsPrinted` (bdr-inv's target), and TailS.lean's untwisted `H¹` form
(`DeRhamH1AbVarT`, TailS.lean:1986-1990), for which Berger is not cited.

## 6. Status

* Done: (1) `F'`-structure on `D_dR` and the leaf restated as the print; (2) the old field proved from it (and the
  converse); autofold spec and dry run; locator fix.
* Remaining: a reviewer's confirmation of the reading (flag "pending review"); the fold itself (integrator).
