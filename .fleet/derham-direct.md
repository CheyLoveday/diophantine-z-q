# derham-direct (2026-11-17)

**Result.** The research field `deRhamVpAbVarPrinted` (`DeRhamPrint.DeRhamVpAbVarPrinted`, GLUE, pending review) is
proved from a new leaf `DeRhamPrint.Direct.DeRhamVpAbVarDirect` stating the print's form, and the two are
equivalent (proved both ways, standard axioms). The new leaf: for `A` over a finite `F/ℚ_p`,
`dim_{F'} D_dR(V_p A) = dim_{ℚ_p} V_p A`, where `F' = fieldF p F ⊆ ℚ̄_p` (the print's `K`: `G_F` acts through
`gfToGqp`, image `G_{F'}`), `D_dR = ddrF = (B_dR ⊗ V)^{G_F}` an `F'`-space through `iotaF : F' → B_dR^+ → B_dR`.
`iotaF` is new: g9-derham's `iotaDR` needs `F` Galois; this is the Hensel lift through `θ⁺` for any finite `F`,
proved unique (`iotaPlusF_unique`) and `G_F`-invariant (`bdrAct_iotaF`). The translation is the tower law
(`finrank_ddrTensorOver`). Source: Berger 2004 (arXiv math/0210184v1) §II.5.1 p. 19, attributing it to Fontaine
(locator as relayed by the integrator; not read here, no network; h-leaves recorded "§I.3" for the same wording).

**Compiles.** `ZInQKernel/Contrib/OneProof/DeRhamPrintDirect.lean` (new; scratch copy
`scratch/derham-direct/DeRhamDirect.lean`); `#discharges` shows the field discharged, still assuming only the new
leaf; autofold dry run (`scratch/derham-direct/autofold.json`): strict 16/15 → 17/14 on 31, the fold module
(`FoldDryRun.lean.txt`) compiles, `sixContactMin_of_open59` standard axioms. Locator fixed in the old docstring
(`DeRhamPrint.lean`, docstring only; `BdRInvariantsPrinted` untouched).

**Remains.** Reviewer confirmation of the reading (leaf flagged "pending review"; autofold counts it LEAF per the
integrator's ruling); the fold itself. Report: `docs/research/derham-direct.md`.
