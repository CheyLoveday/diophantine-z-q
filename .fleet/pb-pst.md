# pb-pst (2026-11-17)

**Result.** Three of the strict review's four objections to pb-fix3's leaves of `r11r12` are cleared by Lean
proofs, with no new hypothesis; P1 is still open.

* **V1 (Berger, also Pan): cleared.** `BmaxOne.bmaxOf_eq` / `bstOf_eq`: bst-construct's `Bmax`/`Bst` (every `log [ε]`
  inverted) equal `B_max^+[1/t]` / `B_max^+[1/t][log p̃]` for one `t = log [ε₀]`, `ε₀` any generator of `ℤ_p(1)`.
  Key: `log [ε] = a·t`, `a ∈ ℤ_p` (`logTeich_eq_mul`), from `A_max ⊆ B_dR^+` being `p`-adically separated
  (`amax_sep`).
* **V2 (Berger): cleared.** `isAdmissible_of_T`: Fontaine's admissibility in basis form (`B ⊗ V` has an invariant
  `B`-basis) implies the dimension form for any `G`-stable `B ⊆ B_dR`. The new leaf `BergerPrintedVT` (one `t`,
  basis form) proves the old `BergerPrintedV` (`bergerPrintedV_of_T`); `FontaineBstInvariants` is off the route.
* **P2 (Pan): cleared.** `HTFinite.finiteDimensional_htSpaceE`, `htMultE_le` (`dim_E (V ⊗ ℂ_p(w))^G ≤ n`), by Galois
  descent from `axSenTate_proof`.
* **P1 (Pan): open.** Pan's pst is Fontaine's (`B_cris`-based); the leaf uses the `B_max`-based ring. It needs a
  `B_max`/`B_cris` comparison (Frobenius, `A_cris → B_dR^+`), not attempted. `PanPrintedPt`
  (`panPrintedP_of_t`) restates Pan over the one-`t` ring; it is a drop-in, but stays GLUE.

**Compiles (VERIFIED).** `ZInQKernel/Contrib/OneProof/PanBergerPst.lean` builds together with Main and Discharges.
All 15 checked declarations use only the standard axioms. `#discharges` lists `bergerPrintedV` (by
`bergerPrintedV_of_T`) and `panPrintedP` (by `panPrintedP_of_t`). The autofold spec `scratch/pb-pst/autofold.json`
replaces `bergerPrintedV` with `bergerPrintedVT`; its dry run gives strict 12/22 → 13/21 and strictest 11/23 → 12/22
(**GLUE −1**, against a target of −2). The dry-run module compiles, and `sixContactMin_of_open61` uses only the
standard axioms.

**Ratings.** `bergerPrintedVT`: printed form (LEAF, unread flags: Springer pagination, Berger §1.2 wording,
Fontaine Exp. III numbering). `panPrintedPt`: consequence (GLUE) until P1 is cleared.

Report: `docs/research/pb-pst.md`; log: `scratch/pb-pst/log.md`.
