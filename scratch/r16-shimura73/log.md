# r16-shimura73 results log

## Setup (06:15)
- Base bf691da22 (leaf-fold33b, top sixContactMin_of_open67, TailZ74). VERIFIED (git log).
- r16CoreY is no longer a top field: it is filled at OpenResearchLeaves41CF -> 40CF (TailZ74.lean:802) by
  `AfTateLam.r16CoreY_of_ds965 n.heckeJ1DS n.afShimura n.afCharpolyDS965 n.igusaGL2DS mumfordTorsionAlgClosed_proof`;
  top fields feeding it: heckeJ1DS, afShimura, afCharpolyDS965, igusaGL2DSGalSome (TailZ74.lean:1355
  `igusaGL2DS := igusaGL2DS_of_igusaGL2DSGalSome n.igusaGL2DSGalSome`). VERIFIED (grep).
- None of the four is read anywhere else in ZInQKernel/OneProof/ (grep of `.heckeJ1DS` etc. outside pass-through
  lines). dsThm965Printed is read by panBerger_of_printedPV (TailZ74.lean:709): it stays. VERIFIED (grep).
- r16CoreY is read only by `R16Split.r16_of_printed` (field r16). VERIFIED (grep).
- Manuscript L768-773 read (VERIFIED): Li p. 296 before Lemma 6 -> span of coefficient conjugates Fricke-stable;
  Shimura Thm 1 quotient + Euler-factor identity -> r_5 constituent of Tate module of A_f. Bibliography L11050-11057.
- locators.md row R16 (VERIFIED, read): Shimura 1973 Thm 1 pp. 526-527 gives the Q-rational quotient, coefficient
  field action, dimension; "final total Euler-factor clause has an extra Gamma0/Fricke-stability condition";
  "Individual-embedding rank-two Tate realization and Frobenius-Hecke relation must still be supplied; total
  characteristic-polynomial divisibility alone is insufficient."
