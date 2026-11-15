# leaf-fold14 (done)

**Result.** `ZInQ.OneProof.frozenTarget` now goes through `HDec.HSyn.sixContactMin_of_open18` (new modules
`OneProof/H/TailZ23.lean`, 48 KB, and `TailZ24.lean`, 51 KB) with bundles `OpenResearchLeaves14` (35),
`OpenTextbookLeaves10` (15), `OpenAddedLeaves13` (17), `OpenGlue7` (1): 68 fields, strict LEAF/GLUE **53/15** (was
47/18), strictest 50/18 (was 46/19). Standard axioms only (VERIFIED).

- **Fold 1, reduct (reduct-b):** `semistableReductionDVR` (K1), `raynaudSemistable` and `semistablePersistsDVR` (all
  GLUE) replaced by `raynaudSemistableSH` (unrestricted; LEAF, GLUE at the strictest reading),
  `semistablePersistsSHcp` (LEAF) and `strictHenselizationPair` (GLUE). Strict 49/16. The restricted 3.3a leaf cannot
  give the general field, so the new bundle maps to leaf-fold9's `OpenResearchLeaves9` (SS1/SS3 by
  `ReductB.ss1_ss3_of_cp`), composing the intermediate maps by hand; `sixContactMin_of_open17` calls
  `sixContactMin_of_open11`.
- **unipotent-b not taken:** both routes need `StrictHenselizationInside` (not in the bundles, not derivable from the
  pair), so neither lowers the strict count.
- **Fold 2, t09-pic:** `t09SymmIsogenyExists` (GLUE) replaced by the four printed leaves `picRepresentableAbVar`,
  `picZeroAbVar`, `phiAmpleIsogeny`, `weilPairingMumford` (single L4; GLUE at the strictest reading). Strict 53/15.

**Checks (VERIFIED).** `lake build +ZInQKernel.OneProof.Main` passes; hash guard: 0 deleted, 0 changed, 189 new
constants (TailZ23, TailZ24, frozenTarget); OpenStatements + `render_open.py --check` ok; OPEN.md and
open-statements.json regenerated. kinds.tsv: 4 rows removed, 7 added (all "pending review"). claims.tsv: the 4 claim
rows of removed fields deleted (needed for render_open.py).

**Remains.** Reviews of the seven new rows (SGA 7 IX base and residue-field reading for 4.7; t09-pic's L1-L4
locators); unipotent-b's `SemiAbelianDescendsSepClosed` and `StrictHenselizationInside`; the uses check shows only
closure membership, not live paths. Report: docs/research/leaf-fold14.md.
