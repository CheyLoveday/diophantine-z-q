# cm-branch2 (2026-11-17) — interim

**Result.** CM-branch fold on the current top (open72) compiles with standard axioms:
`HDec.HSyn.sixContactMin_of_open72_cmbranch2 (r t l) (c : CMBranch.CMInputs2) : SixContactMin`
(`ZInQKernel/Contrib/OneProof/CMBranch2.lean`). Net GLUE column 0: +CMFibreSplit, −gonzalezRotgerThm512X6RCF (now carried
but unread: PruneScan target); +5 leaves pending review (FowlerProp27 printed; CMHeight62, CMjDegree, CMPotentialGood,
CoxProperLattice consequence).

* HeightAdditivityUpper PROVED from the textbook field t35 (CMBranch/HeightAdd.lean).
* ReducedCMPeriod PROVED from t35, homLatticeCorr, t11b and the new textbook leaf CoxProperLattice (CMPeriodLattice proved,
  reduced basis via Mathlib's ModularGroup.fd, Im bound) (CMBranch/PeriodLattice.lean, ReducedPeriod.lean).
* R5ptProps pruned: CMBranch/R5Prune.lean (generated, 6282 lines, R5ptProps := True) compiles ⇒ no consumer reads it;
  closure scan: R5ptProps absent, GR read nowhere (scratch/cm-branch2/gruse-out.txt).
* CMFibreSplit stays GLUE (A8 at CM fibres + matrix units; decomposition in the report §2.3).
* X6 rows stay (read: X6Props, R2X6Props, CMExists, X6Surj); Y3 re-source scoped in report §5.

Report: docs/research/cm-branch2.md. Autofold spec: scratch/cm-branch2/autofold.json. #discharges: scratch/cm-branch2/discharges.txt.
