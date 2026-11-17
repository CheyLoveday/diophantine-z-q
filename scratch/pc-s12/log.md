# pc-s12 results log (round 2 of fork issue #83)

## 2026-11-17 start
- Round-1 uncommitted change to ZInQKernel/Contrib/PoleRC/Count.lean (eqs_of_localBad takes the class
  hypothesis `hcls`; new `NecAt ℓ` = the "only if" halves at every SelM class; `necAt_of_local`;
  `sel_necessary`/`sel_injOn` take `NecAt`): it did NOT compile (unknown `hN` in
  `dimThreeCount_of_local`). FINISHED: added `have hN := necAt_of_local ...`. `lake build
  ZInQKernel.Contrib.PoleRC.Count ZInQKernel.Contrib.OneProof.PoleCompletenessFromRC` OK. COMMITTED.
