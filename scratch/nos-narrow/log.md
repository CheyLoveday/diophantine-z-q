# NOS narrowing results

- **VERIFIED:** Merged only `origin/wip/nos-proof` at `e9828e923` into the specified base `be73b91c5`. Archived its old dry run as `scratch/nos-proof/AutofoldDry.lean.txt`.
- **VERIFIED:** `ZInQKernel/Contrib/OneProof/NeronOggShafarevich.lean` compiled unchanged with Lean 4.35.0. The copied cache was missing dependencies; built the required modules serially, then compiled the contribution. See `proof-build.txt`.
- **VERIFIED (C8 checkpoint):** The closure of `HDec.HSyn.sixContactMin_of_open79_hm` contains 129,868 constants after skipping external module bodies. Both NOS paths read only the forward implication. All six tested converse declarations are absent. `uses-c8.txt` records the run; it used `Uses.lean` with the import and root switched from Main to C8Chain and `sixContactMin_of_open79_hm`.
