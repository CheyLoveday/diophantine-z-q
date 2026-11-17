# fold-b105 log

Base wip/leaf-fold33b d67ea55f (H top `HDec.HSyn.sixContactMin_of_open67`, TailZ74, `OpenResearchLeaves48`;
render_open: 36 open, H 31, strictest 4/27). Build tree: `.lake/build` and `lean/.lake/build` copied (reflink) from
~/dzq-wt/leaf-fold33b (74395dcf, same Lean sources as d67ea55f, Main.olean of 05:45).
Hash dumps (`DumpCompact.lean`, ~1.7 MB each) are kept out of the commit; the comparisons are `cmp_fold<k>.txt`.

## Fold 1: chevalleyPerfect removed (fold-chev regenerated on the coeff-field-tc copy chain)

1. fold-chev's `gen_bypass.py` stops at `sixContactMin_of_open67` (a let-bound multi-line step whose research
   argument is a nested composite of 16 CF conversions). New generator `scratch/fold-b105/gen_chev_bypass.py` (fold-chev's
   helpers verbatim; new walk): each step may have `let` lines; the nested research argument is applied innermost first
   and the walk stops at the first conversion whose result has no `chevalleyPerfect`; the outer conversions and the final
   call are re-emitted (lets kept). Dry run (VERIFIED): walk `openResearchLeaves46_of_OpenResearchLeaves47_cf -> ... ->
   openResearchLeaves36_of_OpenResearchLeaves37_eb_cf` (11 conversions), stop bundle `OpenResearchLeaves36EBCF` (25
   fields); readers bostLowerBound, gaudronRemondThm14 (both in the CF copy of 37->36) and javanpeykarBound (38->37)
   rerouted to `ZInQ.ChevFree.*_of_printed_free` / `semiAbelianDescendsPerfect_proof`. `OpenResearchLeaves48` (29
   fields) -> `OpenResearchLeaves49` (28). kinds count strict 4/27 on 31 -> 4/26 on 30, strictest 4/27 -> 4/26.
   claims.tsv has no chevalleyPerfect row.
2. `python3 scratch/fold-b105/gen_chev_bypass.py` -> `ZInQKernel/OneProof/H/TailZ75.lean` (copy `TailZ75.lean.txt`):
   `OpenResearchLeaves49`, `openResearchLeaves36EBCF_of_OpenResearchLeaves49 (n) (t : OpenTextbookLeaves18)`,
   `sixContactMin_of_open68` (lets t16, l26; then `sixContactMin_of_open48_eb_k954` through the five CF conversions
   36EBCF -> 31EB). Main switched (import, bundle, top, docstring paragraph); kinds row chevalleyPerfect dropped.
3. Build (VERIFIED): `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges` ok (16217 jobs);
   `sixContactMin_of_open68` and `ZInQ.OneProof.frozenTarget`: [propext, Classical.choice, Quot.sound].
4. Hash guard (VERIFIED, `cmp_fold1.txt`): base dump (run against leaf-fold33b's base oleans) 17984 constants, after 18020;
   only before 0; only after 36, all in `ZInQKernel.OneProof.H.TailZ75`; changed 1: `ZInQ.OneProof.frozenTarget`.
5. Closure (VERIFIED, `FoldCheck-fold1.txt`): closure of frozenTarget 304702 constants; no sorryAx, no
   `ChevalleyPerfect`, `semiAbelianDescendsPerfect_of_chevalley`, `*_of_printed_chevalley`, `OpenResearchLeaves48`,
   `sixContactMin_of_open67`; contains `ZInQ.ChevFree.semiAbelianDescendsPerfect_proof`.
6. OpenStatements: 35 open hypotheses (was 36). render_open: 30 H hypotheses, strictest 4/26, 5 others; `--check` ok.
   DischargesTest rerun (`scratch/contrib-kit/DischargesTest-output.txt`; diff: only `OpenResearchLeaves48` -> `49`
   labels). render_open rerun, `--check` ok. frontier_crosswalk: 232 IDs, 4 matched; `--check` ok.
   autoform check: exit 0, "OK: 776 articles, 2337 dependencies; 701 fully proved" (`autoform-check-fold1.txt`).
   `#discharges` does not list chevalleyPerfect: bypass (no proof of `ChevalleyPerfect`), the field is no longer a
   hypothesis. New statements: none (the new bundle is the old one minus the field).
   **render_open count after fold 1: 35 open (H 30, strictest 4/26).**
