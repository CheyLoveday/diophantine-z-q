# fold-b112 log

Base wip/leaf-fold33b d435851d (fork main after lane74; H top `HDec.HSyn.sixContactMin_of_open72`, TailZ79,
`OpenResearchLeaves53`). Build tree `.lake/build` and `lean/.lake/build` copied (reflink) from ~/dzq-wt/lane74
(same commit d435851d, Main.olean of 11-17 10:21).

## 0. Base checks (VERIFIED, 11-17 11:25)
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges`: ok (15975 jobs, replayed); frozenTarget
  [propext, Classical.choice, Quot.sound].
- `bash scratch/lane74/gate.sh`: GATE=ok. `render_open.py --check`: ok, 30 open hypotheses.
- **render_open count at base: 30 open (H 29, strictest 5/24, 1 other).**
- Base hash dump (DumpCompact): 18023 constants (/tmp/fb112/hashes_fold0.txt, not committed).

## Fold 1: bost-gr9 (bostLowerBoundAnSS -> gaudronRemondSec9LowerAnSS; weaker-leaf bypass, count-neutral)

1. Merged origin/wip/bost-gr9 47a34056 (no conflicts; commit af7daff8). Hygiene: `scratch/bost-gr9/GR9Bypass.lean`
   (redeclares HDec.HSyn bundles under HDec.HSyn.GR9) renamed `.lean.txt`; no host paths; no vendored code; no build logs
   on the branch.
2. Finding (base drift): bost-gr9 was written on d67ea55f, where the field was `bostLowerBoundAn`. On this base the field is
   `bostLowerBoundAnSS` (semistab-assembly, fold-b105 fold 2: Bost over `IsAnStableHeightSS`, printed semistability).
   bost-gr9's leaf `GaudronRemondSec9LowerAn` is over `IsAnStableHeight` (`IsSemistableRes`). To keep the printed
   semistability of the sibling rows, new Contrib file `ZInQKernel/Contrib/OneProof/GaudronRemondSection9SS.lean`
   (commit separate from the fold): `ZInQ.BostGR9.GaudronRemondSec9LowerAnSS` (bost-gr9's leaf verbatim with
   `IsAnStableHeight` -> `IsAnStableHeightSS`, as semistab-assembly did for Bost and GR Thm 1.4),
   `gaudronRemondSec9LowerAn_of_ss` (SS leaf => bost-gr9's leaf) and `gaudronRemondSec9LowerAnSS_of_bostLowerBoundAnSS`
   (the replaced field implies the new leaf: never stronger). VERIFIED: builds, the three `#print axioms`
   (`scratch/fold-b112/AxiomsGR9SS.lean`, with `r21_of_sec9An`) are [propext, Classical.choice, Quot.sound].
   Not an on-the-spot statement: it is GR14 section 9 (manuscript bibitem gr2014, cited L894-895) over the printed
   semistability.
3. Closure on this head (`scratch/fold-b112/GR9Closure.lean`, bost-gr9's metaprogram with root `sixContactMin_of_open72`,
   import TailZ79, field forms + `BostLowerBoundAnSS`; 2 min 23 s): 119 affected structures, 90 declarations
   (`gr9-closure.tsv`): TailZ79 3 (`OpenResearchLeaves53`, its conversion to `OpenResearchLeaves36EBCF`,
   `sixContactMin_of_open72`), TailZ74 10 (36EBCF..32EBCF and conversions down to 31), TailZ69 1
   (`sixContactMin_of_open48_eb_k954`), EichlerBoundCopy 76 (identical to bost-gr9's EichlerBoundCopy list, VERIFIED by diff).
4. Generator `scratch/fold-b112/gen_gr9_fold.py` (bost-gr9's gen_bypass.py, regenerated): copies the 89 non-top
   declarations into `HDec.HSyn.GR9` with field types weakened (`HeightSplit.BostLowerBound` -> `GRBostBound`, etc.), the
   field renamed, the reader rewritten to `BostGR9.grBostBound_of_sec9Printed (BostGR9.sec9Printed_of_an
   (BostGR9.gaudronRemondSec9LowerAn_of_ss n.gaudronRemondSec9LowerAnSS) _) _ _ ChevFree.semiAbelianDescendsPerfect_proof`
   (in place of `ChevFree.bostLowerBound_of_printed_free (R3Residual.bostLowerBoundPrinted_of_an
   (SemistabAssembly.bostLowerBoundAn_of_ss n.bostLowerBoundAnSS) _) _ _`) and `HeightSplit.r21_of_leaves'` ->
   `BostGR9.r21_of_grBost'`; the top bundle is emitted in HDec.HSyn as `OpenResearchLeaves54` (27 fields), with the
   javanpeykarThm111An field doc's "semistable reduction as printed" phrase corrected (inbox 62; only in the new structure,
   no existing module edited). Dry run (`GR9DryRun.lean`) compiled: first attempt sorryAx (argument parser dropped a
   `.mumfordTorsionAlgClosed` projection after a parenthesis; fixed), then `sixContactMin_of_open73` standard axioms.
5. `python3 scratch/fold-b112/gen_gr9_fold.py` -> `ZInQKernel/OneProof/H/TailZ80.lean` (3057 lines), Main switched to
   `sixContactMin_of_open73` / `OpenResearchLeaves54` (docstring paragraph added); kinds row `bostLowerBoundAnSS` replaced by
   `gaudronRemondSec9LowerAnSS` (published; flag "pending reading (GR p. 2098 normalization): ... cited inside a proof
   (Lemme 9.1 ...) ... R3' ... remains a step ... provenance cited"; flag_class pending-reading; GLUE/GLUE; packet,
   label, tier, area_issue of the old row); claims.tsv had no row. Count line: strict 5/24 on 29 -> 5/24 on 29.
6. Row edits (inbox 62, 64b) in this fold: 62 (javanpeykarThm111An columns 4 and 7) VERIFIED already applied on the base
   (both replacement texts present verbatim). 64b: the phrase "Berger survey IV.5.1, cited print" is NOT in the
   bergerSurveyF row on this base (grep over docs/, scripts/, OneProof: no hit); the source column's leading survey
   citation ("Berger, An introduction ... IV.5.1 and IV.5.3, with II.2.3, ...; ") is replaced by the lead's text, with
   the survey sections used by the Lean form and the rest of the column kept (`scratch/fold-b112/row_edits_64b.py`).
   Rating unchanged (consequence, GLUE).
7. Build (VERIFIED): `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.OneProof.H.TailZ80
   ZInQKernel.Contrib.OneProof.GaudronRemondSection9SS` ok (15978 jobs); `sixContactMin_of_open73` and `frozenTarget`:
   [propext, Classical.choice, Quot.sound].
8. Checks (`run_checks.sh 1 hashes_fold0.txt`, VERIFIED): hash guard 18023 -> 18882, only before 0, only after 859 (all
   in TailZ80), changed only `ZInQ.OneProof.frozenTarget` (`cmp_fold1.txt`). Closure (`FoldCheck-fold1.txt`): 292940
   constants, no sorryAx; `BostLowerBoundAnSS`, `R3Residual.BostLowerBoundAn`, `HeightFix.BostLowerBoundPrinted`,
   `HeightSplit.BostLowerBound`, `bostLowerBoundAn_of_ss`, `ChevFree.bostLowerBound_of_printed_free`,
   `OpenResearchLeaves53`, `sixContactMin_of_open72` absent; `GaudronRemondSec9LowerAnSS`, `gaudronRemondSec9LowerAn_of_ss`,
   `sec9Printed_of_an`, `grBostBound_of_sec9Printed`, `r21_of_grBost'`, `GRBostBound`, `OpenResearchLeaves54`,
   `sixContactMin_of_open73` present. Field check: 27 vs 27 fields, only `bostLowerBoundAnSS` <-> `gaudronRemondSec9LowerAnSS`,
   no other type differs. OpenStatements: 30. render_open + `--check` ok. DischargesTest rerun (17 DISCHARGES lines).
   frontier_crosswalk 232 IDs, 4 matched; `--check` ok. autoform check exit 0 (776 articles, 645 fully proved).
   `scratch/lane74/gate.sh`: GATE=ok. `#discharges` cannot show the field (bypass; the new leaf is weaker); the closure
   check shows it gone.
   **render_open count after fold 1: 30 open (H 29, strictest 5/24, 1 other); strict 5/24 on 29 (count-neutral).**
