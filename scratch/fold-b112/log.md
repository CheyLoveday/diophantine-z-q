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
