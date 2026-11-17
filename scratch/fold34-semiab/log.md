# fold34-semiab log

Base: wip/leaf-fold33b c0f3d085 (= origin/main; top `sixContactMin_of_open48`, TailZ55; render_open: 35 open, 29 H,
strictest 11/18, 6 others).

1. Merged wip/height-fix (49e6d97d; brings height-dict) and wip/semiab-descend (6a6de248): both clean.
   Hygiene: five scratch files redeclaring HDec.HSyn bundles renamed .lean.txt (height-dict FoldDryRun,
   FoldDryRunAll4; height-fix FoldDryRun; semiab-descend FoldDryRun, FoldDryRunCheck). No host paths in the merged
   files (grep /home/, user name). No vendored code or LICENSE/NOTICE files in either branch.
   dict-models' `ZInQKernel/Contrib/OneProof/RaynaudSemistableOr.lean` is in the base tree (VERIFIED, ls).
