# cm-fold-rebase results log

- 13:17 start. Base 6298e108 (cox-lattice). Merged origin/main 67950e829 (fold-b112 + hygiene; top
  sixContactMin_of_open76, TailZ83, OpenResearchLeaves57) with merge commit d28bdc4e, clean.
- Main's count (docs/one-proof/OPEN.md, kinds.tsv): 29 H rows (27 research + 2 added), strict 5 LEAF / 24 GLUE on 29
  (+ hPC outside H). VERIFIED (read).
- Finding: main's TailZ80 (bost-gr9) is a copy-based reroute: the bundles OpenResearchLeaves53..8EB and the chain
  open8..open72 are copied into HDec.HSyn.GR9 with bostLowerBoundAnSS weakened; open73 = GR9.open72. So cm-branch2's
  R5Prune chain (over the un-weakened bundles, needing bostLowerBoundAnSS) cannot be fed from OpenResearchLeaves57.
  Plan: thread c through GR9.open48 -> GR9.open8 -> (Top2) open7_cm2; dirty-scan that root; copy only the dirty
  declarations not already copied by cm-branch2's R5Prune (reuse its _r5 copies); new generation
  OpenResearchLeaves58CM = 57 - gonzalezRotgerThm512X6RCF + 5 CM fields, conversions 58CM->56_cm->55_cm->54_cm->
  GR9.36EBCF_cm->GR9.35EBCF_cm->GR9.34EBCF_r5 (verbatim copies minus the GR line).
