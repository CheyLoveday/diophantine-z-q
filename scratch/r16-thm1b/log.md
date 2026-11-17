# r16-thm1b results log (round 3 of r16-shimura73)

## Setup (13:08)
- Branch wip/r16-shimura73 at e7ac05a33 (fork main f3402e89 merged; top bundle OpenResearchLeaves57 in TailZ83,
  with fields heckeJ1DS and afShimura). VERIFIED (grep).
- Merge check: `lake build ZInQKernel.Contrib.OneProof.R16Thm1` started 13:09 (rebuilds the merged kernel).

## Drafts (13:20)
- ZInQKernel/Contrib/OneProof/R16Thm1b.lean: ShimuraThm1Af (one row: ShimuraClauses ∧ IsAfQuotient ∧ uniqueness
  up to nu-compatible iso among ShimuraClauses-triples; K_f finite), afShimura_of_thm1Af, r16CoreY_of_thm1Af.
- scratch/r16-thm1b/autofold.json: heckeJ1DS by heckeJ1DS_of_bSh (leaf bShStandardModel, flag updated per (d)),
  afShimura by afShimura_of_thm1Af (leaf shimuraThm1Af, consequence, flagged steps). shimuraQuotientIsAf dropped.

## Merge check (VERIFIED, 13:23)
- `lake build ZInQKernel.Contrib.OneProof.R16Thm1` on the merged tree (11362 jobs): success; R16ShimuraLi,
  R16CoreYDS965, R16Thm1 build (linter warnings only). Nothing broken by the merge; no fix needed.

## Lean (VERIFIED, 13:25)
- R16Thm1.lean docstrings edited (misprint location per ruling (c); xiSq a theorem step per (b); multiplicity one
  cited to Shimura 1973 p. 527 instead of DS 6.6.4 / Shimura 1971 Thm 7.14). Rebuilt: success.
- `lake build ZInQKernel.Contrib.OneProof.R16Thm1b`: success, no warnings in R16Thm1b.
- Axioms (Axioms-output.txt): afShimura_of_thm1Af, r16CoreY_of_thm1Af, heckeJ1DS_of_bSh, afShimura_of_shimura73,
  euler_of_shimura73_li, r16CoreY_of_shimura_li: [propext, Classical.choice, Quot.sound].
