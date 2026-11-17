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
