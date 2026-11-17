# bost-gr9 results log

## 2026-11-17 setup
- Base d67ea55f6 (= wip/leaf-fold33b top); origin/main is an ancestor (VERIFIED, git merge-base).
- Network: WebFetch of lmbp.uca.fr/~gaudron/art13.pdf and arxiv.org refused by sandbox (VERIFIED). GR14 §9 not
  read by this task; its content is taken from the locator audit (docs/research/locators.md row R21, AUDIT-READ):
  GR14 §9, proof of Lemme 9.1, p. 2098 uses h_F(A) >= -(3/2) dim A, referring to Bost and GR (CMH 2014) Cor. 8.4,
  with a normalization warning (content of the warning not recorded by the audit).
- Title per manuscript bibitem L11063-11066 and locators R19: "Polarisations et isogénies", Duke 163 (2014)
  2057-2108 (VERIFIED as recorded in the tree; not re-read in the print).

## Finding 1 (VERIFIED by arithmetic, compiled below)
- Consumer field ZInQ.R3Residual.BostLowerBoundAn: -(g/2)log(2π) <= x + (g/2)log π, i.e. x >= -(g/2)log(2π²)
  = -1.4913 g. GR14 §9's printed form: x >= -(3/2) g. The field is STRICTLY STRONGER than the cited print
  (1/2 log(2π²) < 3/2), so bostLowerBoundAn cannot be proved from a GR §9 leaf.
- The downstream need: R21_Bost (-(3/2) g <= stableFaltingsHeight), consumed via HeightSplit.r21_of_leaves' in
  heightRowsNo20_of8_hf_eb (EichlerBoundCopy.lean:470). TailY already has HeightSplit.GRBostBound (GR §9 form).
- Chain of the field in the bundles: bostLowerBoundAn (OpenResearchLeaves43CF..48, TailZ68-74) ->
  bostLowerBoundPrinted (TailZ74:990) -> HeightSplit.BostLowerBound (TailZ74:465, chevalley) -> R21
  (EichlerBoundCopy:482, OpenResearchLeaves8EB).
