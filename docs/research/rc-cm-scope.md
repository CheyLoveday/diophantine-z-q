# CM field of definition at manuscript scope

**Verified in Lean:** the manuscript-scoped CM field statement is a restriction of the broad statement and holds for both level-one models. At general level it remains a GLUE input.

**Scope finding.** The existing Heegner anchor quantifies over every positive conductor prime to (ND_K), while tex 2841 requires it to be prime to (2ND_K). Its finite-conductor comparison and its anchor predicate both expose that broader domain. Without a proof that the actual newform level is even (or a change to the anchor predicate), the scoped CM input alone cannot be passed at all its call sites. The genus and rough-companion selectors already carry the stronger local hypotheses.

## Known issues

The anchor's wider conductor range is a Lean interface mismatch. Tex 2919 explains the condition in the cited comparison; it does not remove the separate conductor restriction at tex 2841. The prior Heegner-anchor audit also records the citation mismatch at tex 1784 and 1788; this lane does not rely on the Hecke identity there.
