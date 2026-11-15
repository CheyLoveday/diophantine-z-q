# flt-cqj results log

## 2026-11-15 02:55 PST — setup
- Merged origin/main (c2ad4181, w71) into wip/flt-cqj (base cdd05f1c): no conflicts (commit bf759d7c). VERIFIED.
- Source availability (VERIFIED by search): the FLT source of the bijOn proof cone is NOT on this host.
  * `find / -xdev` for `Thm_WeierstrassCurve_bijOn*`, `*cyclicQuotientJ_isRoot*`, `fermats-last-theorem*`: no hits.
  * `git log --all -S "bijOn_cyclicQuotientJ_isRoot_modularPolynomial"`: only cdd05f1c (the Bridge statement).
  * every path ever committed under any `AnthropicFLT/` directory in any ref: 389 distinct files, all in
    CloudB2X0Transitive (250 .lean) and CloudW02Connectedness (135 .lean). The cloud worker's other 411 cone modules
    (224 that built + 187 blocked) were never committed ("That work-in-progress is not committed", cdd05f1c message).
  * Network commands are forbidden by the task rules, so the upstream files (anthropics/fermats-last-theorem@6e837e75)
    cannot be obtained.
- Build tree: copied (reflink) .lake/build and lean/.lake/build from worktree h29-split (304 differing files, mostly
  the CloudB2 vendor tree).

## 03:30 — committed reduction rebuilt on the merged tree (w71)
- `lake build ZInQKernel.Contrib.CloudB2X0Transitive.Reduction`: Build completed successfully (9574 jobs), no errors
  (only linter warnings). VERIFIED. So the 250 vendored FLT modules, Bridge.lean and
  `x0Transitive_of_cyclicQuotientJBijOn : CyclicQuotientJBijOn → ZInQ.RLeaf.X0Transitive` compile on fork main w71.
- Finding (VERIFIED by `git grep`): there is no route X0Transitive → IgusaGL2 in the tree, and none can exist in
  general (IgusaGL2 is the full GL₂ image; X0Transitive is transitivity on cyclic subgroups). The existing route is
  the converse, `CurveSplit.x0Transitive_of_igusaGL2` (TailR.lean:1592), used once, in
  `textbookLeaves6_of_open7` (TailX.lean:239, field `x0Transitive` of `OpenTextbookLeaves6`). Generations 8-11
  only copy `igusaGL2` through. So an autofold discharge of `igusaGL2` (proof of type `ZInQ.RLeaf.IgusaGL2`)
  cannot be built from CyclicQuotientJBijOn; a bypass fold (field replaced by a weaker leaf) is needed.
