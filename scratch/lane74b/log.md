# lane74b results log

Base: wip/lane74-int f558b164 (frozenTarget (r : OpenResearchLeaves53) (t : OpenTextbookLeaves18)
(l : OpenAddedLeaves27) (hPC), via sixContactMin_of_open72, Main imports TailZ79, MainGreenTao, DeRhamRange).
Warm build copied (reflink) from ~/dzq-wt/lane74-int/.lake/build and lean/.lake/build (built at f558b164).
`lake build ZInQKernel +OneProof.Main +OneProof.Discharges`: OK, 16053 jobs (24 rebuilt), 1m45. VERIFIED.

## Item 5: blueprint (commit "lane74b item 5")

- Base `autoform check blueprint --lean-root .` (autoform-bot@46b46d6d, uvx --offline): EXIT 1, 199 errors in 59
  articles (scratch/lane74b/autoform-leanroot-base.txt). 10 of them (route-k/realization, names in namespace
  `ZInQ.RouteK.Slots`, which is also a structure) carry an extra "is a structure" message; all 199 names are
  declarations deleted by lane74 #77. VERIFIED.
- scratch/lane74b/blueprint_mark.py: per article, drop the missing names from `lean:`; if none remains (51 articles)
  drop `lean:`, `statement:`, `proof:` (page becomes unformalized); add a one-line note after the title naming the
  removal (#77), the tag `route-k-final` and #81. 8 articles keep some names (partial). Articles touched:
  scratch/lane74b/blueprint-touched.txt (59: main 10, rank 38, rank-5b 7, route-k 4). No article deleted, no link changed.
- After: `autoform check blueprint` EXIT 0; `--lean-root .` EXIT 0 (776 articles, 645 fully proved, 2328 names
  resolved); `autoform render blueprint --lean-root . --require-declarations` EXIT 0 (175 pages, 701 nodes).
  VERIFIED (scratch/lane74b/autoform-check*.txt, autoform-render.txt).
