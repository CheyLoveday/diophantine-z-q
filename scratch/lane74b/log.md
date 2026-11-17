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

## Item 1: autofold + gate

- Current Main (f558b164) already has the shape autofold.py:68 needs: `theorem _root_.ZInQ.OneProof.frozenTarget`,
  binders, `(hPC : ZInQ.PoleCompleteness) :` newline `ZInQ.FrozenTarget`, the call
  `(HDec.HSyn.sixContactMin_of_open72 r t l) hPC`, imports TailZ79 + MainGreenTao + DeRhamRange (no binder comments).
  `main_state()` parses it: binders r/t/l, top sixContactMin_of_open72, last module TailZ79. VERIFIED (python).
- autofold.py change: `main_state(s=None)` parses a text too (docstring states the required shape); after switching
  Main, autofold re-parses the switched text and dies unless the top theorem is `sixContactMin_of_open{N+1}`, the
  TailZ import is the new module, the other imports (MainGreenTao, DeRhamRange) are unchanged and the binder names /
  bundles are the old ones with the bumped generations. Before, a failed `str.replace` would have written an
  unchanged or half-switched Main silently. `--dry-run` stdout unchanged (count line + module); the switched Main
  goes to stderr.
- Dry runs: no-op spec (scratch/lane74b/gate-noop-spec.json, no discharge): EXIT 0, prints
  `sixContactMin_of_open73 r t l := sixContactMin_of_open72 r t l` over TailZ79; switched Main imports TailZ80,
  MainGreenTao, DeRhamRange, calls `(HDec.HSyn.sixContactMin_of_open73 r t l) hPC`. One-field spec (discharge
  `picRepresentableAbVar` of OpenAddedLeaves27, proof a dummy name, not compiled): EXIT 0, OpenAddedLeaves28,
  switched Main binder `(l : HDec.HSyn.OpenAddedLeaves28)`, `hPC` kept. Tree unchanged after both. VERIFIED.
- Gate script for the lead: scratch/lane74/gate.sh (the chain scripts are outside the repository): no-op dry run,
  tree-unchanged check, compile of the printed fold module, axioms of sixContactMin_of_open73 standard; prints GATE=ok.

## Item 3: Pole.lean

- Pole.lean at f558b164 already had lane74's manuscript body with rewritten docstrings (no "x + ℓ" / "PC is a theorem
  from CR₃" left; those were in the Route K version d61c9c41, which is also the hash upstream's contract pins at
  9c7b60ef). Item 3 done literally: Pole.lean reverted byte for byte, docstrings with body, to b570b14ee
  (= the kernel skeleton cb193ab1b's file, blob 842f08ae). Only docstrings differ from f558b164 (no declaration
  changes). VERIFIED (git hash-object = 842f08ae).
- Upstream contract: the pinned blob of ZInQKernel/Hypotheses/Pole.lean at 9c7b60ef is d61c9c41 (Route K polynomial);
  any manuscript-polynomial Pole.lean differs from it, so the file needs a contract waiver upstream either way
  (FINDING for the lead).
- Remaining Route K wording about PC outside Pole*.lean: ZInQKernel/Hypotheses/CertifiedRank.lean:10 names
  `ZInQ.poleCompleteness_of_certifiedRank` (deleted); CertifiedRank.lean is one of the kept H-reach files (item 7).
- Build after the revert: `lake build ZInQKernel +OneProof.Main +OneProof.Discharges` OK, 16053 jobs (first run stopped
  by the harness's 10-min background limit after ~150 modules, rerun completed: 227 rebuilt, 19m39); frozenTarget
  axioms [propext, Classical.choice, Quot.sound]. VERIFIED (scratch/lane74b/build1b.txt).
- Hash dump f558b164 vs lane74b-after (every ZInQKernel constant of ZInQKernel + OneProof.Main): 179119 = 179119,
  0 changed, 0 removed, 0 added (docstring-only revert). VERIFIED (scratch/lane74b/hashcmp-f558-after.txt).
