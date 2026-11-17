# lane74 results log

Base: wip/leaf-fold33b 74395dcf0. Build tree copied (reflink) from ~/dzq-check2 at 74395dcf (warm).
Issues #74/#76-#79 not readable (gh: connection reset; no network). Worked from the brief.

## #77 (commit 1)

- Tag: `git tag route-k-final bf691da2236b494bb429caabc2f907d4ea428c4d` (SHA from
  `grep LANDED ~/dzq-runs/landed.txt | tail -1 | cut -d' ' -f1`). Local tag created; push failed
  (CONNECT tunnel 403), not retried; command in scratch/lane74/TAG.md. VERIFIED.
- Import graph: scratch/lane74/graph.py (imports of all 7145 tracked ZInQKernel .lean files) and
  delset.py (named set + forced closure). H-reach = transitive imports of OneProof/H/** and
  HDecomp/** (1790 modules).
- Named set (RouteK/**, Contrib/{TYZChain,TYZDecomp,TYZGenus,GZDecomp,GZStatements,GZTheta,HeckeFE},
  MainLiterature, Hypotheses/{CertifiedRank,CR3Literature,TYZInputs}, OneProof/{TYZSplit,TopChain},
  the Contrib/OneProof files in the import closure of OneProof/Main's TYZ/GZ imports and not in
  H-reach) plus forced importers (GaussFE/Headline, PSide/* except TYZInputsIff, three NonVacuous /
  OptimalUnique files, TYZGenusFold/QI, TYZSquareOddness, TYZThm21PairsOne): 298 modules.
- FINDING (importer check): 78 of them are in H-reach and were NOT deleted
  (scratch/lane74/kept-h-reach.txt, 27831 lines). Single entry point:
  OneProof/H/TailZ34 imports Contrib/OneProof/RayClassShimura, which imports
  Contrib/TYZGenus/ShimuraModFn (RingClassLattice, also in H-reach, imports TYZGenus.ShimuraModFn and
  ShimuraMain). From there: TYZGenus.{ShimuraField,ShimuraZn,ShimuraRecip,RingClassBridge,Package}
  -> TYZDecomp.Leaves -> HeckeAll.Provider -> {GaussFE.FunctionalEquation5, HeckeAll.Continuation}
  -> HeckeFE.Basic -> {RouteK.Rank.LFunctionCd, Hypotheses.CR3Literature}; TYZDecomp.Leaves ->
  PSide.TYZInputsIff -> RouteK.PropN; TYZGenus.RingClass -> RouteK.Rank5b.Sec3.RedeiStatement,
  RouteK.Redei.FourRank, Hypotheses.TYZInputs; and RouteK.{Slots,System,Selmer,Assembly.Realize,...}.
  VERIFIED (BFS path printed by scratch tool).
- FINDING: Density/CharSum (Proposition D, used by the headline through MainGreenTao) imports
  RouteK/Selmer/CharSum (Mathlib-only character sums). Kept in place (not deleted).
- Deleted: 220 files, 70475 lines (scratch/lane74/deleted-files.txt). VERIFIED (git rm, wc -l).
- Root ZInQKernel.lean: 23 imports removed (deleted files and the Route K/CR3 modules kept only
  for H-reach). AllContrib.lean: 51 imports of deleted files removed.
- Main.lean: CR3 headlines removed; kept `_of_poleCompleteness` (h22); added
  `_of_poleCompleteness_goodPrimeAP`, `_of_poleCompleteness_greenTaoDense`.
  MainGreenTao.lean: `_of_poleCompleteness_goodPrimeDensity` and the headline
  `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness`.
- OneProof/Main.lean: frozenTarget (r t l) (hPC : PoleCompleteness); imports TailZ74 + MainGreenTao.
- scripts/print_axioms.lean: Route K / CR3 / literature / PropN lines removed, new headlines added.
- Builds: lake build ZInQKernel OK (9923 jobs); +OneProof.Main +Discharges + AllContrib OK;
  every tracked Contrib file OK (15533 jobs); print_axioms: 463 decls, 0 nonstandard;
  frozenTarget axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
- autoform check blueprint: OK. autoform check blueprint --lean-root .: FAILS, 199 dangling `lean:`
  names in 59 blueprint articles (main 10, rank 38, rank-5b 7, route-k 4)
  (scratch/lane74/autoform-check-leanroot-after77.txt). blueprint/ is not editable by this task:
  FINDING for #81.
- FINDING: scratch/contrib-check/Check.lean (the chain's CONTRIB-CHECK step) imports deleted modules
  (MainLiterature, GaussFE.Headline, PSide.*, GZDecomp, GZTheta, GZStatements, TYZChain.*).
