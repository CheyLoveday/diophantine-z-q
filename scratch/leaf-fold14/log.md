# leaf-fold14 results log

- 11-14 18:53 start. Base 29885092 (leaf-fold13). Merged origin/wip/reduct-b 85495b37, origin/wip/unipotent-b 24c44f3d,
  origin/wip/t09-pic 3d0f47a8 (new files only, no conflicts).
- Plan: TailZ23 = ReductB body + OpenResearchLeaves14 + sixContactMin_of_open17 (reduct fold);
  TailZ24 = T09Pic + OpenAddedLeaves13 + sixContactMin_of_open18 (t09-pic fold).
- Finding: SemistablePersistsSHcp cannot give the general field `semistablePersistsDVR` (imperfect residue fields), so
  the reduct fold cannot map to OpenResearchLeaves13; it maps to OpenResearchLeaves9 (TailZ9, the newest generation
  whose bundle has SS1/SS3 as fields instead) and calls sixContactMin_of_open11, composing the intermediate maps
  (TailZ15, Z17, Z18, Z19, Z22) by hand with SS1/SS3 from ReductB.ss1_ss3_of_cp.
- unipotent-b: both routes need StrictHenselizationInside (not in the bundles, not derivable from
  StrictHenselizationPair; a composite like the pair, strict GLUE). Gen route: -1 GLUE +2 GLUE (descends, inside);
  geometric route: -1 GLUE +1 GLUE (inside) + PrintedGeom (pending reading). Neither lowers the strict count: not taken.
- 11-14 19:08 TailZ23 (reduct fold) compiles (lake build, ~15 s); Main switched to sixContactMin_of_open17;
  frozenTarget axioms [propext, Classical.choice, Quot.sound] (VERIFIED). kinds.tsv: 3 rows removed, 3 added.
  Count after fold 1: strict 49/16 (was 47/18, GLUE -2), strictest 47/18 (was 46/19; raynaudSemistableSH flagged
  GLUE at the strictest reading). claims.tsv: the three reduct-b claim rows of the removed fields deleted
  (render_open.py exits otherwise). JSON + OPEN.md regenerated.
- 11-14 19:12 TailZ24 (t09-pic fold) compiles (~25 s); Main switched to sixContactMin_of_open18; frozenTarget axioms
  standard (VERIFIED). kinds.tsv: t09SymmIsogenyExists removed, four t09-pic leaves added (weilPairingMumford flagged
  composite at the strictest reading). Count after fold 2: 68 fields, strict 53/15 (GLUE -1), strictest 50/18.
  claims.tsv: t09-pic's claim row of the removed field deleted. JSON + OPEN.md regenerated.
