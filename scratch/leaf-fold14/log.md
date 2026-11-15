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
