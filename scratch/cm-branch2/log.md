# cm-branch2 results log

- 2026-11-17 08:13 start; base origin/wip/cm-branch 42d874ac; merged origin/main (b1615c9b, top now HDec.HSyn.sixContactMin_of_open72, TailZ79, OpenResearchLeaves53; OpenTextbookLeaves18 is empty) -> 00a966c9.
- 08:20 lake build Main + Discharges + CMBranch.Top started (build1.log).
- FINDING (VERIFIED by reading the tree): HeightAdditivityUpper is provable from proved tree pieces plus the chain's textbook field t35 (UniformizationExists):
  ProductMetrizationGeo (TailB) <- ProductLocalStructure (Metrization2.productLocalStructure, proved) + ProductHodgeLattice (UnifDims.productHodgeLattice_of_cotangent productCotangent tangentDimAtOrigin_proved3 t35);
  the reduction productMetrizationGeo_of_local is in scratch/metrization/part_produnif2.lean (not copied into the tree);
  MetrizationBaseChange <- G0StableBC.metrizationBaseChange_of_hodgeLine (HodgeLineBaseChange proved in the chain, Open4.lean hBC);
  ProductGroupModelExists proved (H5Neron/H5Glue.productGroupModelExists).
