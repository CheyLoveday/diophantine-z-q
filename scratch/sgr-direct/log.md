# sgr-direct results log

Base 43513d87 (leaf-fold25). Marks: VERIFIED (read/compiled/computed), STANDARD (published, reference), SPECULATIVE;
theorem numbers from memory UNVERIFIED.

## 1. Consumer map of `shimuraIntegralModelRep` (VERIFIED, read in ZInQKernel/OneProof/H)

- TailZ34 `openAddedLeaves16_of_OpenAddedLeaves17`: `shimuraGoodReductionNoGuard := SGRSplit.shimuraGoodReductionNoGuard_of_printed n.shimuraIntegralModelRep` (only use).
- TailX l.266: `shimuraGoodReduction := CurveSplitGR.shimuraGoodReduction_of_noGuard (R1R2fp_of_rep r.r1r2) _`;
  TailX l.272: `modelCoordinateResidue := MCRGlue.modelCoordinateResidue_of_quotient' g.quotientP1Coordinate`.
- TailN l.255 / TailO l.2910: `heckeVertWitness := heckeVertWitness_of_leaves5 l.shimuraGoodReduction r.r1r2 (torsionStructure_ofK5 t.t5) ..`
  (= ModelGlue.heckeVertWitness_of_curveBijIso: ShimuraGoodReduction, R1R2fp, T5, ModelCoordinateResidue, CurveBijIso).
- TailK l.318: `g.heckeVertWitness` -> `propTSAll_of_pieces3` (TailI l.77) -> `HeckeRestAll.coverModelOfHecke_of_heckeRest`
  -> `CoverModelOfHecke` (NoVerticalRam of the Hecke cover E/Q(X) at every p > 324) -> `PropTSAll` (Beckmann-type
  specialization) -> `FibreUnramified` -> `fibreCoverExists_of_propTSAll'` -> `modularConstituent`.
- So the true need is `HeckeRestNV.HeckeVertWitness` (TailG l.10216): for the Hecke cover E/Q(X) (any E carrying the
  normalization chart of the R1fp/R2fp curve), every p > 324 has an unramified vertical prime; equivalently (Galois,
  compiled `heckeNoVertRam_of_witness`) `HeckeNoVertRam`. A statement about function fields: no abelian scheme.
