# gt-ega results log

Target: `CToPrinted.EGAIV_8_10_5_openImm` (ZInQKernel/OneProof/H/TailZ19.lean L281; field
`HDec.HSyn.OpenResearchLeaves14.egaIV_8_10_5_openImm`).

## Library (VERIFIED by reading source)
- Mathlib `AlgebraicGeometry.exists_preimage_eq` (AffineTransitionLimit.lean L338, Stacks 01Z4(1)),
  `exists_map_preimage_le_map_preimage` (L269), `Scheme.compactSpace_of_isLimit` (L365).
- CloudW01 `exists_isIso_baseChange_of_isIso_limitBaseChange` (…/DescendingMorphisms/Isomorphism.lean L180, Stacks 081E),
  `baseChangeConeIsLimit`, `baseChangeMap`, `baseChangeCone_π_isPullback`, `baseChangeDiagramMap_isPullback`,
  `baseChangeMap_prop_iff` (BaseChange.lean); `locallyOfFinitePresentation_of_comp` (Morphisms/FinitePresentation/Basic.lean, Stacks 02FV).
- `#discharges` (scratch/gt-ega/Discharges.lean, VERIFIED): DISCHARGES [OpenResearchLeaves14.egaIV_8_10_5_openImm] by ZInQ.Contrib.EGAOpenImm.egaIV_8_10_5_openImm_proof; still assumes: []; axioms: [propext, Classical.choice, Quot.sound]; "72 open hypotheses, 2 theorems checked, 1 discharge one" (the second checked theorem is the general lemma exists_isOpenImmersion_baseChange).
