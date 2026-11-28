import ZInQKernel.Contrib.OneProof.HeightModelM5.GlobalOmega
import ZInQKernel.Contrib.OneProof.HeightModelM5.DetLattice
import ZInQKernel.Contrib.OneProof.HeightModelM5.SheafRows

/-!
# Axiom check for the tree-facing statements

Prints the axioms of the theorems that identify the global sections of the sheaves built in this
directory with the tree's lattices. Each list is expected to lie within `propext`,
`Classical.choice` and `Quot.sound`.
-/

-- N4: global sections of `e*Ω¹`
#print axioms ZInQ.HeightModelM5.genericGermPullOmega
#print axioms ZInQ.HeightModelM5.genericGermPullOmega_apply
#print axioms ZInQ.HeightModelM5.stalkToGeneric_injective_sheaf
#print axioms ZInQ.HeightModelM5.genericGermPullOmega_injective
#print axioms ZInQ.HeightModelM5.range_genericGermPullOmega
#print axioms ZInQ.HeightModelM5.printedOmega_eq_sheaf

-- N5b: global sections of `ε*Ω^g`
#print axioms ZInQ.HeightModelM5.cotangent_isScalarTower
#print axioms ZInQ.HeightModelM5.GlobalPullOmegaTop
#print axioms ZInQ.HeightModelM5.toHodgeLine
#print axioms ZInQ.HeightModelM5.toHodgeLine_injective
#print axioms ZInQ.HeightModelM5.genericGermPullOmegaTop
#print axioms ZInQ.HeightModelM5.genericGermPullOmegaTop_apply
#print axioms ZInQ.HeightModelM5.genericGermPullOmegaTop_injective
#print axioms ZInQ.HeightModelM5.stalkTopMap
#print axioms ZInQ.HeightModelM5.stalkTopMap_smul
#print axioms ZInQ.HeightModelM5.stalkTopMap_add
#print axioms ZInQ.HeightModelM5.stalkTopMap_zero
#print axioms ZInQ.HeightModelM5.stalkTopMap_symm_ιMulti
#print axioms ZInQ.HeightModelM5.phi_mem_printedOmegaAt
#print axioms ZInQ.HeightModelM5.exists_phi_eq
#print axioms ZInQ.HeightModelM5.printedDetLattice_le_stalk
#print axioms ZInQ.HeightModelM5.exists_smul_mem_iInf_of_mem
#print axioms ZInQ.HeightModelM5.exists_smul_wedge_mem
#print axioms ZInQ.HeightModelM5.exists_smul_smul_mem
#print axioms ZInQ.HeightModelM5.exists_smul_stalkTopMap_mem
#print axioms ZInQ.HeightModelM5.range_genericGermPullOmegaTop_eq_iInter
#print axioms ZInQ.HeightModelM5.printedDetLattice_eq_sheaf

-- N6: the GR1 rows over the sheaf
#print axioms ZInQ.HeightModelM5.secIndex_genericGermPullOmegaTop
#print axioms ZInQ.HeightModelM5.IsGR1StableHeightSheaf
#print axioms ZInQ.HeightModelM5.isGR1StableHeightSheaf_iff
#print axioms ZInQ.HeightModelM5.GaudronRemondThm14GR1Sheaf
#print axioms ZInQ.HeightModelM5.gaudronRemondThm14GR1Sheaf_iff
#print axioms ZInQ.HeightModelM5.gaudronRemondThm14GR1_of_sheaf
#print axioms ZInQ.HeightModelM5.GaudronRemondSec9LowerGR1WeakSheaf
#print axioms ZInQ.HeightModelM5.gaudronRemondSec9LowerGR1WeakSheaf_iff
#print axioms ZInQ.HeightModelM5.gaudronRemondSec9LowerGR1Weak_of_sheaf
